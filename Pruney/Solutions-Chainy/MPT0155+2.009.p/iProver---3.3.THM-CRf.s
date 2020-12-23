%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:58 EST 2020

% Result     : Theorem 34.96s
% Output     : CNFRefutation 34.96s
% Verified   : 
% Statistics : Number of formulae       :  112 (97683 expanded)
%              Number of clauses        :   79 (35007 expanded)
%              Number of leaves         :   12 (26051 expanded)
%              Depth                    :   37
%              Number of atoms          :  113 (97684 expanded)
%              Number of equality atoms :  112 (97683 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f25,f33,f30])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f23,f33,f34])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f27,f33,f34,f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f32,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X2)))),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f26,f33,f30,f34])).

fof(f42,plain,(
    k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f32,f34,f37])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_20,plain,
    ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35)))),k2_tarski(X0_35,X1_35)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X3_35,X4_35),k3_xboole_0(k2_tarski(X3_35,X4_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_95,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35)))),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X3_35,X4_35),k3_xboole_0(k2_tarski(X3_35,X4_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) ),
    inference(superposition,[status(thm)],[c_20,c_18])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_19,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)))) = k2_tarski(X0_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_88,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(superposition,[status(thm)],[c_21,c_19])).

cnf(c_136,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(superposition,[status(thm)],[c_88,c_19])).

cnf(c_153,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34),X2_34) ),
    inference(superposition,[status(thm)],[c_136,c_19])).

cnf(c_149,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),k5_xboole_0(X0_34,X1_34))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(superposition,[status(thm)],[c_19,c_136])).

cnf(c_154,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(demodulation,[status(thm)],[c_149,c_88])).

cnf(c_163,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
    inference(light_normalisation,[status(thm)],[c_153,c_154])).

cnf(c_164,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
    inference(demodulation,[status(thm)],[c_163,c_154])).

cnf(c_165,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
    inference(light_normalisation,[status(thm)],[c_164,c_19])).

cnf(c_287,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
    inference(superposition,[status(thm)],[c_19,c_165])).

cnf(c_307,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))),X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) ),
    inference(superposition,[status(thm)],[c_19,c_287])).

cnf(c_78,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_20,c_21])).

cnf(c_128,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(superposition,[status(thm)],[c_78,c_19])).

cnf(c_140,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(superposition,[status(thm)],[c_128,c_19])).

cnf(c_176,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
    inference(light_normalisation,[status(thm)],[c_140,c_140,c_154])).

cnf(c_177,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
    inference(demodulation,[status(thm)],[c_176,c_140,c_154])).

cnf(c_180,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
    inference(superposition,[status(thm)],[c_20,c_177])).

cnf(c_321,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34)),X3_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))),X3_34) ),
    inference(superposition,[status(thm)],[c_287,c_19])).

cnf(c_329,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34)) ),
    inference(demodulation,[status(thm)],[c_321,c_154,c_165])).

cnf(c_375,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) ),
    inference(demodulation,[status(thm)],[c_307,c_180,c_329])).

cnf(c_182,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34)),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
    inference(superposition,[status(thm)],[c_177,c_19])).

cnf(c_184,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
    inference(demodulation,[status(thm)],[c_182,c_154])).

cnf(c_185,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
    inference(light_normalisation,[status(thm)],[c_184,c_19])).

cnf(c_413,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34),k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
    inference(superposition,[status(thm)],[c_329,c_185])).

cnf(c_414,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
    inference(demodulation,[status(thm)],[c_413,c_185])).

cnf(c_493,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) ),
    inference(light_normalisation,[status(thm)],[c_375,c_375,c_414])).

cnf(c_494,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34)) ),
    inference(demodulation,[status(thm)],[c_493,c_329])).

cnf(c_97,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_21,c_18])).

cnf(c_3034,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X1_35)))) = k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_21,c_97])).

cnf(c_3168,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_3034,c_21])).

cnf(c_106,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)))),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_21,c_18])).

cnf(c_3233,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X1_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_20,c_3168])).

cnf(c_3306,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X1_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(superposition,[status(thm)],[c_3233,c_154])).

cnf(c_3322,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X1_35,X1_35)),X0_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(demodulation,[status(thm)],[c_3306,c_154])).

cnf(c_720,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))),X4_34) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) ),
    inference(superposition,[status(thm)],[c_494,c_154])).

cnf(c_409,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))),X4_34) ),
    inference(superposition,[status(thm)],[c_329,c_154])).

cnf(c_419,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))),X4_34) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) ),
    inference(light_normalisation,[status(thm)],[c_409,c_375])).

cnf(c_420,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),k5_xboole_0(X3_34,X4_34))) ),
    inference(demodulation,[status(thm)],[c_419,c_154,c_329])).

cnf(c_421,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),k5_xboole_0(X3_34,X4_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) ),
    inference(demodulation,[status(thm)],[c_420,c_329,c_375])).

cnf(c_496,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,k5_xboole_0(X3_34,X4_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),k5_xboole_0(X3_34,X4_34))) ),
    inference(superposition,[status(thm)],[c_19,c_493])).

cnf(c_570,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,k5_xboole_0(X3_34,X4_34))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),k5_xboole_0(X3_34,X4_34)))) ),
    inference(demodulation,[status(thm)],[c_496,c_493])).

cnf(c_732,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,k5_xboole_0(X3_34,X4_34))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))),X4_34) ),
    inference(light_normalisation,[status(thm)],[c_720,c_421,c_570])).

cnf(c_3867,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X3_35,X3_35)),k5_xboole_0(X0_34,X1_34))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),X0_34)),X1_34) ),
    inference(superposition,[status(thm)],[c_3322,c_732])).

cnf(c_3875,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),X0_34)),X1_34) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(X0_34,X1_34))) ),
    inference(demodulation,[status(thm)],[c_3867,c_3322])).

cnf(c_5061,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(demodulation,[status(thm)],[c_106,c_3875])).

cnf(c_5077,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X1_35,X2_35)),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_3168,c_5061])).

cnf(c_3251,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(superposition,[status(thm)],[c_3168,c_154])).

cnf(c_3268,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X1_35)),X0_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(demodulation,[status(thm)],[c_3251,c_154])).

cnf(c_5142,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
    inference(demodulation,[status(thm)],[c_5077,c_3268])).

cnf(c_22667,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_20,c_5142])).

cnf(c_37005,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_22667,c_5142])).

cnf(c_60710,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)),X0_34))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),X0_34) ),
    inference(superposition,[status(thm)],[c_37005,c_3875])).

cnf(c_76102,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X4_35,X4_35)),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35))))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X3_35,X4_35),k3_xboole_0(k2_tarski(X3_35,X4_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) ),
    inference(demodulation,[status(thm)],[c_95,c_494,c_60710])).

cnf(c_76409,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X3_35,X3_35)),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X2_35,X2_35))))))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_76102,c_97])).

cnf(c_137,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(superposition,[status(thm)],[c_19,c_128])).

cnf(c_76621,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X2_35,X2_35))))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(demodulation,[status(thm)],[c_76409,c_137])).

cnf(c_76622,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X3_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(demodulation,[status(thm)],[c_76621,c_21])).

cnf(c_5,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k2_tarski(sK0,sK0)))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k2_tarski(sK0,sK0)))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_34,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))) ),
    inference(demodulation,[status(thm)],[c_20,c_16])).

cnf(c_37,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k2_tarski(sK0,sK0))))) != k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))) ),
    inference(demodulation,[status(thm)],[c_19,c_34])).

cnf(c_39,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))) ),
    inference(superposition,[status(thm)],[c_19,c_37])).

cnf(c_36928,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_22667,c_39])).

cnf(c_76874,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_76622,c_36928])).

cnf(c_3121,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_20,c_3034])).

cnf(c_4911,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_3121,c_3034])).

cnf(c_37006,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_22667,c_4911])).

cnf(c_5079,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X3_35,X3_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X3_35,X3_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_20,c_5061])).

cnf(c_63396,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X3_35,X3_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X2_35,X3_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_37006,c_5079])).

cnf(c_76875,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_76874,c_63396])).

cnf(c_77531,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_76622,c_76875])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 34.96/5.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.96/5.01  
% 34.96/5.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 34.96/5.01  
% 34.96/5.01  ------  iProver source info
% 34.96/5.01  
% 34.96/5.01  git: date: 2020-06-30 10:37:57 +0100
% 34.96/5.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 34.96/5.01  git: non_committed_changes: false
% 34.96/5.01  git: last_make_outside_of_git: false
% 34.96/5.01  
% 34.96/5.01  ------ 
% 34.96/5.01  
% 34.96/5.01  ------ Input Options
% 34.96/5.01  
% 34.96/5.01  --out_options                           all
% 34.96/5.01  --tptp_safe_out                         true
% 34.96/5.01  --problem_path                          ""
% 34.96/5.01  --include_path                          ""
% 34.96/5.01  --clausifier                            res/vclausify_rel
% 34.96/5.01  --clausifier_options                    --mode clausify
% 34.96/5.01  --stdin                                 false
% 34.96/5.01  --stats_out                             all
% 34.96/5.01  
% 34.96/5.01  ------ General Options
% 34.96/5.01  
% 34.96/5.01  --fof                                   false
% 34.96/5.01  --time_out_real                         305.
% 34.96/5.01  --time_out_virtual                      -1.
% 34.96/5.01  --symbol_type_check                     false
% 34.96/5.01  --clausify_out                          false
% 34.96/5.01  --sig_cnt_out                           false
% 34.96/5.01  --trig_cnt_out                          false
% 34.96/5.01  --trig_cnt_out_tolerance                1.
% 34.96/5.01  --trig_cnt_out_sk_spl                   false
% 34.96/5.01  --abstr_cl_out                          false
% 34.96/5.01  
% 34.96/5.01  ------ Global Options
% 34.96/5.01  
% 34.96/5.01  --schedule                              default
% 34.96/5.01  --add_important_lit                     false
% 34.96/5.01  --prop_solver_per_cl                    1000
% 34.96/5.01  --min_unsat_core                        false
% 34.96/5.01  --soft_assumptions                      false
% 34.96/5.01  --soft_lemma_size                       3
% 34.96/5.01  --prop_impl_unit_size                   0
% 34.96/5.01  --prop_impl_unit                        []
% 34.96/5.01  --share_sel_clauses                     true
% 34.96/5.01  --reset_solvers                         false
% 34.96/5.01  --bc_imp_inh                            [conj_cone]
% 34.96/5.01  --conj_cone_tolerance                   3.
% 34.96/5.01  --extra_neg_conj                        none
% 34.96/5.01  --large_theory_mode                     true
% 34.96/5.01  --prolific_symb_bound                   200
% 34.96/5.01  --lt_threshold                          2000
% 34.96/5.01  --clause_weak_htbl                      true
% 34.96/5.01  --gc_record_bc_elim                     false
% 34.96/5.01  
% 34.96/5.01  ------ Preprocessing Options
% 34.96/5.01  
% 34.96/5.01  --preprocessing_flag                    true
% 34.96/5.01  --time_out_prep_mult                    0.1
% 34.96/5.01  --splitting_mode                        input
% 34.96/5.01  --splitting_grd                         true
% 34.96/5.01  --splitting_cvd                         false
% 34.96/5.01  --splitting_cvd_svl                     false
% 34.96/5.01  --splitting_nvd                         32
% 34.96/5.01  --sub_typing                            true
% 34.96/5.01  --prep_gs_sim                           true
% 34.96/5.01  --prep_unflatten                        true
% 34.96/5.01  --prep_res_sim                          true
% 34.96/5.01  --prep_upred                            true
% 34.96/5.01  --prep_sem_filter                       exhaustive
% 34.96/5.01  --prep_sem_filter_out                   false
% 34.96/5.01  --pred_elim                             true
% 34.96/5.01  --res_sim_input                         true
% 34.96/5.01  --eq_ax_congr_red                       true
% 34.96/5.01  --pure_diseq_elim                       true
% 34.96/5.01  --brand_transform                       false
% 34.96/5.01  --non_eq_to_eq                          false
% 34.96/5.01  --prep_def_merge                        true
% 34.96/5.01  --prep_def_merge_prop_impl              false
% 34.96/5.01  --prep_def_merge_mbd                    true
% 34.96/5.01  --prep_def_merge_tr_red                 false
% 34.96/5.01  --prep_def_merge_tr_cl                  false
% 34.96/5.01  --smt_preprocessing                     true
% 34.96/5.01  --smt_ac_axioms                         fast
% 34.96/5.01  --preprocessed_out                      false
% 34.96/5.01  --preprocessed_stats                    false
% 34.96/5.01  
% 34.96/5.01  ------ Abstraction refinement Options
% 34.96/5.01  
% 34.96/5.01  --abstr_ref                             []
% 34.96/5.01  --abstr_ref_prep                        false
% 34.96/5.01  --abstr_ref_until_sat                   false
% 34.96/5.01  --abstr_ref_sig_restrict                funpre
% 34.96/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 34.96/5.01  --abstr_ref_under                       []
% 34.96/5.01  
% 34.96/5.01  ------ SAT Options
% 34.96/5.01  
% 34.96/5.01  --sat_mode                              false
% 34.96/5.01  --sat_fm_restart_options                ""
% 34.96/5.01  --sat_gr_def                            false
% 34.96/5.01  --sat_epr_types                         true
% 34.96/5.01  --sat_non_cyclic_types                  false
% 34.96/5.01  --sat_finite_models                     false
% 34.96/5.01  --sat_fm_lemmas                         false
% 34.96/5.01  --sat_fm_prep                           false
% 34.96/5.01  --sat_fm_uc_incr                        true
% 34.96/5.01  --sat_out_model                         small
% 34.96/5.01  --sat_out_clauses                       false
% 34.96/5.01  
% 34.96/5.01  ------ QBF Options
% 34.96/5.01  
% 34.96/5.01  --qbf_mode                              false
% 34.96/5.01  --qbf_elim_univ                         false
% 34.96/5.01  --qbf_dom_inst                          none
% 34.96/5.01  --qbf_dom_pre_inst                      false
% 34.96/5.01  --qbf_sk_in                             false
% 34.96/5.01  --qbf_pred_elim                         true
% 34.96/5.01  --qbf_split                             512
% 34.96/5.01  
% 34.96/5.01  ------ BMC1 Options
% 34.96/5.01  
% 34.96/5.01  --bmc1_incremental                      false
% 34.96/5.01  --bmc1_axioms                           reachable_all
% 34.96/5.01  --bmc1_min_bound                        0
% 34.96/5.01  --bmc1_max_bound                        -1
% 34.96/5.01  --bmc1_max_bound_default                -1
% 34.96/5.01  --bmc1_symbol_reachability              true
% 34.96/5.01  --bmc1_property_lemmas                  false
% 34.96/5.01  --bmc1_k_induction                      false
% 34.96/5.01  --bmc1_non_equiv_states                 false
% 34.96/5.01  --bmc1_deadlock                         false
% 34.96/5.01  --bmc1_ucm                              false
% 34.96/5.01  --bmc1_add_unsat_core                   none
% 34.96/5.01  --bmc1_unsat_core_children              false
% 34.96/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 34.96/5.01  --bmc1_out_stat                         full
% 34.96/5.01  --bmc1_ground_init                      false
% 34.96/5.01  --bmc1_pre_inst_next_state              false
% 34.96/5.01  --bmc1_pre_inst_state                   false
% 34.96/5.01  --bmc1_pre_inst_reach_state             false
% 34.96/5.01  --bmc1_out_unsat_core                   false
% 34.96/5.01  --bmc1_aig_witness_out                  false
% 34.96/5.01  --bmc1_verbose                          false
% 34.96/5.01  --bmc1_dump_clauses_tptp                false
% 34.96/5.01  --bmc1_dump_unsat_core_tptp             false
% 34.96/5.01  --bmc1_dump_file                        -
% 34.96/5.01  --bmc1_ucm_expand_uc_limit              128
% 34.96/5.01  --bmc1_ucm_n_expand_iterations          6
% 34.96/5.01  --bmc1_ucm_extend_mode                  1
% 34.96/5.01  --bmc1_ucm_init_mode                    2
% 34.96/5.01  --bmc1_ucm_cone_mode                    none
% 34.96/5.01  --bmc1_ucm_reduced_relation_type        0
% 34.96/5.01  --bmc1_ucm_relax_model                  4
% 34.96/5.01  --bmc1_ucm_full_tr_after_sat            true
% 34.96/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 34.96/5.01  --bmc1_ucm_layered_model                none
% 34.96/5.01  --bmc1_ucm_max_lemma_size               10
% 34.96/5.01  
% 34.96/5.01  ------ AIG Options
% 34.96/5.01  
% 34.96/5.01  --aig_mode                              false
% 34.96/5.01  
% 34.96/5.01  ------ Instantiation Options
% 34.96/5.01  
% 34.96/5.01  --instantiation_flag                    true
% 34.96/5.01  --inst_sos_flag                         false
% 34.96/5.01  --inst_sos_phase                        true
% 34.96/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.96/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.96/5.01  --inst_lit_sel_side                     num_symb
% 34.96/5.01  --inst_solver_per_active                1400
% 34.96/5.01  --inst_solver_calls_frac                1.
% 34.96/5.01  --inst_passive_queue_type               priority_queues
% 34.96/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.96/5.01  --inst_passive_queues_freq              [25;2]
% 34.96/5.01  --inst_dismatching                      true
% 34.96/5.01  --inst_eager_unprocessed_to_passive     true
% 34.96/5.01  --inst_prop_sim_given                   true
% 34.96/5.01  --inst_prop_sim_new                     false
% 34.96/5.01  --inst_subs_new                         false
% 34.96/5.01  --inst_eq_res_simp                      false
% 34.96/5.01  --inst_subs_given                       false
% 34.96/5.01  --inst_orphan_elimination               true
% 34.96/5.01  --inst_learning_loop_flag               true
% 34.96/5.01  --inst_learning_start                   3000
% 34.96/5.01  --inst_learning_factor                  2
% 34.96/5.01  --inst_start_prop_sim_after_learn       3
% 34.96/5.01  --inst_sel_renew                        solver
% 34.96/5.01  --inst_lit_activity_flag                true
% 34.96/5.01  --inst_restr_to_given                   false
% 34.96/5.01  --inst_activity_threshold               500
% 34.96/5.01  --inst_out_proof                        true
% 34.96/5.01  
% 34.96/5.01  ------ Resolution Options
% 34.96/5.01  
% 34.96/5.01  --resolution_flag                       true
% 34.96/5.01  --res_lit_sel                           adaptive
% 34.96/5.01  --res_lit_sel_side                      none
% 34.96/5.01  --res_ordering                          kbo
% 34.96/5.01  --res_to_prop_solver                    active
% 34.96/5.01  --res_prop_simpl_new                    false
% 34.96/5.01  --res_prop_simpl_given                  true
% 34.96/5.01  --res_passive_queue_type                priority_queues
% 34.96/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.96/5.01  --res_passive_queues_freq               [15;5]
% 34.96/5.01  --res_forward_subs                      full
% 34.96/5.01  --res_backward_subs                     full
% 34.96/5.01  --res_forward_subs_resolution           true
% 34.96/5.01  --res_backward_subs_resolution          true
% 34.96/5.01  --res_orphan_elimination                true
% 34.96/5.01  --res_time_limit                        2.
% 34.96/5.01  --res_out_proof                         true
% 34.96/5.01  
% 34.96/5.01  ------ Superposition Options
% 34.96/5.01  
% 34.96/5.01  --superposition_flag                    true
% 34.96/5.01  --sup_passive_queue_type                priority_queues
% 34.96/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.96/5.01  --sup_passive_queues_freq               [8;1;4]
% 34.96/5.01  --demod_completeness_check              fast
% 34.96/5.01  --demod_use_ground                      true
% 34.96/5.01  --sup_to_prop_solver                    passive
% 34.96/5.01  --sup_prop_simpl_new                    true
% 34.96/5.01  --sup_prop_simpl_given                  true
% 34.96/5.01  --sup_fun_splitting                     false
% 34.96/5.01  --sup_smt_interval                      50000
% 34.96/5.02  
% 34.96/5.02  ------ Superposition Simplification Setup
% 34.96/5.02  
% 34.96/5.02  --sup_indices_passive                   []
% 34.96/5.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 34.96/5.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 34.96/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 34.96/5.02  --sup_full_triv                         [TrivRules;PropSubs]
% 34.96/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 34.96/5.02  --sup_full_bw                           [BwDemod]
% 34.96/5.02  --sup_immed_triv                        [TrivRules]
% 34.96/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.96/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 34.96/5.02  --sup_immed_bw_main                     []
% 34.96/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 34.96/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 34.96/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 34.96/5.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 34.96/5.02  
% 34.96/5.02  ------ Combination Options
% 34.96/5.02  
% 34.96/5.02  --comb_res_mult                         3
% 34.96/5.02  --comb_sup_mult                         2
% 34.96/5.02  --comb_inst_mult                        10
% 34.96/5.02  
% 34.96/5.02  ------ Debug Options
% 34.96/5.02  
% 34.96/5.02  --dbg_backtrace                         false
% 34.96/5.02  --dbg_dump_prop_clauses                 false
% 34.96/5.02  --dbg_dump_prop_clauses_file            -
% 34.96/5.02  --dbg_out_stat                          false
% 34.96/5.02  ------ Parsing...
% 34.96/5.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 34.96/5.02  
% 34.96/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 34.96/5.02  
% 34.96/5.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 34.96/5.02  
% 34.96/5.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 34.96/5.02  ------ Proving...
% 34.96/5.02  ------ Problem Properties 
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  clauses                                 6
% 34.96/5.02  conjectures                             1
% 34.96/5.02  EPR                                     0
% 34.96/5.02  Horn                                    6
% 34.96/5.02  unary                                   6
% 34.96/5.02  binary                                  0
% 34.96/5.02  lits                                    6
% 34.96/5.02  lits eq                                 6
% 34.96/5.02  fd_pure                                 0
% 34.96/5.02  fd_pseudo                               0
% 34.96/5.02  fd_cond                                 0
% 34.96/5.02  fd_pseudo_cond                          0
% 34.96/5.02  AC symbols                              0
% 34.96/5.02  
% 34.96/5.02  ------ Schedule UEQ
% 34.96/5.02  
% 34.96/5.02  ------ pure equality problem: resolution off 
% 34.96/5.02  
% 34.96/5.02  ------ Option_UEQ Time Limit: Unbounded
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  ------ 
% 34.96/5.02  Current options:
% 34.96/5.02  ------ 
% 34.96/5.02  
% 34.96/5.02  ------ Input Options
% 34.96/5.02  
% 34.96/5.02  --out_options                           all
% 34.96/5.02  --tptp_safe_out                         true
% 34.96/5.02  --problem_path                          ""
% 34.96/5.02  --include_path                          ""
% 34.96/5.02  --clausifier                            res/vclausify_rel
% 34.96/5.02  --clausifier_options                    --mode clausify
% 34.96/5.02  --stdin                                 false
% 34.96/5.02  --stats_out                             all
% 34.96/5.02  
% 34.96/5.02  ------ General Options
% 34.96/5.02  
% 34.96/5.02  --fof                                   false
% 34.96/5.02  --time_out_real                         305.
% 34.96/5.02  --time_out_virtual                      -1.
% 34.96/5.02  --symbol_type_check                     false
% 34.96/5.02  --clausify_out                          false
% 34.96/5.02  --sig_cnt_out                           false
% 34.96/5.02  --trig_cnt_out                          false
% 34.96/5.02  --trig_cnt_out_tolerance                1.
% 34.96/5.02  --trig_cnt_out_sk_spl                   false
% 34.96/5.02  --abstr_cl_out                          false
% 34.96/5.02  
% 34.96/5.02  ------ Global Options
% 34.96/5.02  
% 34.96/5.02  --schedule                              default
% 34.96/5.02  --add_important_lit                     false
% 34.96/5.02  --prop_solver_per_cl                    1000
% 34.96/5.02  --min_unsat_core                        false
% 34.96/5.02  --soft_assumptions                      false
% 34.96/5.02  --soft_lemma_size                       3
% 34.96/5.02  --prop_impl_unit_size                   0
% 34.96/5.02  --prop_impl_unit                        []
% 34.96/5.02  --share_sel_clauses                     true
% 34.96/5.02  --reset_solvers                         false
% 34.96/5.02  --bc_imp_inh                            [conj_cone]
% 34.96/5.02  --conj_cone_tolerance                   3.
% 34.96/5.02  --extra_neg_conj                        none
% 34.96/5.02  --large_theory_mode                     true
% 34.96/5.02  --prolific_symb_bound                   200
% 34.96/5.02  --lt_threshold                          2000
% 34.96/5.02  --clause_weak_htbl                      true
% 34.96/5.02  --gc_record_bc_elim                     false
% 34.96/5.02  
% 34.96/5.02  ------ Preprocessing Options
% 34.96/5.02  
% 34.96/5.02  --preprocessing_flag                    true
% 34.96/5.02  --time_out_prep_mult                    0.1
% 34.96/5.02  --splitting_mode                        input
% 34.96/5.02  --splitting_grd                         true
% 34.96/5.02  --splitting_cvd                         false
% 34.96/5.02  --splitting_cvd_svl                     false
% 34.96/5.02  --splitting_nvd                         32
% 34.96/5.02  --sub_typing                            true
% 34.96/5.02  --prep_gs_sim                           true
% 34.96/5.02  --prep_unflatten                        true
% 34.96/5.02  --prep_res_sim                          true
% 34.96/5.02  --prep_upred                            true
% 34.96/5.02  --prep_sem_filter                       exhaustive
% 34.96/5.02  --prep_sem_filter_out                   false
% 34.96/5.02  --pred_elim                             true
% 34.96/5.02  --res_sim_input                         true
% 34.96/5.02  --eq_ax_congr_red                       true
% 34.96/5.02  --pure_diseq_elim                       true
% 34.96/5.02  --brand_transform                       false
% 34.96/5.02  --non_eq_to_eq                          false
% 34.96/5.02  --prep_def_merge                        true
% 34.96/5.02  --prep_def_merge_prop_impl              false
% 34.96/5.02  --prep_def_merge_mbd                    true
% 34.96/5.02  --prep_def_merge_tr_red                 false
% 34.96/5.02  --prep_def_merge_tr_cl                  false
% 34.96/5.02  --smt_preprocessing                     true
% 34.96/5.02  --smt_ac_axioms                         fast
% 34.96/5.02  --preprocessed_out                      false
% 34.96/5.02  --preprocessed_stats                    false
% 34.96/5.02  
% 34.96/5.02  ------ Abstraction refinement Options
% 34.96/5.02  
% 34.96/5.02  --abstr_ref                             []
% 34.96/5.02  --abstr_ref_prep                        false
% 34.96/5.02  --abstr_ref_until_sat                   false
% 34.96/5.02  --abstr_ref_sig_restrict                funpre
% 34.96/5.02  --abstr_ref_af_restrict_to_split_sk     false
% 34.96/5.02  --abstr_ref_under                       []
% 34.96/5.02  
% 34.96/5.02  ------ SAT Options
% 34.96/5.02  
% 34.96/5.02  --sat_mode                              false
% 34.96/5.02  --sat_fm_restart_options                ""
% 34.96/5.02  --sat_gr_def                            false
% 34.96/5.02  --sat_epr_types                         true
% 34.96/5.02  --sat_non_cyclic_types                  false
% 34.96/5.02  --sat_finite_models                     false
% 34.96/5.02  --sat_fm_lemmas                         false
% 34.96/5.02  --sat_fm_prep                           false
% 34.96/5.02  --sat_fm_uc_incr                        true
% 34.96/5.02  --sat_out_model                         small
% 34.96/5.02  --sat_out_clauses                       false
% 34.96/5.02  
% 34.96/5.02  ------ QBF Options
% 34.96/5.02  
% 34.96/5.02  --qbf_mode                              false
% 34.96/5.02  --qbf_elim_univ                         false
% 34.96/5.02  --qbf_dom_inst                          none
% 34.96/5.02  --qbf_dom_pre_inst                      false
% 34.96/5.02  --qbf_sk_in                             false
% 34.96/5.02  --qbf_pred_elim                         true
% 34.96/5.02  --qbf_split                             512
% 34.96/5.02  
% 34.96/5.02  ------ BMC1 Options
% 34.96/5.02  
% 34.96/5.02  --bmc1_incremental                      false
% 34.96/5.02  --bmc1_axioms                           reachable_all
% 34.96/5.02  --bmc1_min_bound                        0
% 34.96/5.02  --bmc1_max_bound                        -1
% 34.96/5.02  --bmc1_max_bound_default                -1
% 34.96/5.02  --bmc1_symbol_reachability              true
% 34.96/5.02  --bmc1_property_lemmas                  false
% 34.96/5.02  --bmc1_k_induction                      false
% 34.96/5.02  --bmc1_non_equiv_states                 false
% 34.96/5.02  --bmc1_deadlock                         false
% 34.96/5.02  --bmc1_ucm                              false
% 34.96/5.02  --bmc1_add_unsat_core                   none
% 34.96/5.02  --bmc1_unsat_core_children              false
% 34.96/5.02  --bmc1_unsat_core_extrapolate_axioms    false
% 34.96/5.02  --bmc1_out_stat                         full
% 34.96/5.02  --bmc1_ground_init                      false
% 34.96/5.02  --bmc1_pre_inst_next_state              false
% 34.96/5.02  --bmc1_pre_inst_state                   false
% 34.96/5.02  --bmc1_pre_inst_reach_state             false
% 34.96/5.02  --bmc1_out_unsat_core                   false
% 34.96/5.02  --bmc1_aig_witness_out                  false
% 34.96/5.02  --bmc1_verbose                          false
% 34.96/5.02  --bmc1_dump_clauses_tptp                false
% 34.96/5.02  --bmc1_dump_unsat_core_tptp             false
% 34.96/5.02  --bmc1_dump_file                        -
% 34.96/5.02  --bmc1_ucm_expand_uc_limit              128
% 34.96/5.02  --bmc1_ucm_n_expand_iterations          6
% 34.96/5.02  --bmc1_ucm_extend_mode                  1
% 34.96/5.02  --bmc1_ucm_init_mode                    2
% 34.96/5.02  --bmc1_ucm_cone_mode                    none
% 34.96/5.02  --bmc1_ucm_reduced_relation_type        0
% 34.96/5.02  --bmc1_ucm_relax_model                  4
% 34.96/5.02  --bmc1_ucm_full_tr_after_sat            true
% 34.96/5.02  --bmc1_ucm_expand_neg_assumptions       false
% 34.96/5.02  --bmc1_ucm_layered_model                none
% 34.96/5.02  --bmc1_ucm_max_lemma_size               10
% 34.96/5.02  
% 34.96/5.02  ------ AIG Options
% 34.96/5.02  
% 34.96/5.02  --aig_mode                              false
% 34.96/5.02  
% 34.96/5.02  ------ Instantiation Options
% 34.96/5.02  
% 34.96/5.02  --instantiation_flag                    false
% 34.96/5.02  --inst_sos_flag                         false
% 34.96/5.02  --inst_sos_phase                        true
% 34.96/5.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.96/5.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.96/5.02  --inst_lit_sel_side                     num_symb
% 34.96/5.02  --inst_solver_per_active                1400
% 34.96/5.02  --inst_solver_calls_frac                1.
% 34.96/5.02  --inst_passive_queue_type               priority_queues
% 34.96/5.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.96/5.02  --inst_passive_queues_freq              [25;2]
% 34.96/5.02  --inst_dismatching                      true
% 34.96/5.02  --inst_eager_unprocessed_to_passive     true
% 34.96/5.02  --inst_prop_sim_given                   true
% 34.96/5.02  --inst_prop_sim_new                     false
% 34.96/5.02  --inst_subs_new                         false
% 34.96/5.02  --inst_eq_res_simp                      false
% 34.96/5.02  --inst_subs_given                       false
% 34.96/5.02  --inst_orphan_elimination               true
% 34.96/5.02  --inst_learning_loop_flag               true
% 34.96/5.02  --inst_learning_start                   3000
% 34.96/5.02  --inst_learning_factor                  2
% 34.96/5.02  --inst_start_prop_sim_after_learn       3
% 34.96/5.02  --inst_sel_renew                        solver
% 34.96/5.02  --inst_lit_activity_flag                true
% 34.96/5.02  --inst_restr_to_given                   false
% 34.96/5.02  --inst_activity_threshold               500
% 34.96/5.02  --inst_out_proof                        true
% 34.96/5.02  
% 34.96/5.02  ------ Resolution Options
% 34.96/5.02  
% 34.96/5.02  --resolution_flag                       false
% 34.96/5.02  --res_lit_sel                           adaptive
% 34.96/5.02  --res_lit_sel_side                      none
% 34.96/5.02  --res_ordering                          kbo
% 34.96/5.02  --res_to_prop_solver                    active
% 34.96/5.02  --res_prop_simpl_new                    false
% 34.96/5.02  --res_prop_simpl_given                  true
% 34.96/5.02  --res_passive_queue_type                priority_queues
% 34.96/5.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.96/5.02  --res_passive_queues_freq               [15;5]
% 34.96/5.02  --res_forward_subs                      full
% 34.96/5.02  --res_backward_subs                     full
% 34.96/5.02  --res_forward_subs_resolution           true
% 34.96/5.02  --res_backward_subs_resolution          true
% 34.96/5.02  --res_orphan_elimination                true
% 34.96/5.02  --res_time_limit                        2.
% 34.96/5.02  --res_out_proof                         true
% 34.96/5.02  
% 34.96/5.02  ------ Superposition Options
% 34.96/5.02  
% 34.96/5.02  --superposition_flag                    true
% 34.96/5.02  --sup_passive_queue_type                priority_queues
% 34.96/5.02  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.96/5.02  --sup_passive_queues_freq               [8;1;4]
% 34.96/5.02  --demod_completeness_check              fast
% 34.96/5.02  --demod_use_ground                      true
% 34.96/5.02  --sup_to_prop_solver                    active
% 34.96/5.02  --sup_prop_simpl_new                    false
% 34.96/5.02  --sup_prop_simpl_given                  false
% 34.96/5.02  --sup_fun_splitting                     true
% 34.96/5.02  --sup_smt_interval                      10000
% 34.96/5.02  
% 34.96/5.02  ------ Superposition Simplification Setup
% 34.96/5.02  
% 34.96/5.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 34.96/5.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 34.96/5.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 34.96/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 34.96/5.02  --sup_full_triv                         [TrivRules]
% 34.96/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 34.96/5.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 34.96/5.02  --sup_immed_triv                        [TrivRules]
% 34.96/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.96/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.96/5.02  --sup_immed_bw_main                     []
% 34.96/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 34.96/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 34.96/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.96/5.02  --sup_input_bw                          [BwDemod;BwSubsumption]
% 34.96/5.02  
% 34.96/5.02  ------ Combination Options
% 34.96/5.02  
% 34.96/5.02  --comb_res_mult                         1
% 34.96/5.02  --comb_sup_mult                         1
% 34.96/5.02  --comb_inst_mult                        1000000
% 34.96/5.02  
% 34.96/5.02  ------ Debug Options
% 34.96/5.02  
% 34.96/5.02  --dbg_backtrace                         false
% 34.96/5.02  --dbg_dump_prop_clauses                 false
% 34.96/5.02  --dbg_dump_prop_clauses_file            -
% 34.96/5.02  --dbg_out_stat                          false
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  ------ Proving...
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  % SZS status Theorem for theBenchmark.p
% 34.96/5.02  
% 34.96/5.02   Resolution empty clause
% 34.96/5.02  
% 34.96/5.02  % SZS output start CNFRefutation for theBenchmark.p
% 34.96/5.02  
% 34.96/5.02  fof(f1,axiom,(
% 34.96/5.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f19,plain,(
% 34.96/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f1])).
% 34.96/5.02  
% 34.96/5.02  fof(f9,axiom,(
% 34.96/5.02    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f27,plain,(
% 34.96/5.02    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f9])).
% 34.96/5.02  
% 34.96/5.02  fof(f5,axiom,(
% 34.96/5.02    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f23,plain,(
% 34.96/5.02    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f5])).
% 34.96/5.02  
% 34.96/5.02  fof(f7,axiom,(
% 34.96/5.02    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f25,plain,(
% 34.96/5.02    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f7])).
% 34.96/5.02  
% 34.96/5.02  fof(f4,axiom,(
% 34.96/5.02    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f22,plain,(
% 34.96/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f4])).
% 34.96/5.02  
% 34.96/5.02  fof(f2,axiom,(
% 34.96/5.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f20,plain,(
% 34.96/5.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 34.96/5.02    inference(cnf_transformation,[],[f2])).
% 34.96/5.02  
% 34.96/5.02  fof(f33,plain,(
% 34.96/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 34.96/5.02    inference(definition_unfolding,[],[f22,f20])).
% 34.96/5.02  
% 34.96/5.02  fof(f12,axiom,(
% 34.96/5.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f30,plain,(
% 34.96/5.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f12])).
% 34.96/5.02  
% 34.96/5.02  fof(f34,plain,(
% 34.96/5.02    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) = k1_enumset1(X0,X1,X2)) )),
% 34.96/5.02    inference(definition_unfolding,[],[f25,f33,f30])).
% 34.96/5.02  
% 34.96/5.02  fof(f35,plain,(
% 34.96/5.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 34.96/5.02    inference(definition_unfolding,[],[f23,f33,f34])).
% 34.96/5.02  
% 34.96/5.02  fof(f40,plain,(
% 34.96/5.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k2_tarski(X0,X1))))) )),
% 34.96/5.02    inference(definition_unfolding,[],[f27,f33,f34,f35])).
% 34.96/5.02  
% 34.96/5.02  fof(f3,axiom,(
% 34.96/5.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f21,plain,(
% 34.96/5.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f3])).
% 34.96/5.02  
% 34.96/5.02  fof(f13,axiom,(
% 34.96/5.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f31,plain,(
% 34.96/5.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f13])).
% 34.96/5.02  
% 34.96/5.02  fof(f39,plain,(
% 34.96/5.02    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 34.96/5.02    inference(definition_unfolding,[],[f31,f34])).
% 34.96/5.02  
% 34.96/5.02  fof(f14,conjecture,(
% 34.96/5.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f15,negated_conjecture,(
% 34.96/5.02    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 34.96/5.02    inference(negated_conjecture,[],[f14])).
% 34.96/5.02  
% 34.96/5.02  fof(f16,plain,(
% 34.96/5.02    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 34.96/5.02    inference(ennf_transformation,[],[f15])).
% 34.96/5.02  
% 34.96/5.02  fof(f17,plain,(
% 34.96/5.02    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 34.96/5.02    introduced(choice_axiom,[])).
% 34.96/5.02  
% 34.96/5.02  fof(f18,plain,(
% 34.96/5.02    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 34.96/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 34.96/5.02  
% 34.96/5.02  fof(f32,plain,(
% 34.96/5.02    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 34.96/5.02    inference(cnf_transformation,[],[f18])).
% 34.96/5.02  
% 34.96/5.02  fof(f8,axiom,(
% 34.96/5.02    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 34.96/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.96/5.02  
% 34.96/5.02  fof(f26,plain,(
% 34.96/5.02    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 34.96/5.02    inference(cnf_transformation,[],[f8])).
% 34.96/5.02  
% 34.96/5.02  fof(f37,plain,(
% 34.96/5.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X2)))),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 34.96/5.02    inference(definition_unfolding,[],[f26,f33,f30,f34])).
% 34.96/5.02  
% 34.96/5.02  fof(f42,plain,(
% 34.96/5.02    k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k2_tarski(sK0,sK0))))),
% 34.96/5.02    inference(definition_unfolding,[],[f32,f34,f37])).
% 34.96/5.02  
% 34.96/5.02  cnf(c_1,plain,
% 34.96/5.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 34.96/5.02      inference(cnf_transformation,[],[f19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_20,plain,
% 34.96/5.02      ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
% 34.96/5.02      inference(subtyping,[status(esa)],[c_1]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3)))),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))))) ),
% 34.96/5.02      inference(cnf_transformation,[],[f40]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_18,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35)))),k2_tarski(X0_35,X1_35)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X3_35,X4_35),k3_xboole_0(k2_tarski(X3_35,X4_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) ),
% 34.96/5.02      inference(subtyping,[status(esa)],[c_3]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_95,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35)))),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X3_35,X4_35),k3_xboole_0(k2_tarski(X3_35,X4_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_20,c_18]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_2,plain,
% 34.96/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 34.96/5.02      inference(cnf_transformation,[],[f21]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_19,plain,
% 34.96/5.02      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
% 34.96/5.02      inference(subtyping,[status(esa)],[c_2]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_0,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 34.96/5.02      inference(cnf_transformation,[],[f39]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_21,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)))) = k2_tarski(X0_35,X1_35) ),
% 34.96/5.02      inference(subtyping,[status(esa)],[c_0]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_88,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_21,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_136,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_88,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_153,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34),X2_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_136,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_149,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),k5_xboole_0(X0_34,X1_34))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_19,c_136]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_154,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_149,c_88]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_163,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
% 34.96/5.02      inference(light_normalisation,[status(thm)],[c_153,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_164,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_163,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_165,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
% 34.96/5.02      inference(light_normalisation,[status(thm)],[c_164,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_287,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_19,c_165]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_307,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))),X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_19,c_287]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_78,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_20,c_21]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_128,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_78,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_140,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_128,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_176,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
% 34.96/5.02      inference(light_normalisation,[status(thm)],[c_140,c_140,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_177,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_176,c_140,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_180,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_20,c_177]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_321,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34)),X3_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))),X3_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_287,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_329,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34)) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_321,c_154,c_165]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_375,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_307,c_180,c_329]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_182,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34)),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_177,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_184,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_182,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_185,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
% 34.96/5.02      inference(light_normalisation,[status(thm)],[c_184,c_19]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_413,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34),X1_34),k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_329,c_185]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_414,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_413,c_185]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_493,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) ),
% 34.96/5.02      inference(light_normalisation,[status(thm)],[c_375,c_375,c_414]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_494,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34)) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_493,c_329]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_97,plain,
% 34.96/5.02      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_21,c_18]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3034,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X1_35)))) = k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_21,c_97]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3168,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_3034,c_21]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_106,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)))),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_21,c_18]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3233,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X1_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_20,c_3168]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3306,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X1_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_3233,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3322,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X1_35,X1_35)),X0_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_3306,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_720,plain,
% 34.96/5.02      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))),X4_34) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_494,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_409,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))),X4_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_329,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_419,plain,
% 34.96/5.02      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))),X4_34) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) ),
% 34.96/5.02      inference(light_normalisation,[status(thm)],[c_409,c_375]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_420,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),k5_xboole_0(X3_34,X4_34))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_419,c_154,c_329]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_421,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),k5_xboole_0(X3_34,X4_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34),X4_34)) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_420,c_329,c_375]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_496,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,k5_xboole_0(X3_34,X4_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),k5_xboole_0(X3_34,X4_34))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_19,c_493]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_570,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,k5_xboole_0(X3_34,X4_34))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),k5_xboole_0(X3_34,X4_34)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_496,c_493]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_732,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,k5_xboole_0(X3_34,X4_34))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))),X4_34) ),
% 34.96/5.02      inference(light_normalisation,[status(thm)],[c_720,c_421,c_570]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3867,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X3_35,X3_35)),k5_xboole_0(X0_34,X1_34))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),X0_34)),X1_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_3322,c_732]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3875,plain,
% 34.96/5.02      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),X0_34)),X1_34) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(X0_34,X1_34))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_3867,c_3322]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_5061,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X1_35,X2_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_106,c_3875]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_5077,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X1_35,X2_35)),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_3168,c_5061]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3251,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_3168,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3268,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X0_35,X1_35)),X0_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_3251,c_154]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_5142,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_5077,c_3268]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_22667,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_20,c_5142]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_37005,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_22667,c_5142]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_60710,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)),X0_34))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),X0_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_37005,c_3875]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_76102,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X4_35,X4_35)),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X4_35),k3_xboole_0(k2_tarski(X4_35,X4_35),k2_tarski(X2_35,X3_35))))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35)))),k5_xboole_0(k2_tarski(X3_35,X4_35),k3_xboole_0(k2_tarski(X3_35,X4_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X0_35,X1_35))))))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_95,c_494,c_60710]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_76409,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X2_35),k2_tarski(X3_35,X3_35)),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X2_35,X2_35))))))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_76102,c_97]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_137,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X1_35)),X0_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_19,c_128]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_76621,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X3_35,X3_35),k2_tarski(X2_35,X2_35))))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_76409,c_137]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_76622,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X3_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_76621,c_21]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_5,negated_conjecture,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k2_tarski(sK0,sK0)))) ),
% 34.96/5.02      inference(cnf_transformation,[],[f42]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_16,negated_conjecture,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)))),k2_tarski(sK0,sK0)))) ),
% 34.96/5.02      inference(subtyping,[status(esa)],[c_5]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_34,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_20,c_16]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_37,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k2_tarski(sK0,sK0))))) != k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_19,c_34]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_39,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_19,c_37]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_36928,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_22667,c_39]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_76874,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_76622,c_36928]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_3121,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_20,c_3034]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_4911,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_3121,c_3034]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_37006,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X1_35,X2_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X2_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X2_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_22667,c_4911]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_5079,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X3_35,X3_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X3_35,X3_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_20,c_5061]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_63396,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X3_35,X3_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X2_35,X3_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_37006,c_5079]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_76875,plain,
% 34.96/5.02      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) ),
% 34.96/5.02      inference(demodulation,[status(thm)],[c_76874,c_63396]) ).
% 34.96/5.02  
% 34.96/5.02  cnf(c_77531,plain,
% 34.96/5.02      ( $false ),
% 34.96/5.02      inference(superposition,[status(thm)],[c_76622,c_76875]) ).
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  % SZS output end CNFRefutation for theBenchmark.p
% 34.96/5.02  
% 34.96/5.02  ------                               Statistics
% 34.96/5.02  
% 34.96/5.02  ------ General
% 34.96/5.02  
% 34.96/5.02  abstr_ref_over_cycles:                  0
% 34.96/5.02  abstr_ref_under_cycles:                 0
% 34.96/5.02  gc_basic_clause_elim:                   0
% 34.96/5.02  forced_gc_time:                         0
% 34.96/5.02  parsing_time:                           0.032
% 34.96/5.02  unif_index_cands_time:                  0.
% 34.96/5.02  unif_index_add_time:                    0.
% 34.96/5.02  orderings_time:                         0.
% 34.96/5.02  out_proof_time:                         0.01
% 34.96/5.02  total_time:                             4.21
% 34.96/5.02  num_of_symbols:                         39
% 34.96/5.02  num_of_terms:                           131290
% 34.96/5.02  
% 34.96/5.02  ------ Preprocessing
% 34.96/5.02  
% 34.96/5.02  num_of_splits:                          0
% 34.96/5.02  num_of_split_atoms:                     0
% 34.96/5.02  num_of_reused_defs:                     0
% 34.96/5.02  num_eq_ax_congr_red:                    2
% 34.96/5.02  num_of_sem_filtered_clauses:            0
% 34.96/5.02  num_of_subtypes:                        2
% 34.96/5.02  monotx_restored_types:                  0
% 34.96/5.02  sat_num_of_epr_types:                   0
% 34.96/5.02  sat_num_of_non_cyclic_types:            0
% 34.96/5.02  sat_guarded_non_collapsed_types:        0
% 34.96/5.02  num_pure_diseq_elim:                    0
% 34.96/5.02  simp_replaced_by:                       0
% 34.96/5.02  res_preprocessed:                       16
% 34.96/5.02  prep_upred:                             0
% 34.96/5.02  prep_unflattend:                        0
% 34.96/5.02  smt_new_axioms:                         0
% 34.96/5.02  pred_elim_cands:                        0
% 34.96/5.02  pred_elim:                              0
% 34.96/5.02  pred_elim_cl:                           0
% 34.96/5.02  pred_elim_cycles:                       0
% 34.96/5.02  merged_defs:                            0
% 34.96/5.02  merged_defs_ncl:                        0
% 34.96/5.02  bin_hyper_res:                          0
% 34.96/5.02  prep_cycles:                            2
% 34.96/5.02  pred_elim_time:                         0.
% 34.96/5.02  splitting_time:                         0.
% 34.96/5.02  sem_filter_time:                        0.
% 34.96/5.02  monotx_time:                            0.
% 34.96/5.02  subtype_inf_time:                       0.
% 34.96/5.02  
% 34.96/5.02  ------ Problem properties
% 34.96/5.02  
% 34.96/5.02  clauses:                                6
% 34.96/5.02  conjectures:                            1
% 34.96/5.02  epr:                                    0
% 34.96/5.02  horn:                                   6
% 34.96/5.02  ground:                                 1
% 34.96/5.02  unary:                                  6
% 34.96/5.02  binary:                                 0
% 34.96/5.02  lits:                                   6
% 34.96/5.02  lits_eq:                                6
% 34.96/5.02  fd_pure:                                0
% 34.96/5.02  fd_pseudo:                              0
% 34.96/5.02  fd_cond:                                0
% 34.96/5.02  fd_pseudo_cond:                         0
% 34.96/5.02  ac_symbols:                             0
% 34.96/5.02  
% 34.96/5.02  ------ Propositional Solver
% 34.96/5.02  
% 34.96/5.02  prop_solver_calls:                      13
% 34.96/5.02  prop_fast_solver_calls:                 44
% 34.96/5.02  smt_solver_calls:                       0
% 34.96/5.02  smt_fast_solver_calls:                  0
% 34.96/5.02  prop_num_of_clauses:                    284
% 34.96/5.02  prop_preprocess_simplified:             245
% 34.96/5.02  prop_fo_subsumed:                       0
% 34.96/5.02  prop_solver_time:                       0.
% 34.96/5.02  smt_solver_time:                        0.
% 34.96/5.02  smt_fast_solver_time:                   0.
% 34.96/5.02  prop_fast_solver_time:                  0.
% 34.96/5.02  prop_unsat_core_time:                   0.
% 34.96/5.02  
% 34.96/5.02  ------ QBF
% 34.96/5.02  
% 34.96/5.02  qbf_q_res:                              0
% 34.96/5.02  qbf_num_tautologies:                    0
% 34.96/5.02  qbf_prep_cycles:                        0
% 34.96/5.02  
% 34.96/5.02  ------ BMC1
% 34.96/5.02  
% 34.96/5.02  bmc1_current_bound:                     -1
% 34.96/5.02  bmc1_last_solved_bound:                 -1
% 34.96/5.02  bmc1_unsat_core_size:                   -1
% 34.96/5.02  bmc1_unsat_core_parents_size:           -1
% 34.96/5.02  bmc1_merge_next_fun:                    0
% 34.96/5.02  bmc1_unsat_core_clauses_time:           0.
% 34.96/5.02  
% 34.96/5.02  ------ Instantiation
% 34.96/5.02  
% 34.96/5.02  inst_num_of_clauses:                    0
% 34.96/5.02  inst_num_in_passive:                    0
% 34.96/5.02  inst_num_in_active:                     0
% 34.96/5.02  inst_num_in_unprocessed:                0
% 34.96/5.02  inst_num_of_loops:                      0
% 34.96/5.02  inst_num_of_learning_restarts:          0
% 34.96/5.02  inst_num_moves_active_passive:          0
% 34.96/5.02  inst_lit_activity:                      0
% 34.96/5.02  inst_lit_activity_moves:                0
% 34.96/5.02  inst_num_tautologies:                   0
% 34.96/5.02  inst_num_prop_implied:                  0
% 34.96/5.02  inst_num_existing_simplified:           0
% 34.96/5.02  inst_num_eq_res_simplified:             0
% 34.96/5.02  inst_num_child_elim:                    0
% 34.96/5.02  inst_num_of_dismatching_blockings:      0
% 34.96/5.02  inst_num_of_non_proper_insts:           0
% 34.96/5.02  inst_num_of_duplicates:                 0
% 34.96/5.02  inst_inst_num_from_inst_to_res:         0
% 34.96/5.02  inst_dismatching_checking_time:         0.
% 34.96/5.02  
% 34.96/5.02  ------ Resolution
% 34.96/5.02  
% 34.96/5.02  res_num_of_clauses:                     0
% 34.96/5.02  res_num_in_passive:                     0
% 34.96/5.02  res_num_in_active:                      0
% 34.96/5.02  res_num_of_loops:                       18
% 34.96/5.02  res_forward_subset_subsumed:            0
% 34.96/5.02  res_backward_subset_subsumed:           0
% 34.96/5.02  res_forward_subsumed:                   0
% 34.96/5.02  res_backward_subsumed:                  0
% 34.96/5.02  res_forward_subsumption_resolution:     0
% 34.96/5.02  res_backward_subsumption_resolution:    0
% 34.96/5.02  res_clause_to_clause_subsumption:       213113
% 34.96/5.02  res_orphan_elimination:                 0
% 34.96/5.02  res_tautology_del:                      0
% 34.96/5.02  res_num_eq_res_simplified:              0
% 34.96/5.02  res_num_sel_changes:                    0
% 34.96/5.02  res_moves_from_active_to_pass:          0
% 34.96/5.02  
% 34.96/5.02  ------ Superposition
% 34.96/5.02  
% 34.96/5.02  sup_time_total:                         0.
% 34.96/5.02  sup_time_generating:                    0.
% 34.96/5.02  sup_time_sim_full:                      0.
% 34.96/5.02  sup_time_sim_immed:                     0.
% 34.96/5.02  
% 34.96/5.02  sup_num_of_clauses:                     3310
% 34.96/5.02  sup_num_in_active:                      138
% 34.96/5.02  sup_num_in_passive:                     3172
% 34.96/5.02  sup_num_of_loops:                       159
% 34.96/5.02  sup_fw_superposition:                   19145
% 34.96/5.02  sup_bw_superposition:                   17636
% 34.96/5.02  sup_immediate_simplified:               38101
% 34.96/5.02  sup_given_eliminated:                   2
% 34.96/5.02  comparisons_done:                       0
% 34.96/5.02  comparisons_avoided:                    0
% 34.96/5.02  
% 34.96/5.02  ------ Simplifications
% 34.96/5.02  
% 34.96/5.02  
% 34.96/5.02  sim_fw_subset_subsumed:                 0
% 34.96/5.02  sim_bw_subset_subsumed:                 0
% 34.96/5.02  sim_fw_subsumed:                        1313
% 34.96/5.02  sim_bw_subsumed:                        107
% 34.96/5.02  sim_fw_subsumption_res:                 0
% 34.96/5.02  sim_bw_subsumption_res:                 0
% 34.96/5.02  sim_tautology_del:                      0
% 34.96/5.02  sim_eq_tautology_del:                   16516
% 34.96/5.02  sim_eq_res_simp:                        0
% 34.96/5.02  sim_fw_demodulated:                     38238
% 34.96/5.02  sim_bw_demodulated:                     91
% 34.96/5.02  sim_light_normalised:                   2286
% 34.96/5.02  sim_joinable_taut:                      0
% 34.96/5.02  sim_joinable_simp:                      0
% 34.96/5.02  sim_ac_normalised:                      0
% 34.96/5.02  sim_smt_subsumption:                    0
% 34.96/5.02  
%------------------------------------------------------------------------------
