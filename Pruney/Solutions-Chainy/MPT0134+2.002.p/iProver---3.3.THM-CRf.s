%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:21 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 111 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 118 expanded)
%              Number of equality atoms :   45 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f16,f14,f21])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f17,f14,f22])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f18,f14,f23])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))))) ),
    inference(definition_unfolding,[],[f19,f14,f21,f22,f24])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3)) ),
    inference(definition_unfolding,[],[f13,f14,f14,f14,f14,f14,f14])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) != k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) != k3_enumset1(X0,X1,X2,X3,X4)
   => k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).

fof(f20,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) ),
    inference(definition_unfolding,[],[f20,f14,f23,f24])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4))))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37)))),k3_xboole_0(k1_tarski(X0_37),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37)),k3_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37)),k3_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37))))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_199,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36)),X3_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36)),X3_36)) = k5_xboole_0(k5_xboole_0(X0_36,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36))),k3_xboole_0(X0_36,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36)))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_41,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_34,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != X0_36
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) != X0_36 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_40,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))))
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_199,c_41,c_40,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:02:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.35  % Running in FOF mode
% 2.11/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/1.00  
% 2.11/1.00  ------  iProver source info
% 2.11/1.00  
% 2.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/1.00  git: non_committed_changes: false
% 2.11/1.00  git: last_make_outside_of_git: false
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  ------ Parsing...
% 2.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.11/1.00  ------ Proving...
% 2.11/1.00  ------ Problem Properties 
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  clauses                                 3
% 2.11/1.00  conjectures                             1
% 2.11/1.00  EPR                                     0
% 2.11/1.00  Horn                                    3
% 2.11/1.00  unary                                   3
% 2.11/1.00  binary                                  0
% 2.11/1.00  lits                                    3
% 2.11/1.00  lits eq                                 3
% 2.11/1.00  fd_pure                                 0
% 2.11/1.00  fd_pseudo                               0
% 2.11/1.00  fd_cond                                 0
% 2.11/1.00  fd_pseudo_cond                          0
% 2.11/1.00  AC symbols                              0
% 2.11/1.00  
% 2.11/1.00  ------ Input Options Time Limit: Unbounded
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  Current options:
% 2.11/1.00  ------ 
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  ------ Proving...
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  % SZS status Theorem for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  fof(f7,axiom,(
% 2.11/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f19,plain,(
% 2.11/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f7])).
% 2.11/1.00  
% 2.11/1.00  fof(f6,axiom,(
% 2.11/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f18,plain,(
% 2.11/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f6])).
% 2.11/1.00  
% 2.11/1.00  fof(f5,axiom,(
% 2.11/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f17,plain,(
% 2.11/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f5])).
% 2.11/1.00  
% 2.11/1.00  fof(f4,axiom,(
% 2.11/1.00    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f16,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f4])).
% 2.11/1.00  
% 2.11/1.00  fof(f3,axiom,(
% 2.11/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f15,plain,(
% 2.11/1.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f3])).
% 2.11/1.00  
% 2.11/1.00  fof(f2,axiom,(
% 2.11/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f14,plain,(
% 2.11/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f2])).
% 2.11/1.00  
% 2.11/1.00  fof(f21,plain,(
% 2.11/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k2_tarski(X0,X1)) )),
% 2.11/1.00    inference(definition_unfolding,[],[f15,f14])).
% 2.11/1.00  
% 2.11/1.00  fof(f22,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.11/1.00    inference(definition_unfolding,[],[f16,f14,f21])).
% 2.11/1.00  
% 2.11/1.00  fof(f23,plain,(
% 2.11/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.11/1.00    inference(definition_unfolding,[],[f17,f14,f22])).
% 2.11/1.00  
% 2.11/1.00  fof(f24,plain,(
% 2.11/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.11/1.00    inference(definition_unfolding,[],[f18,f14,f23])).
% 2.11/1.00  
% 2.11/1.00  fof(f26,plain,(
% 2.11/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))))) )),
% 2.11/1.00    inference(definition_unfolding,[],[f19,f14,f21,f22,f24])).
% 2.11/1.00  
% 2.11/1.00  fof(f1,axiom,(
% 2.11/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f13,plain,(
% 2.11/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f1])).
% 2.11/1.00  
% 2.11/1.00  fof(f25,plain,(
% 2.11/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3))) )),
% 2.11/1.00    inference(definition_unfolding,[],[f13,f14,f14,f14,f14,f14,f14])).
% 2.11/1.00  
% 2.11/1.00  fof(f8,conjecture,(
% 2.11/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f9,negated_conjecture,(
% 2.11/1.00    ~! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.11/1.00    inference(negated_conjecture,[],[f8])).
% 2.11/1.00  
% 2.11/1.00  fof(f10,plain,(
% 2.11/1.00    ? [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) != k3_enumset1(X0,X1,X2,X3,X4)),
% 2.11/1.00    inference(ennf_transformation,[],[f9])).
% 2.11/1.00  
% 2.11/1.00  fof(f11,plain,(
% 2.11/1.00    ? [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) != k3_enumset1(X0,X1,X2,X3,X4) => k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f12,plain,(
% 2.11/1.00    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 2.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).
% 2.11/1.00  
% 2.11/1.00  fof(f20,plain,(
% 2.11/1.00    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 2.11/1.00    inference(cnf_transformation,[],[f12])).
% 2.11/1.00  
% 2.11/1.00  fof(f27,plain,(
% 2.11/1.00    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))))),
% 2.11/1.00    inference(definition_unfolding,[],[f20,f14,f23,f24])).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4))))) ),
% 2.11/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_11,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37)))),k3_xboole_0(k1_tarski(X0_37),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37)),k3_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))),k1_tarski(X3_37))),k1_tarski(X4_37))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37)),k3_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37)),k3_xboole_0(k1_tarski(X0_37),k1_tarski(X1_37))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37)),k3_xboole_0(k1_tarski(X2_37),k1_tarski(X3_37))),k1_tarski(X4_37))))) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_199,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))))) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_0,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)))) ),
% 2.11/1.00      inference(cnf_transformation,[],[f25]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_12,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36)),X3_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0_36,X1_36),k3_xboole_0(X0_36,X1_36)),X2_36)),X3_36)) = k5_xboole_0(k5_xboole_0(X0_36,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36))),k3_xboole_0(X0_36,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1_36,X2_36),k3_xboole_0(X1_36,X2_36)),X3_36)))) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_41,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))))) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_14,plain,
% 2.11/1.00      ( X0_36 != X1_36 | X2_36 != X1_36 | X2_36 = X0_36 ),
% 2.11/1.00      theory(equality) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_34,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != X0_36
% 2.11/1.00      | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))))
% 2.11/1.00      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) != X0_36 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_40,plain,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))))
% 2.11/1.00      | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))))
% 2.11/1.00      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))))) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2,negated_conjecture,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) ),
% 2.11/1.00      inference(cnf_transformation,[],[f27]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_10,negated_conjecture,
% 2.11/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))))) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(contradiction,plain,
% 2.11/1.00      ( $false ),
% 2.11/1.00      inference(minisat,[status(thm)],[c_199,c_41,c_40,c_10]) ).
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  ------                               Statistics
% 2.11/1.00  
% 2.11/1.00  ------ Selected
% 2.11/1.00  
% 2.11/1.00  total_time:                             0.09
% 2.11/1.00  
%------------------------------------------------------------------------------
