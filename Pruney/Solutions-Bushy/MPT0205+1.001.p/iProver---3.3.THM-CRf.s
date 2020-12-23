%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0205+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:43 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   11 (  15 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f13,f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f8])).

fof(f14,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_enumset1(X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f10,f11])).

fof(f17,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(definition_unfolding,[],[f14,f15,f11])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_11,plain,
    ( k2_xboole_0(k1_tarski(X0_41),k2_enumset1(X1_41,X2_41,X3_41,X4_41)) = k2_xboole_0(k2_enumset1(X0_41,X1_41,X2_41,X3_41),k1_tarski(X4_41)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_12,plain,
    ( k2_xboole_0(k2_xboole_0(X0_40,X1_40),X2_40) = k2_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_21,plain,
    ( k2_xboole_0(k2_enumset1(X0_41,X1_41,X2_41,X3_41),k2_xboole_0(k1_tarski(X4_41),X0_40)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_41),k2_enumset1(X1_41,X2_41,X3_41,X4_41)),X0_40) ),
    inference(superposition,[status(thm)],[c_11,c_12])).

cnf(c_25,plain,
    ( k2_xboole_0(k1_tarski(X0_41),k2_xboole_0(k2_enumset1(X1_41,X2_41,X3_41,X4_41),X0_40)) = k2_xboole_0(k2_enumset1(X0_41,X1_41,X2_41,X3_41),k2_xboole_0(k1_tarski(X4_41),X0_40)) ),
    inference(superposition,[status(thm)],[c_21,c_12])).

cnf(c_2,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_20,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) ),
    inference(demodulation,[status(thm)],[c_12,c_10])).

cnf(c_27,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) ),
    inference(demodulation,[status(thm)],[c_25,c_20])).

cnf(c_28,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_27])).


%------------------------------------------------------------------------------
