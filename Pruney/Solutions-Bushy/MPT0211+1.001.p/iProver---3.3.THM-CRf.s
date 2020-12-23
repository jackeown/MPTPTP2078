%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0211+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:44 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of clauses        :   10 (  14 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   11
%              Number of atoms          :   28 (  40 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f12,f11,f11])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f14,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f13,f11])).

fof(f17,plain,(
    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(definition_unfolding,[],[f14,f15])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_11,plain,
    ( k2_tarski(X0_35,X1_35) = k2_tarski(X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X2,X0),k2_tarski(X3,X1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X2_35,X3_35)) = k2_xboole_0(k2_tarski(X2_35,X0_35),k2_tarski(X3_35,X1_35)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_22,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_11,c_9])).

cnf(c_23,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_11,c_22])).

cnf(c_25,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK1)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_10,c_23])).

cnf(c_38,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_11,c_25])).


%------------------------------------------------------------------------------
