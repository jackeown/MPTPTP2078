%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0145+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:35 EST 2020

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
   => k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f8,f9])).

fof(f16,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f18,plain,(
    k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)),k1_tarski(sK6)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK6))) ),
    inference(definition_unfolding,[],[f16,f15,f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_2,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)),k1_tarski(sK6)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK6))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)),k1_tarski(sK6)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK6))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_14,negated_conjecture,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_11,c_1,c_0])).


%------------------------------------------------------------------------------
