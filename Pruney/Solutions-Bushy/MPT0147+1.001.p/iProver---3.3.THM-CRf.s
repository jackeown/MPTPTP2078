%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0147+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:35 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   23 (  27 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   24 (  28 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f7,f8])).

fof(f14,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f13,f10])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f11,f10,f10])).

fof(f17,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) ),
    inference(definition_unfolding,[],[f14,f16,f15])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_8,plain,
    ( k2_xboole_0(k2_xboole_0(X0_38,X1_38),X2_38) = k2_xboole_0(X0_38,k2_xboole_0(X1_38,X2_38)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_15,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) ),
    inference(demodulation,[status(thm)],[c_8,c_7])).

cnf(c_16,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_15])).


%------------------------------------------------------------------------------
