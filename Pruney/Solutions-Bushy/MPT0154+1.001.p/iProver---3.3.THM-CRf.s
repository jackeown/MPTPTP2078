%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0154+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:36 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f5])).

fof(f7,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f12,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f10,f9])).

fof(f15,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f12,f9,f13])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f11,f9])).

cnf(c_1,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_7,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_8,plain,
    ( k2_xboole_0(k1_tarski(X0_33),k1_tarski(X0_33)) = k1_tarski(X0_33) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_15,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(demodulation,[status(thm)],[c_7,c_8])).

cnf(c_16,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_15])).


%------------------------------------------------------------------------------
