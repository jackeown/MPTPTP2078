%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0237+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:48 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   18 (  22 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f10,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,plain,(
    k3_tarski(k2_xboole_0(k1_tarski(k1_tarski(sK0)),k1_tarski(k1_tarski(sK1)))) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f10,f9,f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f8,f9])).

cnf(c_1,negated_conjecture,
    ( k3_tarski(k2_xboole_0(k1_tarski(k1_tarski(sK0)),k1_tarski(k1_tarski(sK1)))) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_8,negated_conjecture,
    ( k3_tarski(k2_xboole_0(k1_tarski(k1_tarski(sK0)),k1_tarski(k1_tarski(sK1)))) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_9,plain,
    ( k3_tarski(k2_xboole_0(k1_tarski(X0_34),k1_tarski(X1_34))) = k2_xboole_0(X0_34,X1_34) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_16,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(demodulation,[status(thm)],[c_8,c_9])).

cnf(c_17,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16])).


%------------------------------------------------------------------------------
