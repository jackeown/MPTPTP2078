%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0132+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:33 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   11 (  15 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(ennf_transformation,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f9])).

fof(f16,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)),k2_tarski(X3,X4)) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f19,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_tarski(sK3,sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(definition_unfolding,[],[f16,f17,f13])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_14,plain,
    ( k2_xboole_0(k1_tarski(X0_37),k2_tarski(X1_37,X2_37)) = k2_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X2_37)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_13,plain,
    ( k2_xboole_0(k2_xboole_0(X0_36,X1_36),X2_36) = k2_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_27,plain,
    ( k2_xboole_0(k2_tarski(X0_37,X1_37),k2_xboole_0(k1_tarski(X2_37),X0_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_37),k2_tarski(X1_37,X2_37)),X0_36) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_53,plain,
    ( k2_xboole_0(k1_tarski(X0_37),k2_xboole_0(k2_tarski(X1_37,X2_37),X0_36)) = k2_xboole_0(k2_tarski(X0_37,X1_37),k2_xboole_0(k1_tarski(X2_37),X0_36)) ),
    inference(superposition,[status(thm)],[c_27,c_13])).

cnf(c_3,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_tarski(sK3,sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_tarski(sK3,sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_24,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_tarski(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_13,c_12])).

cnf(c_88,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_53,c_24])).

cnf(c_98,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_88])).


%------------------------------------------------------------------------------
