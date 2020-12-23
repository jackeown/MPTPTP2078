%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0131+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:24 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f20])).

fof(f20,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(superposition,[],[f16,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f16,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(definition_unfolding,[],[f10,f15,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)),k2_tarski(X3,X4)) ),
    inference(definition_unfolding,[],[f14,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f14,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f10,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

%------------------------------------------------------------------------------
