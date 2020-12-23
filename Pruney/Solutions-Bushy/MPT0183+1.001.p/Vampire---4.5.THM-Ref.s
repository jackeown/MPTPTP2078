%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0183+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  21 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  22 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f13,f15])).

fof(f15,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4)) = k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f14,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f13,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK0)) ),
    inference(definition_unfolding,[],[f9,f11,f11])).

fof(f9,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

%------------------------------------------------------------------------------
