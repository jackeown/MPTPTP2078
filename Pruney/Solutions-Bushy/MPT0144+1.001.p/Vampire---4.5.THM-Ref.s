%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0144+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  36 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   26 (  37 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,(
    k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(superposition,[],[f92,f22])).

fof(f22,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f14,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f92,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_tarski(sK5,sK6))) != k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(forward_demodulation,[],[f91,f12])).

fof(f91,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_tarski(sK5,sK6))) != k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK5,sK6))) ),
    inference(forward_demodulation,[],[f44,f22])).

fof(f44,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_tarski(sK5,sK6))) != k2_xboole_0(k2_tarski(sK5,sK6),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(forward_demodulation,[],[f43,f12])).

fof(f43,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_tarski(sK5,sK6))) != k2_xboole_0(k2_tarski(sK5,sK6),k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4))) ),
    inference(forward_demodulation,[],[f18,f12])).

fof(f18,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_tarski(sK5,sK6))) != k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)),k2_tarski(sK5,sK6)) ),
    inference(definition_unfolding,[],[f11,f17,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_tarski(X5,X6))) ),
    inference(definition_unfolding,[],[f16,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f11,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

%------------------------------------------------------------------------------
