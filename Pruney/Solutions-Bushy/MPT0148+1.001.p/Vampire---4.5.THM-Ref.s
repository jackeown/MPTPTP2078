%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0148+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  23 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  24 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK7)))) ),
    inference(superposition,[],[f17,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f17,plain,(
    k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK7))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK7)))) ),
    inference(definition_unfolding,[],[f10,f15,f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)),k2_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X7))) ),
    inference(definition_unfolding,[],[f14,f12,f12])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f10,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

%------------------------------------------------------------------------------
