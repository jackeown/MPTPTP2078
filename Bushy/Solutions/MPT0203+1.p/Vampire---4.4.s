%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t129_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:57 EDT 2019

% Result     : Theorem 18.34s
% Output     : Refutation 18.34s
% Verified   : 
% Statistics : Number of formulae       :   24 (  30 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(forward_demodulation,[],[f186,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t129_enumset1.p',commutativity_k2_xboole_0)).

fof(f186,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2))) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f23,f22])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t129_enumset1.p',t4_xboole_1)).

fof(f30,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(backward_demodulation,[],[f23,f29])).

fof(f29,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(backward_demodulation,[],[f22,f28])).

fof(f28,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(definition_unfolding,[],[f20,f27,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t129_enumset1.p',t51_enumset1)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t129_enumset1.p',t46_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t129_enumset1.p',l142_enumset1)).

fof(f20,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t129_enumset1.p',t129_enumset1)).
%------------------------------------------------------------------------------
