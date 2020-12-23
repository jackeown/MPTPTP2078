%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t131_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:58 EDT 2019

% Result     : Theorem 18.31s
% Output     : Refutation 18.31s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2377,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2336])).

fof(f2336,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) ),
    inference(superposition,[],[f28,f194])).

fof(f194,plain,(
    ! [X14,X12,X10,X15,X13,X11] : k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k2_xboole_0(k1_tarski(X14),X15)) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_enumset1(X11,X12,X13,X14),X15)) ),
    inference(forward_demodulation,[],[f188,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t131_enumset1.p',t4_xboole_1)).

fof(f188,plain,(
    ! [X14,X12,X10,X15,X13,X11] : k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k2_xboole_0(k1_tarski(X14),X15)) = k2_xboole_0(k2_xboole_0(k1_tarski(X10),k2_enumset1(X11,X12,X13,X14)),X15) ),
    inference(superposition,[],[f21,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t131_enumset1.p',t47_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t131_enumset1.p',t50_enumset1)).

fof(f28,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) ),
    inference(backward_demodulation,[],[f21,f26])).

fof(f26,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(definition_unfolding,[],[f18,f25,f22])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_enumset1(X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t131_enumset1.p',l142_enumset1)).

fof(f18,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t131_enumset1.p',t131_enumset1)).
%------------------------------------------------------------------------------
