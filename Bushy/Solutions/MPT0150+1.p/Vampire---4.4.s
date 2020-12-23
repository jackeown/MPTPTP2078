%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t66_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:02 EDT 2019

% Result     : Theorem 18.34s
% Output     : Refutation 18.34s
% Verified   : 
% Statistics : Number of formulae       :   32 (  68 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   17
%              Number of atoms          :   33 (  69 expanded)
%              Number of equality atoms :   32 (  68 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(forward_demodulation,[],[f193,f37])).

fof(f37,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t66_enumset1.p',commutativity_k2_xboole_0)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t66_enumset1.p',t4_xboole_1)).

fof(f193,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(forward_demodulation,[],[f192,f37])).

fof(f192,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(forward_demodulation,[],[f191,f21])).

fof(f191,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK1,sK2,sK3)),k1_enumset1(sK5,sK6,sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(superposition,[],[f47,f37])).

fof(f47,plain,(
    k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(forward_demodulation,[],[f46,f21])).

fof(f46,plain,(
    k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK4)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(forward_demodulation,[],[f45,f37])).

fof(f45,plain,(
    k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(forward_demodulation,[],[f44,f21])).

fof(f44,plain,(
    k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_enumset1(sK1,sK2,sK3)))) ),
    inference(backward_demodulation,[],[f37,f31])).

fof(f31,plain,(
    k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK5,sK6,sK7)))) ),
    inference(backward_demodulation,[],[f22,f30])).

fof(f30,plain,(
    k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK5,sK6,sK7))) ),
    inference(forward_demodulation,[],[f29,f21])).

fof(f29,plain,(
    k2_xboole_0(k1_enumset1(sK5,sK6,sK7),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_tarski(sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK5,sK6,sK7))) ),
    inference(backward_demodulation,[],[f21,f28])).

fof(f28,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_tarski(sK4)),k1_enumset1(sK5,sK6,sK7)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK5,sK6,sK7))) ),
    inference(definition_unfolding,[],[f19,f26,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t66_enumset1.p',t44_enumset1)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t66_enumset1.p',t50_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),k2_xboole_0(k1_tarski(X4),k1_enumset1(X5,X6,X7))) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t66_enumset1.p',l75_enumset1)).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t66_enumset1.p',t66_enumset1)).
%------------------------------------------------------------------------------
