%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t67_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:02 EDT 2019

% Result     : Theorem 18.28s
% Output     : Refutation 18.28s
% Verified   : 
% Statistics : Number of formulae       :   30 (  62 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :   31 (  63 expanded)
%              Number of equality atoms :   30 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) ),
    inference(forward_demodulation,[],[f192,f38])).

fof(f38,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t67_enumset1.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t67_enumset1.p',t4_xboole_1)).

fof(f192,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k2_tarski(sK6,sK7),k2_tarski(sK2,sK3)))) ),
    inference(forward_demodulation,[],[f191,f38])).

fof(f191,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK6,sK7),k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))) ),
    inference(forward_demodulation,[],[f166,f22])).

fof(f166,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)),k2_tarski(sK6,sK7))) ),
    inference(superposition,[],[f46,f38])).

fof(f46,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK6,sK7),k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))) ),
    inference(forward_demodulation,[],[f45,f38])).

fof(f45,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK6,sK7),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f38,f32])).

fof(f32,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) != k2_xboole_0(k2_tarski(sK6,sK7),k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))) ),
    inference(backward_demodulation,[],[f23,f31])).

fof(f31,plain,(
    k2_xboole_0(k2_tarski(sK6,sK7),k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) ),
    inference(forward_demodulation,[],[f30,f22])).

fof(f30,plain,(
    k2_xboole_0(k2_tarski(sK6,sK7),k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) ),
    inference(backward_demodulation,[],[f22,f29])).

fof(f29,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)),k2_tarski(sK6,sK7)) ),
    inference(definition_unfolding,[],[f19,f27,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_tarski(X4,X5)) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t67_enumset1.p',l53_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t67_enumset1.p',t54_enumset1)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) ),
    inference(definition_unfolding,[],[f26,f24,f24])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t67_enumset1.p',l75_enumset1)).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t67_enumset1.p',t67_enumset1)).
%------------------------------------------------------------------------------
