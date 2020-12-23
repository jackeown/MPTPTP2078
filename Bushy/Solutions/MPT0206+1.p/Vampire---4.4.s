%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t132_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:58 EDT 2019

% Result     : Theorem 18.32s
% Output     : Refutation 18.32s
% Verified   : 
% Statistics : Number of formulae       :   25 (  36 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   26 (  37 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,(
    k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_enumset1(sK6,sK7,sK8),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_enumset1(sK6,sK7,sK8),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(forward_demodulation,[],[f46,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t132_enumset1.p',commutativity_k2_xboole_0)).

fof(f46,plain,(
    k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_enumset1(sK6,sK7,sK8),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK6,sK7,sK8))) ),
    inference(forward_demodulation,[],[f45,f38])).

fof(f38,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f25,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t132_enumset1.p',t4_xboole_1)).

fof(f45,plain,(
    k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK6,sK7,sK8))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_enumset1(sK6,sK7,sK8))) ),
    inference(backward_demodulation,[],[f38,f32])).

fof(f32,plain,(
    k2_xboole_0(k1_enumset1(sK6,sK7,sK8),k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_enumset1(sK6,sK7,sK8))) ),
    inference(forward_demodulation,[],[f31,f24])).

fof(f31,plain,(
    k2_xboole_0(k1_enumset1(sK6,sK7,sK8),k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_enumset1(sK6,sK7,sK8))) ),
    inference(backward_demodulation,[],[f24,f30])).

fof(f30,plain,(
    k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)),k1_enumset1(sK6,sK7,sK8)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_enumset1(sK6,sK7,sK8))) ),
    inference(definition_unfolding,[],[f21,f29,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t132_enumset1.p',t54_enumset1)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k2_tarski(X4,X5),k1_enumset1(X6,X7,X8))) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t132_enumset1.p',t48_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t132_enumset1.p',l142_enumset1)).

fof(f21,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t132_enumset1.p',t132_enumset1)).
%------------------------------------------------------------------------------
