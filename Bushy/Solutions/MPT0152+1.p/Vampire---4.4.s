%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t68_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:02 EDT 2019

% Result     : Theorem 18.30s
% Output     : Refutation 18.30s
% Verified   : 
% Statistics : Number of formulae       :   32 (  65 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   17
%              Number of atoms          :   33 (  66 expanded)
%              Number of equality atoms :   32 (  65 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)))) != k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)))) ),
    inference(forward_demodulation,[],[f193,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t68_enumset1.p',commutativity_k2_xboole_0)).

fof(f193,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)))) != k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)),k1_tarski(sK7))) ),
    inference(superposition,[],[f49,f39])).

fof(f39,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f22,f21])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t68_enumset1.p',t4_xboole_1)).

fof(f49,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)))) ),
    inference(forward_demodulation,[],[f48,f21])).

fof(f48,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK0,sK1,sK2)))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)))) ),
    inference(forward_demodulation,[],[f47,f39])).

fof(f47,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK7),k1_enumset1(sK4,sK5,sK6)))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK4,sK5,sK6)))) ),
    inference(forward_demodulation,[],[f46,f39])).

fof(f46,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK7),k1_enumset1(sK4,sK5,sK6)))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK3)))) ),
    inference(backward_demodulation,[],[f39,f33])).

fof(f33,plain,(
    k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK7),k1_enumset1(sK4,sK5,sK6)))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)))) ),
    inference(backward_demodulation,[],[f22,f32])).

fof(f32,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)),k2_xboole_0(k1_tarski(sK7),k1_enumset1(sK4,sK5,sK6))) ),
    inference(forward_demodulation,[],[f31,f21])).

fof(f31,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK4,sK5,sK6))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)),k2_xboole_0(k1_tarski(sK7),k1_enumset1(sK4,sK5,sK6))) ),
    inference(forward_demodulation,[],[f30,f21])).

fof(f30,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k1_enumset1(sK4,sK5,sK6))) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK7),k1_enumset1(sK4,sK5,sK6))) ),
    inference(forward_demodulation,[],[f29,f21])).

fof(f29,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k1_enumset1(sK4,sK5,sK6))) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK7))) ),
    inference(backward_demodulation,[],[f21,f28])).

fof(f28,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k1_enumset1(sK4,sK5,sK6)),k1_tarski(sK7)) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK7))) ),
    inference(definition_unfolding,[],[f19,f26,f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)),k1_enumset1(X4,X5,X6)) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t68_enumset1.p',t46_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t68_enumset1.p',l68_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)),k2_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X7))) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t68_enumset1.p',l75_enumset1)).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t68_enumset1.p',t68_enumset1)).
%------------------------------------------------------------------------------
