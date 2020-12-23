%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0207+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:16 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   43 (  86 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   21
%              Number of atoms          :   44 (  87 expanded)
%              Number of equality atoms :   43 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1790,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1789])).

fof(f1789,plain,(
    k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f1788,f287])).

fof(f287,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1788,plain,(
    k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_tarski(sK7))) ),
    inference(superposition,[],[f1765,f469])).

fof(f469,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f285,f287])).

fof(f285,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1765,plain,(
    k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f1764,f287])).

fof(f1764,plain,(
    k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK8)))) ),
    inference(forward_demodulation,[],[f1763,f469])).

fof(f1763,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f1762,f285])).

fof(f1762,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k1_tarski(sK8)),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    inference(forward_demodulation,[],[f1761,f469])).

fof(f1761,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k1_tarski(sK8)))) ),
    inference(forward_demodulation,[],[f1704,f469])).

fof(f1704,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k1_tarski(sK6)))) ),
    inference(backward_demodulation,[],[f1701,f469])).

fof(f1701,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f1698,f414])).

fof(f414,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f341,f291])).

fof(f291,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f256])).

fof(f256,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f341,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f220])).

fof(f220,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f1698,plain,(
    k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK8),k2_enumset1(sK6,sK6,sK6,sK7))) ),
    inference(backward_demodulation,[],[f1610,f352])).

fof(f352,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f258])).

fof(f258,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f1610,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) != k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f1558,f285])).

fof(f1558,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k1_tarski(sK8)),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    inference(backward_demodulation,[],[f451,f414])).

fof(f451,plain,(
    k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) ),
    inference(forward_demodulation,[],[f450,f287])).

fof(f450,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k1_tarski(sK8))) != k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK8),k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    inference(forward_demodulation,[],[f449,f287])).

fof(f449,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k1_tarski(sK8))) != k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK8),k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))) ),
    inference(backward_demodulation,[],[f387,f287])).

fof(f387,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k1_tarski(sK8))) != k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)),k2_enumset1(sK7,sK7,sK7,sK8)) ),
    inference(definition_unfolding,[],[f282,f381,f294,f291])).

fof(f294,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f240])).

fof(f240,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f381,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k1_tarski(X8))) ),
    inference(definition_unfolding,[],[f307,f380])).

fof(f380,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f304,f294])).

fof(f304,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f268])).

fof(f268,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(f307,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f217])).

fof(f217,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f282,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(cnf_transformation,[],[f281])).

fof(f281,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f279,f280])).

fof(f280,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f279,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(ennf_transformation,[],[f219])).

fof(f219,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(negated_conjecture,[],[f218])).

fof(f218,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
%------------------------------------------------------------------------------
