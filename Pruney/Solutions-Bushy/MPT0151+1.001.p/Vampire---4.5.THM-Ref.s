%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0151+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:26 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   21 (  31 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  32 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f20,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))) ),
    inference(forward_demodulation,[],[f19,f11])).

fof(f19,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)),k2_tarski(sK6,sK7))) ),
    inference(forward_demodulation,[],[f18,f11])).

fof(f18,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),k2_tarski(sK6,sK7)) ),
    inference(backward_demodulation,[],[f17,f11])).

fof(f17,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)),k2_tarski(sK6,sK7)) ),
    inference(definition_unfolding,[],[f10,f15,f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_tarski(X4,X5)) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) ),
    inference(definition_unfolding,[],[f14,f12,f12])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f10,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

% (24394)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

%------------------------------------------------------------------------------
