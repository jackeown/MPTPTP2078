%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0165+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   23 (  35 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  36 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(subsumption_resolution,[],[f341,f330])).

fof(f330,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X5,X5)) ),
    inference(definition_unfolding,[],[f282,f298])).

fof(f298,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X5,X5)) ),
    inference(definition_unfolding,[],[f250,f273])).

fof(f273,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f250,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f282,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f223])).

fof(f223,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f341,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK5,sK5)) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(forward_demodulation,[],[f304,f300])).

fof(f300,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X6,X6)) ),
    inference(definition_unfolding,[],[f249,f297])).

fof(f297,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X7,X7)) ),
    inference(definition_unfolding,[],[f241,f273])).

fof(f241,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f217])).

fof(f217,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f249,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f224])).

fof(f224,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f304,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK5,sK5)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f240,f298,f297])).

fof(f240,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f233,f234])).

fof(f234,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f233,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f231])).

fof(f231,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f230])).

fof(f230,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).
%------------------------------------------------------------------------------
