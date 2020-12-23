%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0174+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   19 (  24 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  25 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(subsumption_resolution,[],[f320,f361])).

fof(f361,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f306,f316])).

fof(f316,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)) ),
    inference(definition_unfolding,[],[f259,f315])).

fof(f315,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k3_enumset1(X7,X7,X7,X7,X7)) ),
    inference(definition_unfolding,[],[f250,f282])).

fof(f282,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f236])).

fof(f236,axiom,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

fof(f250,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f217])).

fof(f217,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f259,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f230])).

fof(f230,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(f306,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f228])).

fof(f228,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f320,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f249,f315])).

fof(f249,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f244])).

fof(f244,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f242,f243])).

fof(f243,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f242,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f240])).

fof(f240,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f239])).

fof(f239,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).
%------------------------------------------------------------------------------
