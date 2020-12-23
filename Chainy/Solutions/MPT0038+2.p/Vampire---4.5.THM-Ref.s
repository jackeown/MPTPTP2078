%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0038+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(subsumption_resolution,[],[f153,f178])).

fof(f178,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f134,f147])).

fof(f147,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f134,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f153,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f110,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f110,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f79,f102])).

fof(f102,plain,
    ( ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
   => ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f65])).

fof(f65,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
%------------------------------------------------------------------------------
