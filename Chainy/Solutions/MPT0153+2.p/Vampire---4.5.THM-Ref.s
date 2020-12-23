%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0153+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f397,plain,(
    $false ),
    inference(subsumption_resolution,[],[f337,f294])).

fof(f294,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f220])).

fof(f220,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f337,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(definition_unfolding,[],[f250,f315])).

fof(f315,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f190])).

fof(f190,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f250,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(cnf_transformation,[],[f234])).

fof(f234,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f222,f233])).

fof(f233,plain,
    ( ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)
   => k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f222,plain,(
    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) ),
    inference(ennf_transformation,[],[f219])).

fof(f219,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(negated_conjecture,[],[f218])).

fof(f218,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
%------------------------------------------------------------------------------
