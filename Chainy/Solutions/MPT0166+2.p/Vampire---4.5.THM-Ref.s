%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0166+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(subsumption_resolution,[],[f391,f304])).

fof(f304,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f391,plain,(
    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    inference(superposition,[],[f290,f293])).

fof(f293,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f220])).

fof(f220,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f290,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f247])).

fof(f247,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f236,f246])).

fof(f246,plain,
    ( ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0)
   => k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f236,plain,(
    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f232])).

fof(f232,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f231])).

fof(f231,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
%------------------------------------------------------------------------------
