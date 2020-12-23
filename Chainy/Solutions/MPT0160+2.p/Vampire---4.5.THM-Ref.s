%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0160+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  23 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  24 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f403,plain,(
    $false ),
    inference(subsumption_resolution,[],[f364,f363])).

fof(f363,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
    inference(definition_unfolding,[],[f298,f362])).

fof(f362,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)) ),
    inference(definition_unfolding,[],[f299,f306])).

fof(f306,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f218])).

fof(f218,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f299,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f298,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f219])).

fof(f219,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f364,plain,(
    k2_tarski(sK0,sK0) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f289,f306,f362])).

fof(f289,plain,(
    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f242])).

fof(f242,plain,(
    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f230,f241])).

fof(f241,plain,
    ( ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0)
   => k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f230,plain,(
    ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0) ),
    inference(ennf_transformation,[],[f226])).

fof(f226,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(negated_conjecture,[],[f225])).

fof(f225,conjecture,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
%------------------------------------------------------------------------------
