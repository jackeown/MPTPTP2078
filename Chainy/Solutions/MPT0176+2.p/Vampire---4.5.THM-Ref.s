%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0176+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(subsumption_resolution,[],[f709,f498])).

fof(f498,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f237])).

fof(f237,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

fof(f709,plain,(
    k2_tarski(sK1,sK2) != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(superposition,[],[f414,f477])).

fof(f477,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f223])).

fof(f223,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f414,plain,(
    k2_tarski(sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(cnf_transformation,[],[f346])).

fof(f346,plain,(
    k2_tarski(sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f247,f345])).

fof(f345,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
   => k2_tarski(sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f247,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f242])).

fof(f242,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f241])).

fof(f241,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_enumset1)).
%------------------------------------------------------------------------------
