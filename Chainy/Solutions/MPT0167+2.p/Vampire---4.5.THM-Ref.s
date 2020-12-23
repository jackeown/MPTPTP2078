%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0167+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(subsumption_resolution,[],[f277,f272])).

fof(f272,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f277,plain,(
    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f242,f248])).

fof(f248,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f242,plain,(
    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f237])).

fof(f237,plain,(
    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f235,f236])).

fof(f236,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f235,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f233])).

fof(f233,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f232])).

fof(f232,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
%------------------------------------------------------------------------------
