%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0171+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   16 (  23 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  24 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(subsumption_resolution,[],[f393,f392])).

fof(f392,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f306,f389])).

fof(f389,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)) ),
    inference(definition_unfolding,[],[f301,f318])).

fof(f318,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f231])).

fof(f231,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f301,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f306,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f393,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f300,f318,f389])).

fof(f300,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f253])).

fof(f253,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f241,f252])).

fof(f252,plain,
    ( ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f241,plain,(
    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f237])).

fof(f237,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f236])).

fof(f236,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).
%------------------------------------------------------------------------------
