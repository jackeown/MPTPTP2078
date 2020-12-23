%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0172+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  31 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  32 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(subsumption_resolution,[],[f420,f419])).

fof(f419,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) ),
    inference(definition_unfolding,[],[f312,f318,f417])).

fof(f417,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f339,f318])).

fof(f339,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f236])).

fof(f236,axiom,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(f318,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f222])).

fof(f222,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f312,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f420,plain,(
    k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6) != k2_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f311,f418])).

fof(f418,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f338,f417,f417])).

fof(f338,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f190])).

fof(f190,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f311,plain,(
    k2_tarski(sK5,sK6) != k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(cnf_transformation,[],[f263])).

fof(f263,plain,(
    k2_tarski(sK5,sK6) != k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f242,f262])).

fof(f262,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1)
   => k2_tarski(sK5,sK6) != k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f242,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f238])).

fof(f238,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f237])).

fof(f237,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).
%------------------------------------------------------------------------------
