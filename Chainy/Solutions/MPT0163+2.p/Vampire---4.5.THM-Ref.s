%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0163+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  23 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  24 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f515,plain,(
    $false ),
    inference(subsumption_resolution,[],[f472,f497])).

fof(f497,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) ),
    inference(definition_unfolding,[],[f386,f467,f352])).

fof(f352,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f222])).

fof(f222,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f467,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) ),
    inference(definition_unfolding,[],[f353,f376])).

fof(f376,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f353,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f386,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f472,plain,(
    k4_enumset1(sK15,sK15,sK15,sK16,sK17,sK18) != k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k1_enumset1(sK18,sK18,sK18)) ),
    inference(definition_unfolding,[],[f342,f467])).

fof(f342,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k4_enumset1(sK15,sK15,sK15,sK16,sK17,sK18) ),
    inference(cnf_transformation,[],[f270])).

fof(f270,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k4_enumset1(sK15,sK15,sK15,sK16,sK17,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f233,f269])).

fof(f269,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k4_enumset1(X0,X0,X0,X1,X2,X3)
   => k2_enumset1(sK15,sK16,sK17,sK18) != k4_enumset1(sK15,sK15,sK15,sK16,sK17,sK18) ),
    introduced(choice_axiom,[])).

fof(f233,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f229])).

fof(f229,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f228])).

fof(f228,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
%------------------------------------------------------------------------------
