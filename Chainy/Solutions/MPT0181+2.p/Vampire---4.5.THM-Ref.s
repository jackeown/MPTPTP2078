%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0181+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  26 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  27 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f555,plain,(
    $false ),
    inference(subsumption_resolution,[],[f554,f505])).

fof(f505,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f364,f363])).

fof(f363,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f364,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f191])).

fof(f191,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f554,plain,(
    k2_xboole_0(k2_tarski(sK15,sK16),k1_tarski(sK17)) != k2_xboole_0(k1_tarski(sK15),k2_tarski(sK16,sK17)) ),
    inference(forward_demodulation,[],[f553,f393])).

fof(f393,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f553,plain,(
    k2_xboole_0(k2_tarski(sK15,sK16),k1_tarski(sK17)) != k2_xboole_0(k1_tarski(sK15),k2_tarski(sK17,sK16)) ),
    inference(forward_demodulation,[],[f503,f505])).

fof(f503,plain,(
    k2_xboole_0(k2_tarski(sK15,sK16),k1_tarski(sK17)) != k2_xboole_0(k2_tarski(sK15,sK17),k1_tarski(sK16)) ),
    inference(definition_unfolding,[],[f360,f363,f363])).

fof(f360,plain,(
    k1_enumset1(sK15,sK16,sK17) != k1_enumset1(sK15,sK17,sK16) ),
    inference(cnf_transformation,[],[f288])).

fof(f288,plain,(
    k1_enumset1(sK15,sK16,sK17) != k1_enumset1(sK15,sK17,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f251,f287])).

fof(f287,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK15,sK16,sK17) != k1_enumset1(sK15,sK17,sK16) ),
    introduced(choice_axiom,[])).

fof(f251,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f247])).

fof(f247,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f246])).

fof(f246,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
%------------------------------------------------------------------------------
