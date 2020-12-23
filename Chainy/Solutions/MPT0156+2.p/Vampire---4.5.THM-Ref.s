%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0156+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  54 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 (  55 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(subsumption_resolution,[],[f502,f470])).

fof(f470,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X3)) ),
    inference(definition_unfolding,[],[f345,f456])).

fof(f456,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X3)) ),
    inference(definition_unfolding,[],[f343,f363])).

fof(f363,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f218])).

fof(f218,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f343,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f345,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f502,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k2_tarski(sK18,sK18)) != k2_xboole_0(k2_tarski(sK15,sK16),k2_tarski(sK17,sK18)) ),
    inference(forward_demodulation,[],[f501,f352])).

fof(f352,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f501,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k2_tarski(sK18,sK18)) != k2_xboole_0(k2_tarski(sK17,sK18),k2_tarski(sK15,sK16)) ),
    inference(forward_demodulation,[],[f500,f379])).

fof(f379,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f219])).

fof(f219,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f500,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k2_tarski(sK18,sK18)) != k2_xboole_0(k2_tarski(sK17,sK18),k1_enumset1(sK15,sK15,sK16)) ),
    inference(forward_demodulation,[],[f499,f352])).

fof(f499,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k2_tarski(sK18,sK18)) != k2_xboole_0(k1_enumset1(sK15,sK15,sK16),k2_tarski(sK17,sK18)) ),
    inference(forward_demodulation,[],[f463,f465])).

fof(f465,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4)) ),
    inference(definition_unfolding,[],[f339,f457])).

fof(f457,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4)) ),
    inference(definition_unfolding,[],[f338,f456,f363])).

fof(f338,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f339,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f186])).

fof(f186,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f463,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k2_tarski(sK18,sK18)) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK15,sK15,sK16),k2_tarski(sK17,sK17)),k2_tarski(sK18,sK18)) ),
    inference(definition_unfolding,[],[f335,f456,f457])).

fof(f335,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k3_enumset1(sK15,sK15,sK16,sK17,sK18) ),
    inference(cnf_transformation,[],[f263])).

fof(f263,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k3_enumset1(sK15,sK15,sK16,sK17,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f226,f262])).

fof(f262,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK15,sK16,sK17,sK18) != k3_enumset1(sK15,sK15,sK16,sK17,sK18) ),
    introduced(choice_axiom,[])).

fof(f226,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f222])).

fof(f222,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f221])).

fof(f221,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
