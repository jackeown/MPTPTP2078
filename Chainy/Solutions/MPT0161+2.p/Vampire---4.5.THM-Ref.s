%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0161+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  23 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  24 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f530,plain,(
    $false ),
    inference(subsumption_resolution,[],[f529,f467])).

fof(f467,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
    inference(definition_unfolding,[],[f350,f353,f353])).

fof(f353,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f218])).

fof(f218,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f350,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f190])).

fof(f190,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f529,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(forward_demodulation,[],[f468,f351])).

fof(f351,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f219])).

fof(f219,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f468,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f315,f461])).

fof(f461,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X3)) ),
    inference(definition_unfolding,[],[f331,f353])).

fof(f331,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f315,plain,(
    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f260])).

fof(f260,plain,(
    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f231,f259])).

fof(f259,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f231,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f227])).

fof(f227,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f226])).

fof(f226,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
%------------------------------------------------------------------------------
