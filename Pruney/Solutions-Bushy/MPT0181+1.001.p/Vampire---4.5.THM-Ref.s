%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0181+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  21 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  27 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f19])).

fof(f19,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f18])).

fof(f18,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f17])).

fof(f17,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f15,f9])).

fof(f9,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f15,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl3_1
  <=> k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f16,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f13])).

fof(f11,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK1)) ),
    inference(definition_unfolding,[],[f8,f10,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f8,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

%------------------------------------------------------------------------------
