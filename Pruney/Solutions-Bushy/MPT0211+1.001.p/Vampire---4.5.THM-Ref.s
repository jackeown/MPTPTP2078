%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0211+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:32 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   33 (  44 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :   28 (  39 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f48])).

fof(f48,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f46])).

fof(f46,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f43,f22])).

fof(f22,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_1
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK1))
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f27,f31])).

fof(f31,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_3
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f27,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_2
  <=> k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(f28,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f25])).

fof(f19,plain,(
    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f18,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f18,plain,(
    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0)) ),
    inference(backward_demodulation,[],[f16,f11])).

fof(f16,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f10,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(f23,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f11,f21])).

%------------------------------------------------------------------------------
