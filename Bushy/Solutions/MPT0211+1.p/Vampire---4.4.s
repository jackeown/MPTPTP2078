%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t137_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:59 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  93 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 142 expanded)
%              Number of equality atoms :   42 (  83 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f39,f111,f120,f127,f192,f201,f208,f348])).

fof(f348,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f345])).

fof(f345,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_13 ),
    inference(superposition,[],[f200,f275])).

fof(f275,plain,(
    ! [X33,X31,X32] : k1_enumset1(X32,X31,X33) = k2_enumset1(X32,X31,X33,X32) ),
    inference(superposition,[],[f177,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X2,X0) ),
    inference(superposition,[],[f22,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t137_enumset1.p',t71_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t137_enumset1.p',t112_enumset1)).

fof(f177,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X4,X6,X7) ),
    inference(superposition,[],[f94,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t137_enumset1.p',l53_enumset1)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t137_enumset1.p',commutativity_k2_tarski)).

fof(f200,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_13
  <=> k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f208,plain,
    ( ~ spl3_15
    | spl3_11 ),
    inference(avatar_split_clause,[],[f194,f190,f206])).

fof(f206,plain,
    ( spl3_15
  <=> k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f190,plain,
    ( spl3_11
  <=> k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f194,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK1,sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f191,f22])).

fof(f191,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f190])).

fof(f201,plain,
    ( ~ spl3_13
    | spl3_11 ),
    inference(avatar_split_clause,[],[f193,f190,f199])).

fof(f193,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f191,f22])).

fof(f192,plain,
    ( ~ spl3_11
    | spl3_3 ),
    inference(avatar_split_clause,[],[f181,f37,f190])).

fof(f37,plain,
    ( spl3_3
  <=> k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f181,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK0,sK2)
    | ~ spl3_3 ),
    inference(superposition,[],[f38,f94])).

fof(f38,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f127,plain,
    ( ~ spl3_9
    | spl3_5 ),
    inference(avatar_split_clause,[],[f112,f109,f125])).

fof(f125,plain,
    ( spl3_9
  <=> k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f109,plain,
    ( spl3_5
  <=> k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK2,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f110,f22])).

fof(f110,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f120,plain,
    ( ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f113,f109,f118])).

fof(f118,plain,
    ( spl3_7
  <=> k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f113,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f110,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    inference(superposition,[],[f22,f21])).

fof(f111,plain,
    ( ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f101,f37,f109])).

fof(f101,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)
    | ~ spl3_3 ),
    inference(superposition,[],[f38,f23])).

fof(f39,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f32,f28,f37])).

fof(f28,plain,
    ( spl3_1
  <=> k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f32,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f31,f20])).

fof(f31,plain,
    ( k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f29,f20])).

fof(f29,plain,
    ( k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f30,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t137_enumset1.p',t137_enumset1)).
%------------------------------------------------------------------------------
