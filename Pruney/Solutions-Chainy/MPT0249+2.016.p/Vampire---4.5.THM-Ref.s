%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 192 expanded)
%              Number of leaves         :   26 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  237 ( 445 expanded)
%              Number of equality atoms :   92 ( 222 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f249,f324,f351,f374,f410])).

fof(f410,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f325,f321,f76,f112])).

fof(f112,plain,
    ( spl3_5
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( spl3_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f321,plain,
    ( spl3_10
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f325,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f323,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f323,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f321])).

fof(f374,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_10
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl3_4
    | spl3_5
    | ~ spl3_10
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f350,f114,f366])).

fof(f366,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(resolution,[],[f330,f326])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f312,f323])).

fof(f312,plain,
    ( ! [X0] :
        ( r1_tarski(k2_xboole_0(sK1,sK2),X0)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ! [X0] :
        ( r1_tarski(k2_xboole_0(sK1,sK2),X0)
        | ~ r2_hidden(sK0,X0)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl3_4 ),
    inference(superposition,[],[f69,f93])).

fof(f93,plain,
    ( k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_4
  <=> k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f330,plain,
    ( ! [X3] :
        ( r2_hidden(sK0,X3)
        | r1_xboole_0(sK1,X3) )
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f109,f323])).

fof(f109,plain,
    ( ! [X0] :
        ( r1_xboole_0(k2_xboole_0(sK1,sK2),X0)
        | r2_hidden(sK0,X0) )
    | ~ spl3_4 ),
    inference(superposition,[],[f68,f93])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f114,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f350,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl3_11
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f351,plain,
    ( ~ spl3_11
    | spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f337,f321,f86,f348])).

fof(f86,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f337,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f331,f163])).

fof(f163,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f159,f60])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f159,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f145,f100])).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f99,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f99,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f72,f49])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f145,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f59,f45])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f331,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f241,f323])).

fof(f241,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f67,f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f324,plain,
    ( spl3_10
    | ~ spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f314,f91,f246,f321])).

fof(f246,plain,
    ( spl3_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f314,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f312,f98])).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f249,plain,
    ( spl3_8
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f242,f91,f81,f246])).

fof(f81,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f242,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f238,f109])).

fof(f238,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(k2_xboole_0(X1,X2),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f212,f48])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k1_xboole_0 = X1
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f42,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f94,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f65,f91])).

fof(f65,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f38,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f89,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (19726)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (19741)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (19733)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (19733)Refutation not found, incomplete strategy% (19733)------------------------------
% 0.21/0.51  % (19733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19733)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19733)Memory used [KB]: 10618
% 0.21/0.51  % (19733)Time elapsed: 0.108 s
% 0.21/0.51  % (19733)------------------------------
% 0.21/0.51  % (19733)------------------------------
% 0.21/0.52  % (19727)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (19717)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (19718)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (19739)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (19724)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (19722)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (19721)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (19745)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (19737)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (19723)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (19719)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (19743)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (19744)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (19720)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (19725)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (19738)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (19731)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (19745)Refutation not found, incomplete strategy% (19745)------------------------------
% 0.21/0.54  % (19745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19727)Refutation not found, incomplete strategy% (19727)------------------------------
% 0.21/0.54  % (19727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19727)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19727)Memory used [KB]: 10746
% 0.21/0.54  % (19727)Time elapsed: 0.136 s
% 0.21/0.54  % (19727)------------------------------
% 0.21/0.54  % (19727)------------------------------
% 0.21/0.54  % (19736)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (19718)Refutation not found, incomplete strategy% (19718)------------------------------
% 0.21/0.54  % (19718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19718)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19718)Memory used [KB]: 1663
% 0.21/0.54  % (19718)Time elapsed: 0.132 s
% 0.21/0.54  % (19718)------------------------------
% 0.21/0.54  % (19718)------------------------------
% 0.21/0.54  % (19730)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (19742)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (19746)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (19746)Refutation not found, incomplete strategy% (19746)------------------------------
% 0.21/0.55  % (19746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19746)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19746)Memory used [KB]: 1663
% 0.21/0.55  % (19746)Time elapsed: 0.138 s
% 0.21/0.55  % (19746)------------------------------
% 0.21/0.55  % (19746)------------------------------
% 0.21/0.55  % (19735)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (19732)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (19734)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (19729)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (19740)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (19734)Refutation not found, incomplete strategy% (19734)------------------------------
% 0.21/0.55  % (19734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19734)Memory used [KB]: 1791
% 0.21/0.55  % (19734)Time elapsed: 0.152 s
% 0.21/0.55  % (19734)------------------------------
% 0.21/0.55  % (19734)------------------------------
% 0.21/0.55  % (19728)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (19745)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19745)Memory used [KB]: 10746
% 0.21/0.56  % (19745)Time elapsed: 0.138 s
% 0.21/0.56  % (19745)------------------------------
% 0.21/0.56  % (19745)------------------------------
% 0.21/0.57  % (19729)Refutation not found, incomplete strategy% (19729)------------------------------
% 0.21/0.57  % (19729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19729)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (19729)Memory used [KB]: 10618
% 0.21/0.57  % (19729)Time elapsed: 0.164 s
% 0.21/0.57  % (19729)------------------------------
% 0.21/0.57  % (19729)------------------------------
% 0.21/0.58  % (19740)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f411,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f249,f324,f351,f374,f410])).
% 0.21/0.59  fof(f410,plain,(
% 0.21/0.59    ~spl3_5 | spl3_1 | ~spl3_10),
% 0.21/0.59    inference(avatar_split_clause,[],[f325,f321,f76,f112])).
% 0.21/0.59  fof(f112,plain,(
% 0.21/0.59    spl3_5 <=> r1_tarski(sK1,sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    spl3_1 <=> sK1 = sK2),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.59  fof(f321,plain,(
% 0.21/0.59    spl3_10 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.59  fof(f325,plain,(
% 0.21/0.59    sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl3_10),
% 0.21/0.59    inference(superposition,[],[f323,f46])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.59  fof(f323,plain,(
% 0.21/0.59    sK1 = k2_xboole_0(sK1,sK2) | ~spl3_10),
% 0.21/0.59    inference(avatar_component_clause,[],[f321])).
% 0.21/0.59  fof(f374,plain,(
% 0.21/0.59    ~spl3_4 | spl3_5 | ~spl3_10 | spl3_11),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f367])).
% 0.21/0.59  fof(f367,plain,(
% 0.21/0.59    $false | (~spl3_4 | spl3_5 | ~spl3_10 | spl3_11)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f350,f114,f366])).
% 0.21/0.59  fof(f366,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | r1_xboole_0(sK1,X0)) ) | (~spl3_4 | ~spl3_10)),
% 0.21/0.59    inference(resolution,[],[f330,f326])).
% 0.21/0.59  fof(f326,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0)) ) | (~spl3_4 | ~spl3_10)),
% 0.21/0.59    inference(superposition,[],[f312,f323])).
% 0.21/0.59  fof(f312,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,sK2),X0) | ~r2_hidden(sK0,X0)) ) | ~spl3_4),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f311])).
% 0.21/0.59  fof(f311,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,sK2),X0) | ~r2_hidden(sK0,X0) | ~r2_hidden(sK0,X0)) ) | ~spl3_4),
% 0.21/0.59    inference(superposition,[],[f69,f93])).
% 0.21/0.59  fof(f93,plain,(
% 0.21/0.59    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f91])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    spl3_4 <=> k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f54,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f61,f62])).
% 0.21/0.59  fof(f62,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f14,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,axiom,(
% 0.21/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.59    inference(flattening,[],[f34])).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.59    inference(nnf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.59  fof(f330,plain,(
% 0.21/0.59    ( ! [X3] : (r2_hidden(sK0,X3) | r1_xboole_0(sK1,X3)) ) | (~spl3_4 | ~spl3_10)),
% 0.21/0.59    inference(superposition,[],[f109,f323])).
% 0.21/0.59  fof(f109,plain,(
% 0.21/0.59    ( ! [X0] : (r1_xboole_0(k2_xboole_0(sK1,sK2),X0) | r2_hidden(sK0,X0)) ) | ~spl3_4),
% 0.21/0.59    inference(superposition,[],[f68,f93])).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f50,f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f51,f63])).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,axiom,(
% 0.21/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,axiom,(
% 0.21/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.59  fof(f114,plain,(
% 0.21/0.59    ~r1_tarski(sK1,sK2) | spl3_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f112])).
% 0.21/0.59  fof(f350,plain,(
% 0.21/0.59    ~r1_xboole_0(sK1,sK2) | spl3_11),
% 0.21/0.59    inference(avatar_component_clause,[],[f348])).
% 0.21/0.59  fof(f348,plain,(
% 0.21/0.59    spl3_11 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.59  fof(f351,plain,(
% 0.21/0.59    ~spl3_11 | spl3_3 | ~spl3_10),
% 0.21/0.59    inference(avatar_split_clause,[],[f337,f321,f86,f348])).
% 0.21/0.59  fof(f86,plain,(
% 0.21/0.59    spl3_3 <=> k1_xboole_0 = sK2),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.59  fof(f337,plain,(
% 0.21/0.59    k1_xboole_0 = sK2 | ~r1_xboole_0(sK1,sK2) | ~spl3_10),
% 0.21/0.59    inference(forward_demodulation,[],[f331,f163])).
% 0.21/0.59  fof(f163,plain,(
% 0.21/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.21/0.59    inference(superposition,[],[f159,f60])).
% 0.21/0.59  fof(f60,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.59  fof(f159,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.59    inference(forward_demodulation,[],[f145,f100])).
% 0.21/0.59  fof(f100,plain,(
% 0.21/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.59    inference(forward_demodulation,[],[f99,f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.59  fof(f99,plain,(
% 0.21/0.59    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 0.21/0.59    inference(forward_demodulation,[],[f72,f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.59    inference(rectify,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.59  fof(f72,plain,(
% 0.21/0.59    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0) )),
% 0.21/0.59    inference(definition_unfolding,[],[f58,f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.59    inference(rectify,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.59  fof(f145,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.59    inference(superposition,[],[f59,f45])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.59  fof(f331,plain,(
% 0.21/0.59    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~r1_xboole_0(sK1,sK2) | ~spl3_10),
% 0.21/0.59    inference(superposition,[],[f241,f323])).
% 0.21/0.59  fof(f241,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f67,f59])).
% 0.21/0.59  fof(f67,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f43,f47])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f33])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(nnf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.59  fof(f324,plain,(
% 0.21/0.59    spl3_10 | ~spl3_8 | ~spl3_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f314,f91,f246,f321])).
% 0.21/0.59  fof(f246,plain,(
% 0.21/0.59    spl3_8 <=> r2_hidden(sK0,sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.59  fof(f314,plain,(
% 0.21/0.59    ~r2_hidden(sK0,sK1) | sK1 = k2_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.59    inference(resolution,[],[f312,f98])).
% 0.21/0.59  fof(f98,plain,(
% 0.21/0.59    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.21/0.59    inference(resolution,[],[f57,f48])).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.59  fof(f57,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(flattening,[],[f36])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.59  fof(f249,plain,(
% 0.21/0.59    spl3_8 | spl3_2 | ~spl3_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f242,f91,f81,f246])).
% 0.21/0.59  fof(f81,plain,(
% 0.21/0.59    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.59  fof(f242,plain,(
% 0.21/0.59    k1_xboole_0 = sK1 | r2_hidden(sK0,sK1) | ~spl3_4),
% 0.21/0.59    inference(resolution,[],[f238,f109])).
% 0.21/0.59  fof(f238,plain,(
% 0.21/0.59    ( ! [X2,X1] : (~r1_xboole_0(k2_xboole_0(X1,X2),X1) | k1_xboole_0 = X1) )),
% 0.21/0.59    inference(resolution,[],[f212,f48])).
% 0.21/0.59  fof(f212,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k1_xboole_0 = X1 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(resolution,[],[f42,f73])).
% 0.21/0.59  fof(f73,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f56])).
% 0.21/0.59  fof(f56,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f37])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(flattening,[],[f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    spl3_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f65,f91])).
% 0.21/0.59  fof(f65,plain,(
% 0.21/0.59    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.59    inference(definition_unfolding,[],[f38,f64])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.59    inference(ennf_transformation,[],[f23])).
% 0.21/0.59  fof(f23,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.59    inference(negated_conjecture,[],[f22])).
% 0.21/0.59  fof(f22,conjecture,(
% 0.21/0.59    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.59  fof(f89,plain,(
% 0.21/0.59    ~spl3_3),
% 0.21/0.59    inference(avatar_split_clause,[],[f41,f86])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    k1_xboole_0 != sK2),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f84,plain,(
% 0.21/0.59    ~spl3_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f40,f81])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    k1_xboole_0 != sK1),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f79,plain,(
% 0.21/0.59    ~spl3_1),
% 0.21/0.59    inference(avatar_split_clause,[],[f39,f76])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    sK1 != sK2),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (19740)------------------------------
% 0.21/0.59  % (19740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (19740)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (19740)Memory used [KB]: 11001
% 0.21/0.59  % (19740)Time elapsed: 0.183 s
% 0.21/0.59  % (19740)------------------------------
% 0.21/0.59  % (19740)------------------------------
% 0.21/0.59  % (19716)Success in time 0.228 s
%------------------------------------------------------------------------------
