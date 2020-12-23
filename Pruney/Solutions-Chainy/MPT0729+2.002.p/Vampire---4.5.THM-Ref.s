%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:10 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 328 expanded)
%              Number of leaves         :   26 ( 118 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 482 expanded)
%              Number of equality atoms :   49 ( 262 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30311)Termination reason: Refutation not found, incomplete strategy

% (30311)Memory used [KB]: 10618
% (30311)Time elapsed: 0.148 s
% (30311)------------------------------
% (30311)------------------------------
fof(f530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f171,f181,f201,f215,f453,f488,f517,f529])).

fof(f529,plain,(
    ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f86,f487,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f487,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f485])).

fof(f485,plain,
    ( spl3_38
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f517,plain,(
    ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl3_37 ),
    inference(unit_resulting_resolution,[],[f70,f90,f483,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f483,plain,
    ( ! [X2] : ~ r2_hidden(sK0,X2)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl3_37
  <=> ! [X2] : ~ r2_hidden(sK0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f90,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f70,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f30,f68])).

fof(f68,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f33,f66,f67])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f65])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f30,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f488,plain,
    ( spl3_37
    | spl3_38
    | ~ spl3_9
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f471,f451,f169,f485,f482])).

fof(f169,plain,
    ( spl3_9
  <=> ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f451,plain,
    ( spl3_36
  <=> ! [X2] :
        ( r2_hidden(sK1,X2)
        | ~ r2_hidden(sK0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f471,plain,
    ( ! [X2] :
        ( r2_hidden(sK0,sK0)
        | ~ r2_hidden(sK0,X2) )
    | ~ spl3_9
    | ~ spl3_36 ),
    inference(resolution,[],[f455,f87])).

fof(f455,plain,
    ( ! [X1] : ~ r2_hidden(sK0,k4_xboole_0(X1,sK0))
    | ~ spl3_9
    | ~ spl3_36 ),
    inference(resolution,[],[f452,f170])).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f452,plain,
    ( ! [X2] :
        ( r2_hidden(sK1,X2)
        | ~ r2_hidden(sK0,X2) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f451])).

fof(f453,plain,
    ( spl3_12
    | spl3_36
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f432,f97,f451,f212])).

fof(f212,plain,
    ( spl3_12
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f97,plain,
    ( spl3_2
  <=> k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f432,plain,
    ( ! [X2] :
        ( r2_hidden(sK1,X2)
        | r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,X2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f426,f87])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k4_xboole_0(X0,sK1))
        | r2_hidden(sK1,X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f416,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f416,plain,
    ( ! [X5] :
        ( r2_hidden(sK1,k4_xboole_0(X5,sK1))
        | ~ r2_hidden(sK0,k4_xboole_0(X5,sK1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f90,f126])).

% (30316)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f126,plain,
    ( ! [X1] :
        ( k4_xboole_0(X1,sK1) = k4_xboole_0(k4_xboole_0(X1,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(sK1,k4_xboole_0(X1,sK1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f105,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f105,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(X1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k4_xboole_0(X1,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f103,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f103,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(X1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(X1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_2 ),
    inference(superposition,[],[f77,f99])).

fof(f99,plain,
    ( k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f215,plain,
    ( ~ spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f210,f178,f212])).

fof(f178,plain,
    ( spl3_11
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f210,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl3_11 ),
    inference(resolution,[],[f180,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f180,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f201,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f72,f176,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f176,plain,
    ( ! [X0] : ~ r2_hidden(sK1,X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_10
  <=> ! [X0] : ~ r2_hidden(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f66])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f181,plain,
    ( spl3_10
    | spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f172,f169,f178,f175])).

fof(f172,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,sK0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f170,f87])).

fof(f171,plain,
    ( spl3_9
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f158,f97,f92,f169])).

fof(f92,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f158,plain,
    ( ! [X0] :
        ( sK0 = sK1
        | ~ r2_hidden(sK1,k4_xboole_0(X0,sK0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f129,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f129,plain,
    ( ! [X2] : ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(X2,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f90,f105])).

fof(f100,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f69,f97])).

fof(f69,plain,(
    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f28,f68,f68])).

fof(f28,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f95,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f92])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:37:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (30299)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (30298)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (30318)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (30320)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (30302)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (30306)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (30297)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (30307)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (30308)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.26/0.52  % (30305)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.52  % (30310)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.53  % (30324)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.53  % (30295)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.26/0.53  % (30317)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.53  % (30309)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.53  % (30321)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.26/0.53  % (30315)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.26/0.53  % (30323)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.26/0.53  % (30300)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.53  % (30301)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.54  % (30322)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.54  % (30314)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.54  % (30312)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.54  % (30303)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.54  % (30304)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.54  % (30296)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.54  % (30323)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.55  % (30313)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.55  % (30319)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.44/0.55  % (30311)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.55  % (30311)Refutation not found, incomplete strategy% (30311)------------------------------
% 1.44/0.55  % (30311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  % (30311)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (30311)Memory used [KB]: 10618
% 1.44/0.55  % (30311)Time elapsed: 0.148 s
% 1.44/0.55  % (30311)------------------------------
% 1.44/0.55  % (30311)------------------------------
% 1.44/0.55  fof(f530,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f95,f100,f171,f181,f201,f215,f453,f488,f517,f529])).
% 1.44/0.55  fof(f529,plain,(
% 1.44/0.55    ~spl3_38),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f523])).
% 1.44/0.55  fof(f523,plain,(
% 1.44/0.55    $false | ~spl3_38),
% 1.44/0.55    inference(unit_resulting_resolution,[],[f86,f487,f47])).
% 1.44/0.55  fof(f47,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f26])).
% 1.44/0.55  fof(f26,plain,(
% 1.44/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f21])).
% 1.44/0.55  fof(f21,axiom,(
% 1.44/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.44/0.55  fof(f487,plain,(
% 1.44/0.55    r2_hidden(sK0,sK0) | ~spl3_38),
% 1.44/0.55    inference(avatar_component_clause,[],[f485])).
% 1.44/0.55  fof(f485,plain,(
% 1.44/0.55    spl3_38 <=> r2_hidden(sK0,sK0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.44/0.55  fof(f86,plain,(
% 1.44/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.55    inference(equality_resolution,[],[f40])).
% 1.44/0.55  fof(f40,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.55  fof(f517,plain,(
% 1.44/0.55    ~spl3_37),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f497])).
% 1.44/0.55  fof(f497,plain,(
% 1.44/0.55    $false | ~spl3_37),
% 1.44/0.55    inference(unit_resulting_resolution,[],[f70,f90,f483,f87])).
% 1.44/0.55  fof(f87,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f56])).
% 1.44/0.55  fof(f56,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.44/0.55  fof(f483,plain,(
% 1.44/0.55    ( ! [X2] : (~r2_hidden(sK0,X2)) ) | ~spl3_37),
% 1.44/0.55    inference(avatar_component_clause,[],[f482])).
% 1.44/0.55  fof(f482,plain,(
% 1.44/0.55    spl3_37 <=> ! [X2] : ~r2_hidden(sK0,X2)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.44/0.55  fof(f90,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) )),
% 1.44/0.55    inference(equality_resolution,[],[f83])).
% 1.44/0.55  fof(f83,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f61,f67])).
% 1.44/0.55  fof(f67,plain,(
% 1.44/0.55    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f32,f65])).
% 1.44/0.55  fof(f65,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f36,f64])).
% 1.44/0.55  fof(f64,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f48,f63])).
% 1.44/0.55  fof(f63,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f14])).
% 1.44/0.55  fof(f14,axiom,(
% 1.44/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.44/0.55  fof(f48,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f13])).
% 1.44/0.55  fof(f13,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f12])).
% 1.44/0.55  fof(f12,axiom,(
% 1.44/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f11])).
% 1.44/0.55  fof(f11,axiom,(
% 1.44/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.55  fof(f61,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f17])).
% 1.44/0.55  fof(f17,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.44/0.55  fof(f70,plain,(
% 1.44/0.55    ( ! [X0] : (r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f30,f68])).
% 1.44/0.55  fof(f68,plain,(
% 1.44/0.55    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f33,f66,f67])).
% 1.44/0.55  fof(f66,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f37,f65])).
% 1.44/0.55  fof(f37,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f15])).
% 1.44/0.55  fof(f15,axiom,(
% 1.44/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f19])).
% 1.44/0.55  fof(f19,axiom,(
% 1.44/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.44/0.55  fof(f30,plain,(
% 1.44/0.55    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f20])).
% 1.44/0.55  fof(f20,axiom,(
% 1.44/0.55    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.44/0.55  fof(f488,plain,(
% 1.44/0.55    spl3_37 | spl3_38 | ~spl3_9 | ~spl3_36),
% 1.44/0.55    inference(avatar_split_clause,[],[f471,f451,f169,f485,f482])).
% 1.44/0.55  fof(f169,plain,(
% 1.44/0.55    spl3_9 <=> ! [X0] : ~r2_hidden(sK1,k4_xboole_0(X0,sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.44/0.55  fof(f451,plain,(
% 1.44/0.55    spl3_36 <=> ! [X2] : (r2_hidden(sK1,X2) | ~r2_hidden(sK0,X2))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.44/0.55  fof(f471,plain,(
% 1.44/0.55    ( ! [X2] : (r2_hidden(sK0,sK0) | ~r2_hidden(sK0,X2)) ) | (~spl3_9 | ~spl3_36)),
% 1.44/0.55    inference(resolution,[],[f455,f87])).
% 1.44/0.55  fof(f455,plain,(
% 1.44/0.55    ( ! [X1] : (~r2_hidden(sK0,k4_xboole_0(X1,sK0))) ) | (~spl3_9 | ~spl3_36)),
% 1.44/0.55    inference(resolution,[],[f452,f170])).
% 1.44/0.55  fof(f170,plain,(
% 1.44/0.55    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK0))) ) | ~spl3_9),
% 1.44/0.55    inference(avatar_component_clause,[],[f169])).
% 1.44/0.55  fof(f452,plain,(
% 1.44/0.55    ( ! [X2] : (r2_hidden(sK1,X2) | ~r2_hidden(sK0,X2)) ) | ~spl3_36),
% 1.44/0.55    inference(avatar_component_clause,[],[f451])).
% 1.44/0.55  fof(f453,plain,(
% 1.44/0.55    spl3_12 | spl3_36 | ~spl3_2),
% 1.44/0.55    inference(avatar_split_clause,[],[f432,f97,f451,f212])).
% 1.44/0.55  fof(f212,plain,(
% 1.44/0.55    spl3_12 <=> r2_hidden(sK0,sK1)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.44/0.55  fof(f97,plain,(
% 1.44/0.55    spl3_2 <=> k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.55  fof(f432,plain,(
% 1.44/0.55    ( ! [X2] : (r2_hidden(sK1,X2) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,X2)) ) | ~spl3_2),
% 1.44/0.55    inference(resolution,[],[f426,f87])).
% 1.44/0.55  fof(f426,plain,(
% 1.44/0.55    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1)) | r2_hidden(sK1,X0)) ) | ~spl3_2),
% 1.44/0.55    inference(resolution,[],[f416,f89])).
% 1.44/0.55  fof(f89,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f54])).
% 1.44/0.55  fof(f54,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f416,plain,(
% 1.44/0.55    ( ! [X5] : (r2_hidden(sK1,k4_xboole_0(X5,sK1)) | ~r2_hidden(sK0,k4_xboole_0(X5,sK1))) ) | ~spl3_2),
% 1.44/0.55    inference(superposition,[],[f90,f126])).
% 1.44/0.55  % (30316)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.55  fof(f126,plain,(
% 1.44/0.55    ( ! [X1] : (k4_xboole_0(X1,sK1) = k4_xboole_0(k4_xboole_0(X1,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK1,k4_xboole_0(X1,sK1))) ) | ~spl3_2),
% 1.44/0.55    inference(superposition,[],[f105,f76])).
% 1.44/0.55  fof(f76,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f45,f67])).
% 1.44/0.55  fof(f45,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,axiom,(
% 1.44/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.44/0.55  fof(f105,plain,(
% 1.44/0.55    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k4_xboole_0(X1,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ) | ~spl3_2),
% 1.44/0.55    inference(forward_demodulation,[],[f103,f77])).
% 1.44/0.55  fof(f77,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f49,f66])).
% 1.44/0.55  fof(f49,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f7])).
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.44/0.55  fof(f103,plain,(
% 1.44/0.55    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(X1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) ) | ~spl3_2),
% 1.44/0.55    inference(superposition,[],[f77,f99])).
% 1.44/0.55  fof(f99,plain,(
% 1.44/0.55    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl3_2),
% 1.44/0.55    inference(avatar_component_clause,[],[f97])).
% 1.44/0.55  fof(f215,plain,(
% 1.44/0.55    ~spl3_12 | ~spl3_11),
% 1.44/0.55    inference(avatar_split_clause,[],[f210,f178,f212])).
% 1.44/0.55  fof(f178,plain,(
% 1.44/0.55    spl3_11 <=> r2_hidden(sK1,sK0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.44/0.55  fof(f210,plain,(
% 1.44/0.55    ~r2_hidden(sK0,sK1) | ~spl3_11),
% 1.44/0.55    inference(resolution,[],[f180,f39])).
% 1.44/0.55  fof(f39,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f25])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.44/0.55  fof(f180,plain,(
% 1.44/0.55    r2_hidden(sK1,sK0) | ~spl3_11),
% 1.44/0.55    inference(avatar_component_clause,[],[f178])).
% 1.44/0.55  fof(f201,plain,(
% 1.44/0.55    ~spl3_10),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f184])).
% 1.44/0.55  fof(f184,plain,(
% 1.44/0.55    $false | ~spl3_10),
% 1.44/0.55    inference(unit_resulting_resolution,[],[f72,f176,f80])).
% 1.44/0.55  fof(f80,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f58,f65])).
% 1.44/0.55  fof(f58,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f16])).
% 1.44/0.55  fof(f16,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.44/0.55  fof(f176,plain,(
% 1.44/0.55    ( ! [X0] : (~r2_hidden(sK1,X0)) ) | ~spl3_10),
% 1.44/0.55    inference(avatar_component_clause,[],[f175])).
% 1.44/0.55  fof(f175,plain,(
% 1.44/0.55    spl3_10 <=> ! [X0] : ~r2_hidden(sK1,X0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.44/0.55  fof(f72,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f34,f66])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,axiom,(
% 1.44/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.44/0.55  fof(f181,plain,(
% 1.44/0.55    spl3_10 | spl3_11 | ~spl3_9),
% 1.44/0.55    inference(avatar_split_clause,[],[f172,f169,f178,f175])).
% 1.44/0.55  fof(f172,plain,(
% 1.44/0.55    ( ! [X0] : (r2_hidden(sK1,sK0) | ~r2_hidden(sK1,X0)) ) | ~spl3_9),
% 1.44/0.55    inference(resolution,[],[f170,f87])).
% 1.44/0.55  fof(f171,plain,(
% 1.44/0.55    spl3_9 | spl3_1 | ~spl3_2),
% 1.44/0.55    inference(avatar_split_clause,[],[f158,f97,f92,f169])).
% 1.44/0.55  fof(f92,plain,(
% 1.44/0.55    spl3_1 <=> sK0 = sK1),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.55  fof(f158,plain,(
% 1.44/0.55    ( ! [X0] : (sK0 = sK1 | ~r2_hidden(sK1,k4_xboole_0(X0,sK0))) ) | ~spl3_2),
% 1.44/0.55    inference(resolution,[],[f129,f82])).
% 1.44/0.55  fof(f82,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f62,f67])).
% 1.44/0.55  fof(f62,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f17])).
% 1.44/0.55  fof(f129,plain,(
% 1.44/0.55    ( ! [X2] : (~r2_hidden(sK1,k4_xboole_0(k4_xboole_0(X2,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ) | ~spl3_2),
% 1.44/0.55    inference(superposition,[],[f90,f105])).
% 1.44/0.55  fof(f100,plain,(
% 1.44/0.55    spl3_2),
% 1.44/0.55    inference(avatar_split_clause,[],[f69,f97])).
% 1.44/0.55  fof(f69,plain,(
% 1.44/0.55    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.44/0.55    inference(definition_unfolding,[],[f28,f68,f68])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f23])).
% 1.44/0.55  fof(f23,negated_conjecture,(
% 1.44/0.55    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.44/0.55    inference(negated_conjecture,[],[f22])).
% 1.44/0.55  fof(f22,conjecture,(
% 1.44/0.55    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).
% 1.44/0.55  fof(f95,plain,(
% 1.44/0.55    ~spl3_1),
% 1.44/0.55    inference(avatar_split_clause,[],[f29,f92])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    sK0 != sK1),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (30323)------------------------------
% 1.44/0.55  % (30323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (30323)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (30323)Memory used [KB]: 11129
% 1.44/0.55  % (30323)Time elapsed: 0.140 s
% 1.44/0.55  % (30323)------------------------------
% 1.44/0.55  % (30323)------------------------------
% 1.44/0.56  % (30294)Success in time 0.201 s
%------------------------------------------------------------------------------
