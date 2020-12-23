%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 359 expanded)
%              Number of leaves         :   34 ( 133 expanded)
%              Depth                    :    9
%              Number of atoms          :  432 (1089 expanded)
%              Number of equality atoms :  127 ( 485 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f56,f61,f80,f85,f96,f107,f118,f152,f170,f187,f192,f208,f219,f223,f235,f241,f247,f269,f317,f323,f337,f358,f377,f382,f397,f403,f404])).

fof(f404,plain,
    ( spl6_13
    | spl6_31
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl6_13
    | spl6_31
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f376,f128,f396,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f396,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl6_34
  <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f128,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,sK4)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_13
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f376,plain,
    ( ~ r1_tarski(sK3,sK0)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_31
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f403,plain,
    ( spl6_13
    | spl6_25
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl6_13
    | spl6_25
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f240,f128,f396,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f240,plain,
    ( ~ r1_tarski(sK4,sK1)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl6_25
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f397,plain,
    ( spl6_34
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f388,f380,f394])).

fof(f380,plain,
    ( spl6_32
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f388,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_32 ),
    inference(resolution,[],[f381,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f381,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f380])).

fof(f382,plain,
    ( spl6_1
    | spl6_32
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f120,f58,f380,f40])).

fof(f40,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f58,plain,
    ( spl6_5
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) )
    | ~ spl6_5 ),
    inference(superposition,[],[f22,f60])).

fof(f60,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f377,plain,
    ( ~ spl6_31
    | spl6_2
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f353,f266,f45,f374])).

fof(f45,plain,
    ( spl6_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f266,plain,
    ( spl6_28
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f353,plain,
    ( sK0 = sK3
    | ~ r1_tarski(sK3,sK0)
    | ~ spl6_28 ),
    inference(resolution,[],[f268,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f268,plain,
    ( r1_tarski(sK0,sK3)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f266])).

fof(f358,plain,
    ( ~ spl6_8
    | ~ spl6_11
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_11
    | spl6_13 ),
    inference(unit_resulting_resolution,[],[f91,f128,f113,f32])).

fof(f113,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_11
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f91,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_8
  <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f337,plain,
    ( ~ spl6_29
    | spl6_12
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f299,f232,f115,f314])).

fof(f314,plain,
    ( spl6_29
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f115,plain,
    ( spl6_12
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f232,plain,
    ( spl6_24
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f299,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_12
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f274,f36])).

fof(f36,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f274,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK2))
    | spl6_12
    | ~ spl6_24 ),
    inference(superposition,[],[f117,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f117,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f323,plain,(
    spl6_29 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl6_29 ),
    inference(unit_resulting_resolution,[],[f37,f316])).

fof(f316,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f314])).

fof(f317,plain,
    ( ~ spl6_29
    | spl6_9
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f296,f232,f93,f314])).

fof(f93,plain,
    ( spl6_9
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f296,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_9
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f272,f36])).

fof(f272,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),k1_xboole_0)
    | spl6_9
    | ~ spl6_24 ),
    inference(superposition,[],[f95,f234])).

fof(f95,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f269,plain,
    ( spl6_28
    | spl6_24
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f225,f216,f232,f266])).

fof(f216,plain,
    ( spl6_21
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f225,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK0,sK3)
    | ~ spl6_21 ),
    inference(resolution,[],[f218,f22])).

fof(f218,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f247,plain,
    ( spl6_19
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl6_19
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f186,f37,f222])).

fof(f222,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X3,X4))
        | r1_tarski(sK5,X4) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl6_22
  <=> ! [X3,X4] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X3,X4))
        | r1_tarski(sK5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f186,plain,
    ( ~ r1_tarski(sK5,sK2)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_19
  <=> r1_tarski(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f241,plain,
    ( ~ spl6_25
    | spl6_3
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f236,f228,f49,f238])).

fof(f49,plain,
    ( spl6_3
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f228,plain,
    ( spl6_23
  <=> r1_tarski(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f236,plain,
    ( sK1 = sK4
    | ~ r1_tarski(sK4,sK1)
    | ~ spl6_23 ),
    inference(resolution,[],[f230,f32])).

fof(f230,plain,
    ( r1_tarski(sK1,sK4)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f228])).

fof(f235,plain,
    ( spl6_23
    | spl6_24
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f224,f216,f232,f228])).

fof(f224,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK1,sK4)
    | ~ spl6_21 ),
    inference(resolution,[],[f218,f23])).

fof(f223,plain,
    ( spl6_1
    | spl6_22
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f155,f58,f221,f40])).

fof(f155,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X3,X4))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | r1_tarski(sK5,X4) )
    | ~ spl6_5 ),
    inference(superposition,[],[f23,f60])).

fof(f219,plain,
    ( spl6_21
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f211,f58,f40,f216])).

fof(f211,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_5 ),
    inference(resolution,[],[f123,f37])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0
        | r1_tarski(X0,k2_zfmisc_1(sK3,sK4)) )
    | ~ spl6_5 ),
    inference(superposition,[],[f22,f60])).

fof(f208,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f42,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f198,f36])).

fof(f198,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f194,f36])).

fof(f194,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5)
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(superposition,[],[f60,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_16
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f42,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f192,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f42,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f180,f36])).

fof(f180,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f177,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f177,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5)
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(superposition,[],[f60,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_15
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f187,plain,
    ( ~ spl6_19
    | spl6_4
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f171,f167,f53,f184])).

fof(f53,plain,
    ( spl6_4
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f167,plain,
    ( spl6_17
  <=> r1_tarski(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f171,plain,
    ( sK2 = sK5
    | ~ r1_tarski(sK5,sK2)
    | ~ spl6_17 ),
    inference(resolution,[],[f169,f32])).

fof(f169,plain,
    ( r1_tarski(sK2,sK5)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,
    ( spl6_17
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f162,f58,f40,f167])).

fof(f162,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | r1_tarski(sK2,sK5)
    | ~ spl6_5 ),
    inference(resolution,[],[f158,f37])).

fof(f158,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | k1_xboole_0 = k2_zfmisc_1(X3,X4)
        | r1_tarski(X4,sK5) )
    | ~ spl6_5 ),
    inference(superposition,[],[f23,f60])).

fof(f152,plain,
    ( spl6_15
    | spl6_16
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f142,f127,f149,f145])).

fof(f142,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl6_13 ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl6_13 ),
    inference(superposition,[],[f26,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,
    ( spl6_11
    | ~ spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f109,f105,f115,f111])).

fof(f105,plain,
    ( spl6_10
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | r1_tarski(X0,k2_zfmisc_1(sK3,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f109,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4))
    | ~ spl6_10 ),
    inference(superposition,[],[f106,f36])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | r1_tarski(X0,k2_zfmisc_1(sK3,sK4)) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl6_6
    | spl6_10
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f70,f58,f105,f74])).

fof(f74,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | r1_tarski(X0,k2_zfmisc_1(sK3,sK4))
        | k1_xboole_0 = sK5 )
    | ~ spl6_5 ),
    inference(superposition,[],[f24,f60])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f96,plain,
    ( spl6_8
    | ~ spl6_9
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f87,f78,f93,f89])).

fof(f78,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,sK5))
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f87,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_7 ),
    inference(superposition,[],[f79,f36])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,sK5))
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f85,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f42,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f81,f35])).

fof(f81,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(superposition,[],[f60,f76])).

fof(f76,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f80,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f67,f58,f78,f74])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,sK5))
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0)
        | k1_xboole_0 = sK5 )
    | ~ spl6_5 ),
    inference(superposition,[],[f24,f60])).

fof(f61,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f19,f29,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f56,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f21,f53,f49,f45])).

fof(f21,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f33,f40])).

fof(f33,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f20,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (28229)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (28221)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (28213)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (28206)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.55  % (28214)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (28229)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f405,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f43,f56,f61,f80,f85,f96,f107,f118,f152,f170,f187,f192,f208,f219,f223,f235,f241,f247,f269,f317,f323,f337,f358,f377,f382,f397,f403,f404])).
% 0.20/0.56  fof(f404,plain,(
% 0.20/0.56    spl6_13 | spl6_31 | ~spl6_34),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f399])).
% 0.20/0.56  fof(f399,plain,(
% 0.20/0.56    $false | (spl6_13 | spl6_31 | ~spl6_34)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f376,f128,f396,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.56    inference(flattening,[],[f10])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.20/0.56  fof(f396,plain,(
% 0.20/0.56    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1)) | ~spl6_34),
% 0.20/0.56    inference(avatar_component_clause,[],[f394])).
% 0.20/0.56  fof(f394,plain,(
% 0.20/0.56    spl6_34 <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.56  fof(f128,plain,(
% 0.20/0.56    k1_xboole_0 != k2_zfmisc_1(sK3,sK4) | spl6_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f127])).
% 0.20/0.56  fof(f127,plain,(
% 0.20/0.56    spl6_13 <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.56  fof(f376,plain,(
% 0.20/0.56    ~r1_tarski(sK3,sK0) | spl6_31),
% 0.20/0.56    inference(avatar_component_clause,[],[f374])).
% 0.20/0.56  fof(f374,plain,(
% 0.20/0.56    spl6_31 <=> r1_tarski(sK3,sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.56  fof(f403,plain,(
% 0.20/0.56    spl6_13 | spl6_25 | ~spl6_34),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f398])).
% 0.20/0.56  fof(f398,plain,(
% 0.20/0.56    $false | (spl6_13 | spl6_25 | ~spl6_34)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f240,f128,f396,f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X1,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f240,plain,(
% 0.20/0.56    ~r1_tarski(sK4,sK1) | spl6_25),
% 0.20/0.56    inference(avatar_component_clause,[],[f238])).
% 0.20/0.56  fof(f238,plain,(
% 0.20/0.56    spl6_25 <=> r1_tarski(sK4,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.56  fof(f397,plain,(
% 0.20/0.56    spl6_34 | ~spl6_32),
% 0.20/0.56    inference(avatar_split_clause,[],[f388,f380,f394])).
% 0.20/0.56  fof(f380,plain,(
% 0.20/0.56    spl6_32 <=> ! [X1,X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.56  fof(f388,plain,(
% 0.20/0.56    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1)) | ~spl6_32),
% 0.20/0.56    inference(resolution,[],[f381,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(flattening,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f381,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0)) ) | ~spl6_32),
% 0.20/0.56    inference(avatar_component_clause,[],[f380])).
% 0.20/0.56  fof(f382,plain,(
% 0.20/0.56    spl6_1 | spl6_32 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f120,f58,f380,f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    spl6_5 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0)) ) | ~spl6_5),
% 0.20/0.56    inference(superposition,[],[f22,f60])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) | ~spl6_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f58])).
% 0.20/0.56  fof(f377,plain,(
% 0.20/0.56    ~spl6_31 | spl6_2 | ~spl6_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f353,f266,f45,f374])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    spl6_2 <=> sK0 = sK3),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.56  fof(f266,plain,(
% 0.20/0.56    spl6_28 <=> r1_tarski(sK0,sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.56  fof(f353,plain,(
% 0.20/0.56    sK0 = sK3 | ~r1_tarski(sK3,sK0) | ~spl6_28),
% 0.20/0.56    inference(resolution,[],[f268,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f268,plain,(
% 0.20/0.56    r1_tarski(sK0,sK3) | ~spl6_28),
% 0.20/0.56    inference(avatar_component_clause,[],[f266])).
% 0.20/0.56  fof(f358,plain,(
% 0.20/0.56    ~spl6_8 | ~spl6_11 | spl6_13),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f355])).
% 0.20/0.56  fof(f355,plain,(
% 0.20/0.56    $false | (~spl6_8 | ~spl6_11 | spl6_13)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f91,f128,f113,f32])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) | ~spl6_11),
% 0.20/0.56    inference(avatar_component_clause,[],[f111])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    spl6_11 <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0) | ~spl6_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f89])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    spl6_8 <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.56  fof(f337,plain,(
% 0.20/0.56    ~spl6_29 | spl6_12 | ~spl6_24),
% 0.20/0.56    inference(avatar_split_clause,[],[f299,f232,f115,f314])).
% 0.20/0.56  fof(f314,plain,(
% 0.20/0.56    spl6_29 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.56  fof(f115,plain,(
% 0.20/0.56    spl6_12 <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    spl6_24 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.56  fof(f299,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl6_12 | ~spl6_24)),
% 0.20/0.56    inference(forward_demodulation,[],[f274,f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.56    inference(flattening,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.56    inference(nnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.56  fof(f274,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK2)) | (spl6_12 | ~spl6_24)),
% 0.20/0.56    inference(superposition,[],[f117,f234])).
% 0.20/0.56  fof(f234,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_24),
% 0.20/0.56    inference(avatar_component_clause,[],[f232])).
% 0.20/0.56  fof(f117,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl6_12),
% 0.20/0.56    inference(avatar_component_clause,[],[f115])).
% 0.20/0.56  fof(f323,plain,(
% 0.20/0.56    spl6_29),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f318])).
% 0.20/0.56  fof(f318,plain,(
% 0.20/0.56    $false | spl6_29),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f37,f316])).
% 0.20/0.56  fof(f316,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_29),
% 0.20/0.56    inference(avatar_component_clause,[],[f314])).
% 0.20/0.56  fof(f317,plain,(
% 0.20/0.56    ~spl6_29 | spl6_9 | ~spl6_24),
% 0.20/0.56    inference(avatar_split_clause,[],[f296,f232,f93,f314])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    spl6_9 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.56  fof(f296,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl6_9 | ~spl6_24)),
% 0.20/0.56    inference(forward_demodulation,[],[f272,f36])).
% 0.20/0.56  fof(f272,plain,(
% 0.20/0.56    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),k1_xboole_0) | (spl6_9 | ~spl6_24)),
% 0.20/0.56    inference(superposition,[],[f95,f234])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | spl6_9),
% 0.20/0.56    inference(avatar_component_clause,[],[f93])).
% 0.20/0.56  fof(f269,plain,(
% 0.20/0.56    spl6_28 | spl6_24 | ~spl6_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f225,f216,f232,f266])).
% 0.20/0.56  fof(f216,plain,(
% 0.20/0.56    spl6_21 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.56  fof(f225,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK0,sK3) | ~spl6_21),
% 0.20/0.56    inference(resolution,[],[f218,f22])).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_21),
% 0.20/0.56    inference(avatar_component_clause,[],[f216])).
% 0.20/0.56  fof(f247,plain,(
% 0.20/0.56    spl6_19 | ~spl6_22),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f242])).
% 0.20/0.56  fof(f242,plain,(
% 0.20/0.56    $false | (spl6_19 | ~spl6_22)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f186,f37,f222])).
% 0.20/0.56  fof(f222,plain,(
% 0.20/0.56    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X3,X4)) | r1_tarski(sK5,X4)) ) | ~spl6_22),
% 0.20/0.56    inference(avatar_component_clause,[],[f221])).
% 0.20/0.56  fof(f221,plain,(
% 0.20/0.56    spl6_22 <=> ! [X3,X4] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X3,X4)) | r1_tarski(sK5,X4))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.56  fof(f186,plain,(
% 0.20/0.56    ~r1_tarski(sK5,sK2) | spl6_19),
% 0.20/0.56    inference(avatar_component_clause,[],[f184])).
% 0.20/0.56  fof(f184,plain,(
% 0.20/0.56    spl6_19 <=> r1_tarski(sK5,sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.56  fof(f241,plain,(
% 0.20/0.56    ~spl6_25 | spl6_3 | ~spl6_23),
% 0.20/0.56    inference(avatar_split_clause,[],[f236,f228,f49,f238])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    spl6_3 <=> sK1 = sK4),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.56  fof(f228,plain,(
% 0.20/0.56    spl6_23 <=> r1_tarski(sK1,sK4)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    sK1 = sK4 | ~r1_tarski(sK4,sK1) | ~spl6_23),
% 0.20/0.56    inference(resolution,[],[f230,f32])).
% 0.20/0.56  fof(f230,plain,(
% 0.20/0.56    r1_tarski(sK1,sK4) | ~spl6_23),
% 0.20/0.56    inference(avatar_component_clause,[],[f228])).
% 0.20/0.56  fof(f235,plain,(
% 0.20/0.56    spl6_23 | spl6_24 | ~spl6_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f224,f216,f232,f228])).
% 0.20/0.56  fof(f224,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK1,sK4) | ~spl6_21),
% 0.20/0.56    inference(resolution,[],[f218,f23])).
% 0.20/0.56  fof(f223,plain,(
% 0.20/0.56    spl6_1 | spl6_22 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f155,f58,f221,f40])).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X3,X4)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(sK5,X4)) ) | ~spl6_5),
% 0.20/0.56    inference(superposition,[],[f23,f60])).
% 0.20/0.56  fof(f219,plain,(
% 0.20/0.56    spl6_21 | spl6_1 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f211,f58,f40,f216])).
% 0.20/0.56  fof(f211,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_5),
% 0.20/0.56    inference(resolution,[],[f123,f37])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,k2_zfmisc_1(sK3,sK4))) ) | ~spl6_5),
% 0.20/0.56    inference(superposition,[],[f22,f60])).
% 0.20/0.56  fof(f208,plain,(
% 0.20/0.56    spl6_1 | ~spl6_5 | ~spl6_16),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f206])).
% 0.20/0.56  fof(f206,plain,(
% 0.20/0.56    $false | (spl6_1 | ~spl6_5 | ~spl6_16)),
% 0.20/0.56    inference(subsumption_resolution,[],[f42,f199])).
% 0.20/0.56  fof(f199,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl6_5 | ~spl6_16)),
% 0.20/0.56    inference(forward_demodulation,[],[f198,f36])).
% 0.20/0.56  fof(f198,plain,(
% 0.20/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) | (~spl6_5 | ~spl6_16)),
% 0.20/0.56    inference(forward_demodulation,[],[f194,f36])).
% 0.20/0.56  fof(f194,plain,(
% 0.20/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5) | (~spl6_5 | ~spl6_16)),
% 0.20/0.56    inference(superposition,[],[f60,f151])).
% 0.20/0.56  fof(f151,plain,(
% 0.20/0.56    k1_xboole_0 = sK3 | ~spl6_16),
% 0.20/0.56    inference(avatar_component_clause,[],[f149])).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    spl6_16 <=> k1_xboole_0 = sK3),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | spl6_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f40])).
% 0.20/0.56  fof(f192,plain,(
% 0.20/0.56    spl6_1 | ~spl6_5 | ~spl6_15),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f190])).
% 0.20/0.56  fof(f190,plain,(
% 0.20/0.56    $false | (spl6_1 | ~spl6_5 | ~spl6_15)),
% 0.20/0.56    inference(subsumption_resolution,[],[f42,f181])).
% 0.20/0.56  fof(f181,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl6_5 | ~spl6_15)),
% 0.20/0.56    inference(forward_demodulation,[],[f180,f36])).
% 0.20/0.56  fof(f180,plain,(
% 0.20/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) | (~spl6_5 | ~spl6_15)),
% 0.20/0.56    inference(forward_demodulation,[],[f177,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f177,plain,(
% 0.20/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5) | (~spl6_5 | ~spl6_15)),
% 0.20/0.56    inference(superposition,[],[f60,f147])).
% 0.20/0.56  fof(f147,plain,(
% 0.20/0.56    k1_xboole_0 = sK4 | ~spl6_15),
% 0.20/0.56    inference(avatar_component_clause,[],[f145])).
% 0.20/0.56  fof(f145,plain,(
% 0.20/0.56    spl6_15 <=> k1_xboole_0 = sK4),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.56  fof(f187,plain,(
% 0.20/0.56    ~spl6_19 | spl6_4 | ~spl6_17),
% 0.20/0.56    inference(avatar_split_clause,[],[f171,f167,f53,f184])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    spl6_4 <=> sK2 = sK5),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    spl6_17 <=> r1_tarski(sK2,sK5)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.56  fof(f171,plain,(
% 0.20/0.56    sK2 = sK5 | ~r1_tarski(sK5,sK2) | ~spl6_17),
% 0.20/0.56    inference(resolution,[],[f169,f32])).
% 0.20/0.56  fof(f169,plain,(
% 0.20/0.56    r1_tarski(sK2,sK5) | ~spl6_17),
% 0.20/0.56    inference(avatar_component_clause,[],[f167])).
% 0.20/0.56  fof(f170,plain,(
% 0.20/0.56    spl6_17 | spl6_1 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f162,f58,f40,f167])).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(sK2,sK5) | ~spl6_5),
% 0.20/0.56    inference(resolution,[],[f158,f37])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(X3,X4) | r1_tarski(X4,sK5)) ) | ~spl6_5),
% 0.20/0.56    inference(superposition,[],[f23,f60])).
% 0.20/0.56  fof(f152,plain,(
% 0.20/0.56    spl6_15 | spl6_16 | ~spl6_13),
% 0.20/0.56    inference(avatar_split_clause,[],[f142,f127,f149,f145])).
% 0.20/0.56  fof(f142,plain,(
% 0.20/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl6_13),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f141])).
% 0.20/0.56  fof(f141,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl6_13),
% 0.20/0.56    inference(superposition,[],[f26,f129])).
% 0.20/0.56  fof(f129,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl6_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f127])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f118,plain,(
% 0.20/0.56    spl6_11 | ~spl6_12 | ~spl6_10),
% 0.20/0.56    inference(avatar_split_clause,[],[f109,f105,f115,f111])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    spl6_10 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r1_tarski(X0,k2_zfmisc_1(sK3,sK4)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) | ~spl6_10),
% 0.20/0.56    inference(superposition,[],[f106,f36])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r1_tarski(X0,k2_zfmisc_1(sK3,sK4))) ) | ~spl6_10),
% 0.20/0.56    inference(avatar_component_clause,[],[f105])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    spl6_6 | spl6_10 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f70,f58,f105,f74])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    spl6_6 <=> k1_xboole_0 = sK5),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r1_tarski(X0,k2_zfmisc_1(sK3,sK4)) | k1_xboole_0 = sK5) ) | ~spl6_5),
% 0.20/0.56    inference(superposition,[],[f24,f60])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    spl6_8 | ~spl6_9 | ~spl6_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f87,f78,f93,f89])).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    spl6_7 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,sK5)) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0) | ~spl6_7),
% 0.20/0.56    inference(superposition,[],[f79,f36])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,sK5)) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0)) ) | ~spl6_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f78])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    spl6_1 | ~spl6_5 | ~spl6_6),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f83])).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    $false | (spl6_1 | ~spl6_5 | ~spl6_6)),
% 0.20/0.56    inference(subsumption_resolution,[],[f42,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl6_5 | ~spl6_6)),
% 0.20/0.56    inference(forward_demodulation,[],[f81,f35])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0) | (~spl6_5 | ~spl6_6)),
% 0.20/0.56    inference(superposition,[],[f60,f76])).
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    k1_xboole_0 = sK5 | ~spl6_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f74])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    spl6_6 | spl6_7 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f67,f58,f78,f74])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,sK5)) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) | k1_xboole_0 = sK5) ) | ~spl6_5),
% 0.20/0.56    inference(superposition,[],[f24,f60])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f34,f58])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.20/0.56    inference(definition_unfolding,[],[f19,f29,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f13])).
% 1.50/0.56  fof(f13,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f9,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.50/0.56    inference(flattening,[],[f8])).
% 1.50/0.56  fof(f8,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.50/0.56    inference(ennf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.50/0.56    inference(negated_conjecture,[],[f6])).
% 1.50/0.56  fof(f6,conjecture,(
% 1.50/0.56    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    ~spl6_2 | ~spl6_3 | ~spl6_4),
% 1.50/0.56    inference(avatar_split_clause,[],[f21,f53,f49,f45])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ~spl6_1),
% 1.50/0.56    inference(avatar_split_clause,[],[f33,f40])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.50/0.56    inference(definition_unfolding,[],[f20,f29])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (28229)------------------------------
% 1.50/0.56  % (28229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (28229)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (28229)Memory used [KB]: 10874
% 1.50/0.56  % (28229)Time elapsed: 0.095 s
% 1.50/0.56  % (28229)------------------------------
% 1.50/0.56  % (28229)------------------------------
% 1.50/0.56  % (28211)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.57  % (28205)Success in time 0.21 s
%------------------------------------------------------------------------------
