%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 149 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :    5
%              Number of atoms          :  267 ( 417 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f53,f69,f81,f87,f93,f97,f104,f109,f115,f127,f142,f156,f160,f174,f186,f194])).

fof(f194,plain,
    ( spl6_25
    | spl6_24
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f193,f184,f85,f151,f154])).

fof(f154,plain,
    ( spl6_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f151,plain,
    ( spl6_24
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f85,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f184,plain,
    ( spl6_26
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(superposition,[],[f86,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f184])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f85])).

fof(f186,plain,
    ( spl6_26
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f177,f113,f48,f184])).

fof(f48,plain,
    ( spl6_5
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f113,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k2_zfmisc_1(sK1,X0)
        | ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f177,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(resolution,[],[f114,f49])).

fof(f49,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1))
        | k1_xboole_0 = k2_zfmisc_1(sK1,X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f113])).

fof(f174,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f161,f45])).

fof(f45,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f161,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl6_2
    | ~ spl6_25 ),
    inference(backward_demodulation,[],[f37,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f154])).

fof(f37,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl6_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f160,plain,
    ( spl6_1
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl6_1
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f158,f108])).

fof(f108,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f158,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_1
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f33,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f151])).

fof(f33,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f156,plain,
    ( spl6_24
    | spl6_25
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f145,f140,f85,f154,f151])).

fof(f140,plain,
    ( spl6_22
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f145,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(superposition,[],[f86,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( spl6_22
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f133,f125,f51,f140])).

fof(f51,plain,
    ( spl6_6
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f125,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,sK1)
        | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f133,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(resolution,[],[f126,f52])).

fof(f52,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
        | k1_xboole_0 = k2_zfmisc_1(X0,sK1) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl6_21
    | spl6_2
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f110,f102,f36,f125])).

fof(f102,plain,
    ( spl6_17
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | r1_tarski(X1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,sK1)
        | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) )
    | spl6_2
    | ~ spl6_17 ),
    inference(resolution,[],[f103,f37])).

fof(f103,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(X1,X3)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f102])).

fof(f115,plain,
    ( spl6_19
    | spl6_2
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f105,f95,f36,f113])).

fof(f95,plain,
    ( spl6_16
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(sK1,X0)
        | ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) )
    | spl6_2
    | ~ spl6_16 ),
    inference(resolution,[],[f96,f37])).

fof(f96,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(X0,X2)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f95])).

fof(f109,plain,
    ( spl6_18
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f98,f91,f67,f107])).

fof(f67,plain,
    ( spl6_10
  <=> ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f91,plain,
    ( spl6_15
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f98,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(resolution,[],[f92,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f91])).

fof(f104,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f28,f102])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f97,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f27,f95])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f83,f79,f40,f91])).

fof(f40,plain,
    ( spl6_3
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f79,plain,
    ( spl6_13
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f83,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(condensation,[],[f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f80,f41])).

fof(f41,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f79])).

fof(f87,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f24,f85])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f81,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f21,f79])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f69,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f19,f67])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f53,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f14,f51,f48])).

fof(f14,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f46,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f42,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f38,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:51:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3681)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (3680)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (3681)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f53,f69,f81,f87,f93,f97,f104,f109,f115,f127,f142,f156,f160,f174,f186,f194])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    spl6_25 | spl6_24 | ~spl6_14 | ~spl6_26),
% 0.22/0.48    inference(avatar_split_clause,[],[f193,f184,f85,f151,f154])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    spl6_25 <=> k1_xboole_0 = sK1),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    spl6_24 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl6_14 <=> ! [X1,X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    spl6_26 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl6_14 | ~spl6_26)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f192])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl6_14 | ~spl6_26)),
% 0.22/0.48    inference(superposition,[],[f86,f185])).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl6_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f184])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl6_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f85])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    spl6_26 | ~spl6_5 | ~spl6_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f177,f113,f48,f184])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl6_5 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    spl6_19 <=> ! [X1,X0] : (k1_xboole_0 = k2_zfmisc_1(sK1,X0) | ~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | (~spl6_5 | ~spl6_19)),
% 0.22/0.48    inference(resolution,[],[f114,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl6_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) | k1_xboole_0 = k2_zfmisc_1(sK1,X0)) ) | ~spl6_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f113])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    spl6_2 | ~spl6_4 | ~spl6_25),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    $false | (spl6_2 | ~spl6_4 | ~spl6_25)),
% 0.22/0.48    inference(subsumption_resolution,[],[f161,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl6_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ~r1_tarski(k1_xboole_0,sK3) | (spl6_2 | ~spl6_25)),
% 0.22/0.48    inference(backward_demodulation,[],[f37,f155])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | ~spl6_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f154])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK3) | spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl6_2 <=> r1_tarski(sK1,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    spl6_1 | ~spl6_18 | ~spl6_24),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f159])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    $false | (spl6_1 | ~spl6_18 | ~spl6_24)),
% 0.22/0.48    inference(subsumption_resolution,[],[f158,f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | ~spl6_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f107])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl6_18 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | (spl6_1 | ~spl6_24)),
% 0.22/0.48    inference(backward_demodulation,[],[f33,f152])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl6_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f151])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0) | spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    spl6_1 <=> v1_xboole_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl6_24 | spl6_25 | ~spl6_14 | ~spl6_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f145,f140,f85,f154,f151])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    spl6_22 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl6_14 | ~spl6_22)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl6_14 | ~spl6_22)),
% 0.22/0.48    inference(superposition,[],[f86,f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f140])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    spl6_22 | ~spl6_6 | ~spl6_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f133,f125,f51,f140])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl6_6 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl6_21 <=> ! [X1,X0] : (k1_xboole_0 = k2_zfmisc_1(X0,sK1) | ~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl6_6 | ~spl6_21)),
% 0.22/0.48    inference(resolution,[],[f126,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f51])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) | k1_xboole_0 = k2_zfmisc_1(X0,sK1)) ) | ~spl6_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f125])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl6_21 | spl6_2 | ~spl6_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f110,f102,f36,f125])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl6_17 <=> ! [X1,X3,X0,X2] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,sK1) | ~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) ) | (spl6_2 | ~spl6_17)),
% 0.22/0.48    inference(resolution,[],[f103,f37])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | ~spl6_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f102])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    spl6_19 | spl6_2 | ~spl6_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f105,f95,f36,f113])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl6_16 <=> ! [X1,X3,X0,X2] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(sK1,X0) | ~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1))) ) | (spl6_2 | ~spl6_16)),
% 0.22/0.48    inference(resolution,[],[f96,f37])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | ~spl6_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    spl6_18 | ~spl6_10 | ~spl6_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f98,f91,f67,f107])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl6_10 <=> ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl6_15 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | (~spl6_10 | ~spl6_15)),
% 0.22/0.48    inference(resolution,[],[f92,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) ) | ~spl6_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f91])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl6_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f102])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl6_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f95])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl6_15 | ~spl6_3 | ~spl6_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f83,f79,f40,f91])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl6_3 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl6_13 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_3 | ~spl6_13)),
% 0.22/0.48    inference(condensation,[],[f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) ) | (~spl6_3 | ~spl6_13)),
% 0.22/0.48    inference(resolution,[],[f80,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f40])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl6_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl6_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f85])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl6_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f79])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl6_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f67])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl6_5 | spl6_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f14,f51,f48])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f44])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f40])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ~spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f15,f36])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ~spl6_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f32])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (3681)------------------------------
% 0.22/0.48  % (3681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3681)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (3681)Memory used [KB]: 10618
% 0.22/0.48  % (3681)Time elapsed: 0.068 s
% 0.22/0.48  % (3681)------------------------------
% 0.22/0.48  % (3681)------------------------------
% 0.22/0.49  % (3671)Success in time 0.124 s
%------------------------------------------------------------------------------
