%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0301+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 221 expanded)
%              Number of leaves         :   30 ( 105 expanded)
%              Depth                    :    6
%              Number of atoms          :  328 ( 594 expanded)
%              Number of equality atoms :   71 ( 140 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f44,f51,f57,f66,f70,f81,f90,f94,f102,f106,f124,f129,f138,f143,f150,f158,f179,f183,f187,f198,f210,f227,f236,f240])).

fof(f240,plain,
    ( spl8_12
    | ~ spl8_26
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f239])).

% (26438)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (26437)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f239,plain,
    ( $false
    | spl8_12
    | ~ spl8_26
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f186,f186,f93,f178])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK6(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl8_26
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK6(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f93,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(o_0_0_xboole_0,sK1)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_12
  <=> o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f186,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_28
  <=> ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f236,plain,
    ( spl8_10
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl8_10
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f229,f80])).

fof(f80,plain,
    ( o_0_0_xboole_0 != sK1
    | spl8_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_10
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f229,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(resolution,[],[f209,f123])).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_18
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f209,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_30
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f227,plain,
    ( spl8_11
    | ~ spl8_18
    | ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl8_11
    | ~ spl8_18
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f220,f89])).

fof(f89,plain,
    ( o_0_0_xboole_0 != sK0
    | spl8_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_11
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f220,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl8_18
    | ~ spl8_29 ),
    inference(resolution,[],[f206,f123])).

fof(f206,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl8_29
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f210,plain,
    ( spl8_29
    | spl8_30
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f200,f185,f148,f208,f205])).

fof(f148,plain,
    ( spl8_23
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),o_0_0_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f149,f186])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),o_0_0_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f198,plain,
    ( spl8_14
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl8_14
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f101,f186,f186,f182])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK7(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl8_27
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK7(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f101,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK0,o_0_0_xboole_0)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl8_14
  <=> o_0_0_xboole_0 = k2_zfmisc_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f187,plain,
    ( spl8_28
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f168,f156,f141,f185])).

fof(f141,plain,
    ( spl8_22
  <=> ! [X1,X5,X0,X4] :
        ( ~ r2_hidden(X4,X0)
        | ~ r2_hidden(X5,X1)
        | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f156,plain,
    ( spl8_24
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f168,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(condensation,[],[f164])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,o_0_0_xboole_0)
        | ~ r2_hidden(X1,X2) )
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(resolution,[],[f157,f142])).

fof(f142,plain,
    ( ! [X4,X0,X5,X1] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(X5,X1)
        | ~ r2_hidden(X4,X0) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f141])).

fof(f157,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,o_0_0_xboole_0))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f156])).

fof(f183,plain,(
    spl8_27 ),
    inference(avatar_split_clause,[],[f21,f181])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f179,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f20,f177])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f158,plain,
    ( spl8_24
    | ~ spl8_1
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f144,f136,f35,f156])).

fof(f35,plain,
    ( spl8_1
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f136,plain,
    ( spl8_21
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f144,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,o_0_0_xboole_0))
    | ~ spl8_1
    | ~ spl8_21 ),
    inference(resolution,[],[f137,f36])).

fof(f36,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f136])).

fof(f150,plain,
    ( spl8_23
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f146,f141,f104,f148])).

fof(f104,plain,
    ( spl8_15
  <=> o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),o_0_0_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(superposition,[],[f142,f105])).

fof(f105,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f143,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f28,f141])).

fof(f28,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f138,plain,
    ( spl8_21
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f134,f127,f68,f136])).

fof(f68,plain,
    ( spl8_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f127,plain,
    ( spl8_19
  <=> ! [X1,X3,X0] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

% (26436)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(resolution,[],[f128,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f128,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f30,f127])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f124,plain,
    ( spl8_18
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f72,f64,f35,f122])).

fof(f64,plain,
    ( spl8_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f72,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | r2_hidden(sK2(X0),X0) )
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f17,f71])).

fof(f71,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(resolution,[],[f65,f36])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f106,plain,
    ( spl8_15
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f87,f64,f53,f35,f104])).

fof(f53,plain,
    ( spl8_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f87,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f54,f71])).

fof(f54,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f102,plain,
    ( ~ spl8_14
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f86,f64,f39,f35,f100])).

fof(f39,plain,
    ( spl8_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f86,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK0,o_0_0_xboole_0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f40,f71])).

fof(f40,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f94,plain,
    ( ~ spl8_12
    | ~ spl8_1
    | spl8_4
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f74,f64,f46,f35,f92])).

fof(f46,plain,
    ( spl8_4
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f74,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(o_0_0_xboole_0,sK1)
    | ~ spl8_1
    | spl8_4
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f47,f71])).

fof(f47,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f90,plain,
    ( ~ spl8_11
    | ~ spl8_1
    | spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f88,f64,f49,f35,f83])).

fof(f49,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f88,plain,
    ( o_0_0_xboole_0 != sK0
    | ~ spl8_1
    | spl8_5
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f50,f71])).

fof(f50,plain,
    ( k1_xboole_0 != sK0
    | spl8_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f81,plain,
    ( ~ spl8_10
    | ~ spl8_1
    | spl8_3
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f73,f64,f42,f35,f79])).

fof(f42,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f73,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl8_1
    | spl8_3
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f43,f71])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | spl8_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f70,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f18,f68])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f66,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f16,f64])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f57,plain,
    ( spl8_6
    | spl8_3
    | spl8_5 ),
    inference(avatar_split_clause,[],[f14,f49,f42,f53])).

fof(f14,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f51,plain,
    ( ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f33,f49,f46])).

fof(f33,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,
    ( ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f32,f42,f39])).

fof(f32,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

%------------------------------------------------------------------------------
