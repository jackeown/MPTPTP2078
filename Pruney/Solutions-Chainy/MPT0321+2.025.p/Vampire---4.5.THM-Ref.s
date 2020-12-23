%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:32 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 165 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  238 ( 446 expanded)
%              Number of equality atoms :   43 ( 128 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f90,f95,f144,f161,f170,f368,f387,f404,f410,f418,f426,f438,f444])).

fof(f444,plain,
    ( spl8_2
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | spl8_2
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f80,f25,f307,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f307,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl8_28
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f80,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f438,plain,
    ( ~ spl8_13
    | spl8_28 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | ~ spl8_13
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f308,f166,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f166,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_13
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f308,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f306])).

fof(f426,plain,
    ( spl8_4
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | spl8_4
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f89,f133,f142,f30])).

fof(f142,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl8_11
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f133,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_9
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f89,plain,
    ( sK0 != sK2
    | spl8_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f418,plain,
    ( spl8_11
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f362,f168,f141])).

fof(f168,plain,
    ( spl8_14
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f362,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl8_14 ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl8_14 ),
    inference(resolution,[],[f188,f32])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK2),sK0)
        | r1_tarski(X1,sK2) )
    | ~ spl8_14 ),
    inference(resolution,[],[f169,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f169,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f168])).

fof(f410,plain,
    ( spl8_3
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl8_3
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f85,f139,f130,f30])).

fof(f130,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_8
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f139,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_10
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f85,plain,
    ( sK1 != sK3
    | spl8_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f404,plain,
    ( spl8_8
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f403,f366,f128])).

fof(f366,plain,
    ( spl8_30
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f403,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl8_30 ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl8_30 ),
    inference(resolution,[],[f390,f32])).

fof(f390,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(X2,sK3),sK1)
        | r1_tarski(X2,sK3) )
    | ~ spl8_30 ),
    inference(resolution,[],[f367,f33])).

fof(f367,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f366])).

fof(f387,plain,
    ( spl8_1
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl8_1
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f75,f25,f376,f30])).

fof(f376,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl8_17 ),
    inference(resolution,[],[f199,f32])).

fof(f199,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl8_17
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f75,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f368,plain,
    ( spl8_17
    | spl8_30
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f163,f92,f366,f198])).

fof(f92,plain,
    ( spl8_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f106,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

% (28661)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (28676)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f106,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X11,sK3) )
    | ~ spl8_5 ),
    inference(superposition,[],[f56,f94])).

fof(f94,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f170,plain,
    ( spl8_13
    | spl8_14
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f162,f92,f168,f165])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f105,f57])).

fof(f105,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X8,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f94])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f161,plain,
    ( spl8_9
    | spl8_2
    | ~ spl8_8
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f150,f92,f128,f78,f132])).

fof(f150,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1
    | r1_tarski(sK2,sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f100,plain,
    ( ! [X3] :
        ( r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X3,sK3) )
    | ~ spl8_5 ),
    inference(superposition,[],[f38,f94])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f144,plain,
    ( spl8_10
    | spl8_1
    | ~ spl8_11
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f113,f92,f141,f73,f137])).

fof(f113,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0
    | r1_tarski(sK3,sK1)
    | ~ spl8_5 ),
    inference(resolution,[],[f98,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,
    ( ! [X1] :
        ( r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X1,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f37,f94])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f21,f92])).

fof(f21,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f90,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f20,f87,f83])).

fof(f20,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f23,f78])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f22,f73])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:04:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (28658)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.53  % (28664)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (28668)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.53  % (28673)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.53  % (28670)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.16/0.54  % (28656)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.55  % (28654)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.55  % (28655)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.16/0.55  % (28653)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.16/0.55  % (28667)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.55  % (28651)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.56  % (28673)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f445,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f76,f81,f90,f95,f144,f161,f170,f368,f387,f404,f410,f418,f426,f438,f444])).
% 1.44/0.56  fof(f444,plain,(
% 1.44/0.56    spl8_2 | ~spl8_28),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f440])).
% 1.44/0.56  fof(f440,plain,(
% 1.44/0.56    $false | (spl8_2 | ~spl8_28)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f80,f25,f307,f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.56  fof(f307,plain,(
% 1.44/0.56    r1_tarski(sK1,k1_xboole_0) | ~spl8_28),
% 1.44/0.56    inference(avatar_component_clause,[],[f306])).
% 1.44/0.56  fof(f306,plain,(
% 1.44/0.56    spl8_28 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.44/0.56  fof(f80,plain,(
% 1.44/0.56    k1_xboole_0 != sK1 | spl8_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f78])).
% 1.44/0.56  fof(f78,plain,(
% 1.44/0.56    spl8_2 <=> k1_xboole_0 = sK1),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.44/0.56  fof(f438,plain,(
% 1.44/0.56    ~spl8_13 | spl8_28),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f432])).
% 1.44/0.56  fof(f432,plain,(
% 1.44/0.56    $false | (~spl8_13 | spl8_28)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f308,f166,f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.44/0.56  fof(f166,plain,(
% 1.44/0.56    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_13),
% 1.44/0.56    inference(avatar_component_clause,[],[f165])).
% 1.44/0.56  fof(f165,plain,(
% 1.44/0.56    spl8_13 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.44/0.56  fof(f308,plain,(
% 1.44/0.56    ~r1_tarski(sK1,k1_xboole_0) | spl8_28),
% 1.44/0.56    inference(avatar_component_clause,[],[f306])).
% 1.44/0.56  fof(f426,plain,(
% 1.44/0.56    spl8_4 | ~spl8_9 | ~spl8_11),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f422])).
% 1.44/0.56  fof(f422,plain,(
% 1.44/0.56    $false | (spl8_4 | ~spl8_9 | ~spl8_11)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f89,f133,f142,f30])).
% 1.44/0.56  fof(f142,plain,(
% 1.44/0.56    r1_tarski(sK0,sK2) | ~spl8_11),
% 1.44/0.56    inference(avatar_component_clause,[],[f141])).
% 1.44/0.56  fof(f141,plain,(
% 1.44/0.56    spl8_11 <=> r1_tarski(sK0,sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.44/0.56  fof(f133,plain,(
% 1.44/0.56    r1_tarski(sK2,sK0) | ~spl8_9),
% 1.44/0.56    inference(avatar_component_clause,[],[f132])).
% 1.44/0.56  fof(f132,plain,(
% 1.44/0.56    spl8_9 <=> r1_tarski(sK2,sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.44/0.56  fof(f89,plain,(
% 1.44/0.56    sK0 != sK2 | spl8_4),
% 1.44/0.56    inference(avatar_component_clause,[],[f87])).
% 1.44/0.56  fof(f87,plain,(
% 1.44/0.56    spl8_4 <=> sK0 = sK2),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.44/0.56  fof(f418,plain,(
% 1.44/0.56    spl8_11 | ~spl8_14),
% 1.44/0.56    inference(avatar_split_clause,[],[f362,f168,f141])).
% 1.44/0.56  fof(f168,plain,(
% 1.44/0.56    spl8_14 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.44/0.56  fof(f362,plain,(
% 1.44/0.56    r1_tarski(sK0,sK2) | ~spl8_14),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f361])).
% 1.44/0.56  fof(f361,plain,(
% 1.44/0.56    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl8_14),
% 1.44/0.56    inference(resolution,[],[f188,f32])).
% 1.44/0.56  fof(f188,plain,(
% 1.44/0.56    ( ! [X1] : (~r2_hidden(sK5(X1,sK2),sK0) | r1_tarski(X1,sK2)) ) | ~spl8_14),
% 1.44/0.56    inference(resolution,[],[f169,f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f16])).
% 1.44/0.56  fof(f169,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl8_14),
% 1.44/0.56    inference(avatar_component_clause,[],[f168])).
% 1.44/0.56  fof(f410,plain,(
% 1.44/0.56    spl8_3 | ~spl8_8 | ~spl8_10),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f406])).
% 1.44/0.56  fof(f406,plain,(
% 1.44/0.56    $false | (spl8_3 | ~spl8_8 | ~spl8_10)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f85,f139,f130,f30])).
% 1.44/0.56  fof(f130,plain,(
% 1.44/0.56    r1_tarski(sK1,sK3) | ~spl8_8),
% 1.44/0.56    inference(avatar_component_clause,[],[f128])).
% 1.44/0.56  fof(f128,plain,(
% 1.44/0.56    spl8_8 <=> r1_tarski(sK1,sK3)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.44/0.56  fof(f139,plain,(
% 1.44/0.56    r1_tarski(sK3,sK1) | ~spl8_10),
% 1.44/0.56    inference(avatar_component_clause,[],[f137])).
% 1.44/0.56  fof(f137,plain,(
% 1.44/0.56    spl8_10 <=> r1_tarski(sK3,sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.44/0.56  fof(f85,plain,(
% 1.44/0.56    sK1 != sK3 | spl8_3),
% 1.44/0.56    inference(avatar_component_clause,[],[f83])).
% 1.44/0.56  fof(f83,plain,(
% 1.44/0.56    spl8_3 <=> sK1 = sK3),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.44/0.56  fof(f404,plain,(
% 1.44/0.56    spl8_8 | ~spl8_30),
% 1.44/0.56    inference(avatar_split_clause,[],[f403,f366,f128])).
% 1.44/0.56  fof(f366,plain,(
% 1.44/0.56    spl8_30 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.44/0.56  fof(f403,plain,(
% 1.44/0.56    r1_tarski(sK1,sK3) | ~spl8_30),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f402])).
% 1.44/0.56  fof(f402,plain,(
% 1.44/0.56    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl8_30),
% 1.44/0.56    inference(resolution,[],[f390,f32])).
% 1.44/0.56  fof(f390,plain,(
% 1.44/0.56    ( ! [X2] : (~r2_hidden(sK5(X2,sK3),sK1) | r1_tarski(X2,sK3)) ) | ~spl8_30),
% 1.44/0.56    inference(resolution,[],[f367,f33])).
% 1.44/0.56  fof(f367,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl8_30),
% 1.44/0.56    inference(avatar_component_clause,[],[f366])).
% 1.44/0.56  fof(f387,plain,(
% 1.44/0.56    spl8_1 | ~spl8_17),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f383])).
% 1.44/0.56  fof(f383,plain,(
% 1.44/0.56    $false | (spl8_1 | ~spl8_17)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f75,f25,f376,f30])).
% 1.44/0.56  fof(f376,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl8_17),
% 1.44/0.56    inference(resolution,[],[f199,f32])).
% 1.44/0.56  fof(f199,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_17),
% 1.44/0.56    inference(avatar_component_clause,[],[f198])).
% 1.44/0.56  fof(f198,plain,(
% 1.44/0.56    spl8_17 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.44/0.56  fof(f75,plain,(
% 1.44/0.56    k1_xboole_0 != sK0 | spl8_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f73])).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    spl8_1 <=> k1_xboole_0 = sK0),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.44/0.56  fof(f368,plain,(
% 1.44/0.56    spl8_17 | spl8_30 | ~spl8_5),
% 1.44/0.56    inference(avatar_split_clause,[],[f163,f92,f366,f198])).
% 1.44/0.56  fof(f92,plain,(
% 1.44/0.56    spl8_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.44/0.56  fof(f163,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl8_5),
% 1.44/0.56    inference(resolution,[],[f106,f57])).
% 1.44/0.56  fof(f57,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.44/0.56  % (28661)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.56  % (28676)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.56  fof(f106,plain,(
% 1.44/0.56    ( ! [X10,X11] : (~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X11,sK3)) ) | ~spl8_5),
% 1.44/0.56    inference(superposition,[],[f56,f94])).
% 1.44/0.56  fof(f94,plain,(
% 1.44/0.56    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl8_5),
% 1.44/0.56    inference(avatar_component_clause,[],[f92])).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f8])).
% 1.44/0.56  fof(f170,plain,(
% 1.44/0.56    spl8_13 | spl8_14 | ~spl8_5),
% 1.44/0.56    inference(avatar_split_clause,[],[f162,f92,f168,f165])).
% 1.44/0.56  fof(f162,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_5),
% 1.44/0.56    inference(resolution,[],[f105,f57])).
% 1.44/0.56  fof(f105,plain,(
% 1.44/0.56    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X8,sK2)) ) | ~spl8_5),
% 1.44/0.56    inference(superposition,[],[f55,f94])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f8])).
% 1.44/0.56  fof(f161,plain,(
% 1.44/0.56    spl8_9 | spl8_2 | ~spl8_8 | ~spl8_5),
% 1.44/0.56    inference(avatar_split_clause,[],[f150,f92,f128,f78,f132])).
% 1.44/0.56  fof(f150,plain,(
% 1.44/0.56    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1 | r1_tarski(sK2,sK0) | ~spl8_5),
% 1.44/0.56    inference(resolution,[],[f100,f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X3,sK3)) ) | ~spl8_5),
% 1.44/0.56    inference(superposition,[],[f38,f94])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.44/0.56  fof(f144,plain,(
% 1.44/0.56    spl8_10 | spl8_1 | ~spl8_11 | ~spl8_5),
% 1.44/0.56    inference(avatar_split_clause,[],[f113,f92,f141,f73,f137])).
% 1.44/0.56  fof(f113,plain,(
% 1.44/0.56    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0 | r1_tarski(sK3,sK1) | ~spl8_5),
% 1.44/0.56    inference(resolution,[],[f98,f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f98,plain,(
% 1.44/0.56    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X1,sK2)) ) | ~spl8_5),
% 1.44/0.56    inference(superposition,[],[f37,f94])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f17])).
% 1.44/0.56  fof(f95,plain,(
% 1.44/0.56    spl8_5),
% 1.44/0.56    inference(avatar_split_clause,[],[f21,f92])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.44/0.56    inference(flattening,[],[f14])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.56    inference(negated_conjecture,[],[f12])).
% 1.44/0.56  fof(f12,conjecture,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.44/0.56  fof(f90,plain,(
% 1.44/0.56    ~spl8_3 | ~spl8_4),
% 1.44/0.56    inference(avatar_split_clause,[],[f20,f87,f83])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    sK0 != sK2 | sK1 != sK3),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f81,plain,(
% 1.44/0.56    ~spl8_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f23,f78])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    k1_xboole_0 != sK1),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f76,plain,(
% 1.44/0.56    ~spl8_1),
% 1.44/0.56    inference(avatar_split_clause,[],[f22,f73])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    k1_xboole_0 != sK0),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (28673)------------------------------
% 1.44/0.56  % (28673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (28673)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (28673)Memory used [KB]: 11001
% 1.44/0.56  % (28673)Time elapsed: 0.081 s
% 1.44/0.56  % (28674)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.56  % (28673)------------------------------
% 1.44/0.56  % (28673)------------------------------
% 1.44/0.56  % (28678)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.56  % (28671)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.56  % (28680)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.56  % (28665)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.56  % (28647)Success in time 0.188 s
%------------------------------------------------------------------------------
