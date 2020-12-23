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
% DateTime   : Thu Dec  3 12:47:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 130 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :    5
%              Number of atoms          :  213 ( 321 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f54,f58,f66,f74,f82,f86,f95,f108,f122,f126,f130,f154,f167,f178])).

fof(f178,plain,
    ( spl5_1
    | ~ spl5_22
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl5_1
    | ~ spl5_22
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f175,f34])).

fof(f34,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f175,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_22
    | ~ spl5_24 ),
    inference(resolution,[],[f166,f153])).

fof(f153,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_xboole_0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_22
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK2(k1_xboole_0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f166,plain,
    ( ! [X3] : ~ r2_hidden(X3,k2_relat_1(k1_xboole_0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_24
  <=> ! [X3] : ~ r2_hidden(X3,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f167,plain,
    ( spl5_24
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f117,f106,f84,f72,f165])).

fof(f72,plain,
    ( spl5_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f84,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,k2_relat_1(X1))
        | r2_hidden(sK1(X1),k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f106,plain,
    ( spl5_17
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f117,plain,
    ( ! [X3] : ~ r2_hidden(X3,k2_relat_1(k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f116,f73])).

fof(f73,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f116,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(resolution,[],[f107,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X1),k1_relat_1(X1))
        | ~ r2_hidden(X0,k2_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f107,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f106])).

fof(f154,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f136,f124,f120,f80,f44,f152])).

fof(f44,plain,
    ( spl5_4
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f80,plain,
    ( spl5_12
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f120,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
        | r2_hidden(sK2(X0,X1),X1)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f124,plain,
    ( spl5_20
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK2(k1_xboole_0,X0),X0) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f128,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(resolution,[],[f125,f45])).

fof(f45,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f125,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f124])).

fof(f128,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_xboole_0,X0),X0)
        | k1_relat_1(k1_xboole_0) = X0 )
    | ~ spl5_12
    | ~ spl5_19 ),
    inference(resolution,[],[f121,f81])).

fof(f81,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
        | r2_hidden(sK2(X0,X1),X1)
        | k1_relat_1(X0) = X1 )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f130,plain,
    ( spl5_2
    | ~ spl5_12
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl5_2
    | ~ spl5_12
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f37,f81,f81,f121])).

fof(f37,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f126,plain,
    ( spl5_20
    | ~ spl5_9
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f115,f106,f64,f124])).

fof(f64,plain,
    ( spl5_9
  <=> ! [X0] :
        ( r2_hidden(sK0(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f115,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl5_9
    | ~ spl5_17 ),
    inference(resolution,[],[f107,f65])).

fof(f65,plain,
    ( ! [X0] :
        ( r2_hidden(sK0(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f122,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f23,f120])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f108,plain,
    ( spl5_17
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f104,f93,f80,f106])).

fof(f93,plain,
    ( spl5_15
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(resolution,[],[f94,f81])).

fof(f94,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f28,f93])).

fof(f28,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f86,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f20,f84])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK1(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f82,plain,
    ( spl5_12
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f67,f56,f52,f80])).

fof(f52,plain,
    ( spl5_6
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f56,plain,
    ( spl5_7
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f67,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(superposition,[],[f53,f57])).

fof(f57,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f53,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f74,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f68,f56,f40,f72])).

fof(f40,plain,
    ( spl5_3
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(superposition,[],[f41,f57])).

fof(f41,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f66,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f16,f64])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f58,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f54,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f46,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f15,f44])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f42,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f38,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f14,f36,f33])).

fof(f14,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (25064)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (25070)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (25064)Refutation not found, incomplete strategy% (25064)------------------------------
% 0.20/0.47  % (25064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (25064)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (25064)Memory used [KB]: 10490
% 0.20/0.47  % (25064)Time elapsed: 0.050 s
% 0.20/0.47  % (25064)------------------------------
% 0.20/0.47  % (25064)------------------------------
% 0.20/0.47  % (25070)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f38,f42,f46,f54,f58,f66,f74,f82,f86,f95,f108,f122,f126,f130,f154,f167,f178])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl5_1 | ~spl5_22 | ~spl5_24),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    $false | (spl5_1 | ~spl5_22 | ~spl5_24)),
% 0.20/0.47    inference(subsumption_resolution,[],[f175,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl5_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl5_22 | ~spl5_24)),
% 0.20/0.47    inference(resolution,[],[f166,f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) ) | ~spl5_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f152])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    spl5_22 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(k1_xboole_0,X0),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(k1_xboole_0))) ) | ~spl5_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f165])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl5_24 <=> ! [X3] : ~r2_hidden(X3,k2_relat_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    spl5_24 | ~spl5_10 | ~spl5_13 | ~spl5_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f117,f106,f84,f72,f165])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl5_10 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl5_13 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK1(X1),k1_relat_1(X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl5_17 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(k1_xboole_0))) ) | (~spl5_10 | ~spl5_13 | ~spl5_17)),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    v1_relat_1(k1_xboole_0) | ~spl5_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl5_13 | ~spl5_17)),
% 0.20/0.47    inference(resolution,[],[f107,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK1(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl5_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | ~spl5_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    spl5_22 | ~spl5_4 | ~spl5_12 | ~spl5_19 | ~spl5_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f136,f124,f120,f80,f44,f152])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl5_4 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl5_12 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl5_19 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl5_20 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(k1_xboole_0,X0),X0)) ) | (~spl5_4 | ~spl5_12 | ~spl5_19 | ~spl5_20)),
% 0.20/0.47    inference(backward_demodulation,[],[f128,f132])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_4 | ~spl5_20)),
% 0.20/0.47    inference(resolution,[],[f125,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f44])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl5_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_relat_1(k1_xboole_0) = X0) ) | (~spl5_12 | ~spl5_19)),
% 0.20/0.47    inference(resolution,[],[f121,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) ) | ~spl5_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f120])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl5_2 | ~spl5_12 | ~spl5_19),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    $false | (spl5_2 | ~spl5_12 | ~spl5_19)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f37,f81,f81,f121])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    spl5_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl5_20 | ~spl5_9 | ~spl5_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f115,f106,f64,f124])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl5_9 <=> ! [X0] : (r2_hidden(sK0(X0),X0) | v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl5_9 | ~spl5_17)),
% 0.20/0.47    inference(resolution,[],[f107,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_xboole_0(X0)) ) | ~spl5_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl5_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f120])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl5_17 | ~spl5_12 | ~spl5_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f104,f93,f80,f106])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl5_15 <=> ! [X0,X2] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | (~spl5_12 | ~spl5_15)),
% 0.20/0.47    inference(resolution,[],[f94,f81])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) ) | ~spl5_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl5_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f93])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.47    inference(equality_resolution,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl5_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f84])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK1(X1),k1_relat_1(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl5_12 | ~spl5_6 | ~spl5_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f67,f56,f52,f80])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl5_6 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl5_7 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_6 | ~spl5_7)),
% 0.20/0.47    inference(superposition,[],[f53,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl5_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl5_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f52])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl5_10 | ~spl5_3 | ~spl5_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f68,f56,f40,f72])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl5_3 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    v1_relat_1(k1_xboole_0) | (~spl5_3 | ~spl5_7)),
% 0.20/0.47    inference(superposition,[],[f41,f57])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f40])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl5_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f64])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl5_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f56])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl5_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f52])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f15,f44])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f40])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ~spl5_1 | ~spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f14,f36,f33])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (25070)------------------------------
% 0.20/0.47  % (25070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (25070)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (25070)Memory used [KB]: 10618
% 0.20/0.47  % (25070)Time elapsed: 0.055 s
% 0.20/0.47  % (25070)------------------------------
% 0.20/0.47  % (25070)------------------------------
% 0.20/0.48  % (25060)Success in time 0.116 s
%------------------------------------------------------------------------------
