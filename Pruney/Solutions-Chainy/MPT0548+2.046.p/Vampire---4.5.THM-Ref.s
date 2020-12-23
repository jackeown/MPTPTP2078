%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 108 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :  185 ( 259 expanded)
%              Number of equality atoms :   47 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f49,f53,f61,f67,f75,f79,f94,f101,f110,f115,f120])).

fof(f120,plain,
    ( spl4_1
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_1
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f32,f109])).

fof(f109,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_18
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f32,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f115,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_9
    | spl4_17 ),
    inference(subsumption_resolution,[],[f112,f66])).

fof(f66,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_9
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f112,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_8
    | spl4_17 ),
    inference(resolution,[],[f106,f60])).

fof(f60,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | r2_hidden(sK1(X0),X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_8
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f106,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_17
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f110,plain,
    ( ~ spl4_17
    | spl4_18
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f103,f99,f73,f43,f108,f105])).

fof(f43,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f73,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f99,plain,
    ( spl4_16
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f103,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f102,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f102,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(superposition,[],[f74,f100])).

fof(f100,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f101,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f97,f92,f65,f39,f35,f99])).

fof(f35,plain,
    ( spl4_2
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f39,plain,
    ( spl4_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f92,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k1_relat_1(X0),X1)
        | k7_relat_1(X0,X1) = X0
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f97,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f96,f66])).

fof(f96,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f36,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(superposition,[],[f93,f40])).

fof(f40,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),X1)
        | k7_relat_1(X0,X1) = X0
        | r2_hidden(sK1(X0),X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl4_15
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f88,f77,f59,f92])).

fof(f77,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),X1)
        | k7_relat_1(X0,X1) = X0
        | r2_hidden(sK1(X0),X0) )
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f24,f77])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f75,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f23,f73])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f67,plain,
    ( spl4_9
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f62,f51,f47,f65])).

fof(f47,plain,
    ( spl4_5
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f51,plain,
    ( spl4_6
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f62,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f48,f52])).

fof(f52,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f48,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f61,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f20,f59])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f53,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f49,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f45,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f41,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f33,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:51:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.47  % (16415)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (16428)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (16415)Refutation not found, incomplete strategy% (16415)------------------------------
% 0.21/0.48  % (16415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16415)Memory used [KB]: 10490
% 0.21/0.48  % (16415)Time elapsed: 0.059 s
% 0.21/0.48  % (16415)------------------------------
% 0.21/0.48  % (16415)------------------------------
% 0.21/0.49  % (16423)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (16420)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (16423)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f49,f53,f61,f67,f75,f79,f94,f101,f110,f115,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_1 | ~spl4_18),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_18)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f32,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl4_18 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    spl4_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~spl4_8 | ~spl4_9 | spl4_17),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    $false | (~spl4_8 | ~spl4_9 | spl4_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl4_9 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | (~spl4_8 | spl4_17)),
% 0.21/0.49    inference(resolution,[],[f106,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) ) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl4_8 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | spl4_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl4_17 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~spl4_17 | spl4_18 | ~spl4_4 | ~spl4_11 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f103,f99,f73,f43,f108,f105])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl4_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl4_11 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl4_16 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_4 | ~spl4_11 | ~spl4_16)),
% 0.21/0.49    inference(forward_demodulation,[],[f102,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_11 | ~spl4_16)),
% 0.21/0.49    inference(superposition,[],[f74,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_16 | ~spl4_2 | ~spl4_3 | ~spl4_9 | ~spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f92,f65,f39,f35,f99])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl4_2 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl4_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl4_15 <=> ! [X1,X0] : (~r1_tarski(k1_relat_1(X0),X1) | k7_relat_1(X0,X1) = X0 | r2_hidden(sK1(X0),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_9 | ~spl4_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f66])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f35])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)) ) | (~spl4_3 | ~spl4_15)),
% 0.21/0.49    inference(superposition,[],[f93,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | k7_relat_1(X0,X1) = X0 | r2_hidden(sK1(X0),X0)) ) | ~spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl4_15 | ~spl4_8 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f88,f77,f59,f92])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl4_12 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | k7_relat_1(X0,X1) = X0 | r2_hidden(sK1(X0),X0)) ) | (~spl4_8 | ~spl4_12)),
% 0.21/0.49    inference(resolution,[],[f78,f60])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) ) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f77])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f73])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl4_9 | ~spl4_5 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f51,f47,f65])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl4_5 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl4_6 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_5 | ~spl4_6)),
% 0.21/0.49    inference(superposition,[],[f48,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f47])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f59])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f51])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f43])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f39])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f35])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (16423)------------------------------
% 0.21/0.49  % (16423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16423)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (16423)Memory used [KB]: 10618
% 0.21/0.49  % (16423)Time elapsed: 0.076 s
% 0.21/0.49  % (16423)------------------------------
% 0.21/0.49  % (16423)------------------------------
% 0.21/0.49  % (16413)Success in time 0.13 s
%------------------------------------------------------------------------------
