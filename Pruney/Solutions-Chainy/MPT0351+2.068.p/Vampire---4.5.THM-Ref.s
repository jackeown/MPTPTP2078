%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 (  97 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :  181 ( 248 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f53,f65,f77,f81,f95,f103,f114,f128,f134])).

fof(f134,plain,
    ( ~ spl3_1
    | spl3_18
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl3_1
    | spl3_18
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f131,f36])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f131,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_18
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_18
    | ~ spl3_20 ),
    inference(superposition,[],[f113,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f113,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_18
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f128,plain,
    ( spl3_20
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f97,f93,f79,f126])).

fof(f79,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f93,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(resolution,[],[f94,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f93])).

fof(f114,plain,
    ( ~ spl3_18
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f110,f101,f51,f39,f35,f112])).

fof(f39,plain,
    ( spl3_2
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( spl3_5
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f110,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f109,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_2
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f52,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f108,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_2
    | ~ spl3_16 ),
    inference(superposition,[],[f40,f102])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f40,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f103,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f29,f101])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f95,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f83,f75,f63,f43,f93])).

fof(f43,plain,
    ( spl3_3
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f44,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f81,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f24,f79])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f77,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f23,f75])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f51])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f19,f18])).

fof(f18,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f41,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f32,f39])).

fof(f32,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f16,f18])).

fof(f16,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:17:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (26140)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.46  % (26134)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (26139)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (26134)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f37,f41,f45,f53,f65,f77,f81,f95,f103,f114,f128,f134])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    ~spl3_1 | spl3_18 | ~spl3_20),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f133])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    $false | (~spl3_1 | spl3_18 | ~spl3_20)),
% 0.22/0.47    inference(subsumption_resolution,[],[f131,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl3_18 | ~spl3_20)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f130])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    sK0 != sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl3_18 | ~spl3_20)),
% 0.22/0.47    inference(superposition,[],[f113,f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f126])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    spl3_20 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    sK0 != k2_xboole_0(sK1,sK0) | spl3_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f112])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    spl3_18 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    spl3_20 | ~spl3_12 | ~spl3_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f97,f93,f79,f126])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    spl3_12 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    spl3_15 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1) ) | (~spl3_12 | ~spl3_15)),
% 0.22/0.47    inference(resolution,[],[f94,f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f79])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f93])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    ~spl3_18 | ~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f110,f101,f51,f39,f35,f112])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl3_2 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl3_5 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl3_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    sK0 != k2_xboole_0(sK1,sK0) | (~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_16)),
% 0.22/0.47    inference(subsumption_resolution,[],[f109,f36])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    sK0 != k2_xboole_0(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl3_2 | ~spl3_5 | ~spl3_16)),
% 0.22/0.47    inference(subsumption_resolution,[],[f108,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    sK0 != k2_xboole_0(sK1,sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl3_2 | ~spl3_16)),
% 0.22/0.47    inference(superposition,[],[f40,f102])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f101])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    sK0 != k4_subset_1(sK0,sK1,sK0) | spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f39])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    spl3_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f101])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    spl3_15 | ~spl3_3 | ~spl3_8 | ~spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f83,f75,f63,f43,f93])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl3_3 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl3_8 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    spl3_11 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl3_3 | ~spl3_8 | ~spl3_11)),
% 0.22/0.47    inference(subsumption_resolution,[],[f82,f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f43])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl3_8 | ~spl3_11)),
% 0.22/0.47    inference(resolution,[],[f76,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f63])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) ) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f75])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f79])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f75])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f30,f63])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(equality_resolution,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f33,f51])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f19,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f17,f43])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f32,f39])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 0.22/0.47    inference(backward_demodulation,[],[f16,f18])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f35])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (26134)------------------------------
% 0.22/0.47  % (26134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26134)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (26134)Memory used [KB]: 10618
% 0.22/0.47  % (26134)Time elapsed: 0.059 s
% 0.22/0.47  % (26134)------------------------------
% 0.22/0.47  % (26134)------------------------------
% 0.22/0.47  % (26123)Success in time 0.111 s
%------------------------------------------------------------------------------
