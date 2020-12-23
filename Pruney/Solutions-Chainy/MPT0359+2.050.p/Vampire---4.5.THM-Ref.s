%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 142 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  172 ( 272 expanded)
%              Number of equality atoms :   45 ( 102 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f58,f113,f192,f194,f208,f259])).

fof(f259,plain,
    ( spl2_2
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl2_2
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f116,f145])).

fof(f145,plain,
    ( sK0 = sK1
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl2_7
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f116,plain,
    ( sK0 != sK1
    | spl2_2 ),
    inference(forward_demodulation,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f27,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f25,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f56,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_2
  <=> sK1 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f208,plain,
    ( ~ spl2_9
    | spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f207,f189,f143,f185])).

fof(f185,plain,
    ( spl2_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f189,plain,
    ( spl2_10
  <=> k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f207,plain,
    ( sK0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f199,f42])).

fof(f199,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_10 ),
    inference(superposition,[],[f31,f191])).

fof(f191,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f189])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f194,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl2_9 ),
    inference(subsumption_resolution,[],[f24,f187])).

fof(f187,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f185])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f192,plain,
    ( ~ spl2_9
    | spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f179,f50,f189,f185])).

fof(f50,plain,
    ( spl2_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f179,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(resolution,[],[f177,f51])).

fof(f51,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | k1_xboole_0 = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f172])).

% (12454)Refutation not found, incomplete strategy% (12454)------------------------------
% (12454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12454)Termination reason: Refutation not found, incomplete strategy

% (12454)Memory used [KB]: 1663
% (12454)Time elapsed: 0.115 s
% (12454)------------------------------
% (12454)------------------------------
fof(f172,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_subset_1(X0,X1)
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f89,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
      | k1_xboole_0 = k3_subset_1(X1,X2)
      | ~ r1_tarski(k3_subset_1(X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f44,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f113,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f47,f62,f61,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f91,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
      | r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f38,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f61,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f52,f59])).

fof(f59,plain,
    ( sK0 = sK1
    | ~ spl2_2 ),
    inference(superposition,[],[f42,f55])).

fof(f55,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f52,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f62,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f24,f59])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f58,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f41,f54,f50])).

fof(f41,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f22,f39])).

fof(f22,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f40,f54,f50])).

fof(f40,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f23,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:08:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (12455)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.50  % (12455)Refutation not found, incomplete strategy% (12455)------------------------------
% 0.21/0.50  % (12455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12440)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (12455)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  % (12454)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (12455)Memory used [KB]: 1663
% 0.21/0.51  % (12455)Time elapsed: 0.094 s
% 0.21/0.51  % (12455)------------------------------
% 0.21/0.51  % (12455)------------------------------
% 0.21/0.51  % (12441)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (12450)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (12447)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (12447)Refutation not found, incomplete strategy% (12447)------------------------------
% 0.21/0.51  % (12447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12459)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (12447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12447)Memory used [KB]: 10746
% 0.21/0.51  % (12447)Time elapsed: 0.105 s
% 0.21/0.51  % (12447)------------------------------
% 0.21/0.51  % (12447)------------------------------
% 0.21/0.52  % (12463)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (12450)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (12451)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f57,f58,f113,f192,f194,f208,f259])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    spl2_2 | ~spl2_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    $false | (spl2_2 | ~spl2_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f116,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl2_7 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    sK0 != sK1 | spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f56,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    sK1 != k3_subset_1(sK0,k1_xboole_0) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl2_2 <=> sK1 = k3_subset_1(sK0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~spl2_9 | spl2_7 | ~spl2_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f207,f189,f143,f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    spl2_9 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    spl2_10 <=> k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    sK0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_10),
% 0.21/0.52    inference(forward_demodulation,[],[f199,f42])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_10),
% 0.21/0.52    inference(superposition,[],[f31,f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~spl2_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f189])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    spl2_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f193])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    $false | spl2_9),
% 0.21/0.52    inference(subsumption_resolution,[],[f24,f187])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f185])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~spl2_9 | spl2_10 | ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f179,f50,f189,f185])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl2_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f177,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | k1_xboole_0 = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.52  % (12454)Refutation not found, incomplete strategy% (12454)------------------------------
% 0.21/0.52  % (12454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12454)Memory used [KB]: 1663
% 0.21/0.52  % (12454)Time elapsed: 0.115 s
% 0.21/0.52  % (12454)------------------------------
% 0.21/0.52  % (12454)------------------------------
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k3_subset_1(X0,X1) | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(resolution,[],[f89,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) | k1_xboole_0 = k3_subset_1(X1,X2) | ~r1_tarski(k3_subset_1(X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(superposition,[],[f44,f31])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f26])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl2_1 | ~spl2_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f47,f62,f61,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X2) | ~r1_tarski(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X2) | ~r1_tarski(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X0,X2)) )),
% 0.21/0.52    inference(resolution,[],[f91,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k3_xboole_0(X0,X1),X2) | r1_tarski(k3_subset_1(X0,X1),X2) | ~r1_tarski(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(superposition,[],[f38,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl2_1 | ~spl2_2)),
% 0.21/0.52    inference(superposition,[],[f52,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f42,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f24,f59])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl2_1 | spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f54,f50])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f39])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f54,f50])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f23,f39])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12450)------------------------------
% 0.21/0.52  % (12450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12450)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12450)Memory used [KB]: 6396
% 0.21/0.52  % (12450)Time elapsed: 0.118 s
% 0.21/0.52  % (12450)------------------------------
% 0.21/0.52  % (12450)------------------------------
% 0.21/0.52  % (12463)Refutation not found, incomplete strategy% (12463)------------------------------
% 0.21/0.52  % (12463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12463)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12463)Memory used [KB]: 6268
% 0.21/0.52  % (12463)Time elapsed: 0.116 s
% 0.21/0.52  % (12463)------------------------------
% 0.21/0.52  % (12463)------------------------------
% 0.21/0.52  % (12465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (12436)Success in time 0.17 s
%------------------------------------------------------------------------------
