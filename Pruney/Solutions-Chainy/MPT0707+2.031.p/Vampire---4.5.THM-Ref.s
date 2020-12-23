%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 129 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :  226 ( 321 expanded)
%              Number of equality atoms :   43 (  61 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f49,f57,f61,f69,f74,f78,f82,f87,f93,f107,f112,f118,f137,f145])).

fof(f145,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f40,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f143,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f142,f56])).

fof(f56,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_6
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f142,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f141,f48])).

fof(f48,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f141,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(superposition,[],[f77,f136])).

fof(f136,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_22
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f137,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f125,f116,f72,f47,f135])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f116,plain,
    ( spl3_19
  <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f125,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f123,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(superposition,[],[f117,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f117,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f116])).

fof(f118,plain,
    ( spl3_19
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f114,f110,f105,f116])).

fof(f105,plain,
    ( spl3_17
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f110,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f114,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(resolution,[],[f111,f106])).

fof(f106,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f105])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f89,f85,f55,f47,f110])).

fof(f85,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f88,f56])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(resolution,[],[f86,f48])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f107,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f98,f91,f59,f105])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f91,plain,
    ( spl3_14
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f98,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f92,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f83,f80,f35,f91])).

fof(f35,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f83,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f81,f36])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f26,f85])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f82,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f70,f67,f43,f80])).

fof(f43,plain,
    ( spl3_3
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f68,f44])).

fof(f44,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f78,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f25,f76])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f74,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f24,f72])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f61,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f57,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f41,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:02:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (11743)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.45  % (11750)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.45  % (11750)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % (11741)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (11741)Refutation not found, incomplete strategy% (11741)------------------------------
% 0.20/0.46  % (11741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (11741)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (11741)Memory used [KB]: 6140
% 0.20/0.46  % (11741)Time elapsed: 0.053 s
% 0.20/0.46  % (11741)------------------------------
% 0.20/0.46  % (11741)------------------------------
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f37,f41,f45,f49,f57,f61,f69,f74,f78,f82,f87,f93,f107,f112,f118,f137,f145])).
% 0.20/0.46  fof(f145,plain,(
% 0.20/0.46    spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_11 | ~spl3_22),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f144])).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    $false | (spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_11 | ~spl3_22)),
% 0.20/0.46    inference(subsumption_resolution,[],[f143,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl3_2 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f143,plain,(
% 0.20/0.46    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | (~spl3_4 | ~spl3_6 | ~spl3_11 | ~spl3_22)),
% 0.20/0.46    inference(forward_demodulation,[],[f142,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl3_6 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f142,plain,(
% 0.20/0.46    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) | (~spl3_4 | ~spl3_11 | ~spl3_22)),
% 0.20/0.46    inference(subsumption_resolution,[],[f141,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f141,plain,(
% 0.20/0.46    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK0)) | (~spl3_11 | ~spl3_22)),
% 0.20/0.46    inference(superposition,[],[f77,f136])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl3_22),
% 0.20/0.46    inference(avatar_component_clause,[],[f135])).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    spl3_22 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl3_11 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    spl3_22 | ~spl3_4 | ~spl3_10 | ~spl3_19),
% 0.20/0.46    inference(avatar_split_clause,[],[f125,f116,f72,f47,f135])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    spl3_10 <=> ! [X1,X0] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    spl3_19 <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | (~spl3_4 | ~spl3_10 | ~spl3_19)),
% 0.20/0.46    inference(subsumption_resolution,[],[f123,f48])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | (~spl3_10 | ~spl3_19)),
% 0.20/0.46    inference(superposition,[],[f117,f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | ~spl3_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f72])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | ~spl3_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f116])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    spl3_19 | ~spl3_17 | ~spl3_18),
% 0.20/0.46    inference(avatar_split_clause,[],[f114,f110,f105,f116])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    spl3_17 <=> r1_tarski(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    spl3_18 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | (~spl3_17 | ~spl3_18)),
% 0.20/0.46    inference(resolution,[],[f111,f106])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    r1_tarski(sK1,sK0) | ~spl3_17),
% 0.20/0.46    inference(avatar_component_clause,[],[f105])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | ~spl3_18),
% 0.20/0.46    inference(avatar_component_clause,[],[f110])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    spl3_18 | ~spl3_4 | ~spl3_6 | ~spl3_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f89,f85,f55,f47,f110])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    spl3_13 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl3_4 | ~spl3_6 | ~spl3_13)),
% 0.20/0.46    inference(forward_demodulation,[],[f88,f56])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl3_4 | ~spl3_13)),
% 0.20/0.46    inference(resolution,[],[f86,f48])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl3_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f85])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    spl3_17 | ~spl3_7 | ~spl3_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f98,f91,f59,f105])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl3_7 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    spl3_14 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    r1_tarski(sK1,sK0) | (~spl3_7 | ~spl3_14)),
% 0.20/0.46    inference(resolution,[],[f92,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl3_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f91])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    spl3_14 | ~spl3_1 | ~spl3_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f83,f80,f35,f91])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    spl3_12 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    r2_hidden(sK1,k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_12)),
% 0.20/0.46    inference(resolution,[],[f81,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f35])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1))) ) | ~spl3_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f80])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl3_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f85])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl3_12 | ~spl3_3 | ~spl3_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f70,f67,f43,f80])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    spl3_3 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl3_9 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1))) ) | (~spl3_3 | ~spl3_9)),
% 0.20/0.46    inference(resolution,[],[f68,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f43])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl3_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl3_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f76])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    spl3_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f72])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl3_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f67])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl3_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f32,f59])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(equality_resolution,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f55])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f47])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f43])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f39])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f18,f35])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (11750)------------------------------
% 0.20/0.46  % (11750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (11750)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (11750)Memory used [KB]: 10618
% 0.20/0.46  % (11750)Time elapsed: 0.060 s
% 0.20/0.46  % (11750)------------------------------
% 0.20/0.46  % (11750)------------------------------
% 0.20/0.46  % (11754)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (11740)Success in time 0.105 s
%------------------------------------------------------------------------------
