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
% DateTime   : Thu Dec  3 13:07:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 158 expanded)
%              Number of leaves         :   16 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 451 expanded)
%              Number of equality atoms :   42 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f40,f45,f50,f57,f62,f74,f78,f88,f93,f98,f105,f116])).

fof(f116,plain,
    ( ~ spl2_1
    | ~ spl2_9
    | spl2_10
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_9
    | spl2_10
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f114,f31])).

fof(f31,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl2_9
    | spl2_10
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f113,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f113,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | ~ spl2_9
    | spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f112,f87])).

fof(f87,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_9
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f112,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f111,f92])).

fof(f92,plain,
    ( ~ v1_partfun1(sK1,k1_xboole_0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_10
  <=> v1_partfun1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f111,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | ~ spl2_12 ),
    inference(superposition,[],[f27,f104])).

fof(f104,plain,
    ( sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_12
  <=> sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f27,plain,(
    ! [X2,X1] :
      ( v1_partfun1(k3_partfun1(X2,k1_xboole_0,X1),k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

% (31469)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (31477)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (31477)Refutation not found, incomplete strategy% (31477)------------------------------
% (31477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31477)Termination reason: Refutation not found, incomplete strategy

% (31477)Memory used [KB]: 6140
% (31477)Time elapsed: 0.002 s
% (31477)------------------------------
% (31477)------------------------------
% (31474)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (31463)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (31468)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (31483)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (31471)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).

fof(f105,plain,
    ( spl2_12
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f82,f67,f59,f102])).

fof(f59,plain,
    ( spl2_6
  <=> sK1 = k3_partfun1(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( spl2_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f82,plain,
    ( sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f61,f69])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f61,plain,
    ( sK1 = k3_partfun1(sK1,sK0,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f98,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f80,f67,f42,f95])).

fof(f42,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f44,f69])).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f93,plain,
    ( ~ spl2_10
    | ~ spl2_7
    | spl2_8 ),
    inference(avatar_split_clause,[],[f83,f71,f67,f90])).

fof(f71,plain,
    ( spl2_8
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f83,plain,
    ( ~ v1_partfun1(sK1,k1_xboole_0)
    | ~ spl2_7
    | spl2_8 ),
    inference(backward_demodulation,[],[f72,f69])).

fof(f72,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f88,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f79,f67,f37,f85])).

fof(f37,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f39,f69])).

fof(f39,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f78,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f76,f56])).

fof(f56,plain,
    ( k1_tarski(sK1) != k5_partfun1(sK0,sK0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_5
  <=> k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f76,plain,
    ( k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f75,f44])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | k1_tarski(sK1) = k5_partfun1(sK0,X0,sK1) )
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(resolution,[],[f73,f33])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK1,X0)
        | k1_tarski(sK1) = k5_partfun1(X0,X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_1 ),
    inference(resolution,[],[f31,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(f73,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,
    ( spl2_7
    | spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f65,f59,f42,f37,f29,f71,f67])).

fof(f65,plain,
    ( v1_partfun1(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f64,f61])).

fof(f64,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f63,f39])).

fof(f63,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f35,f44])).

fof(f35,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_2(sK1,X4,X5)
        | k1_xboole_0 = X5
        | v1_partfun1(k3_partfun1(sK1,X4,X5),X4) )
    | ~ spl2_1 ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f51,f42,f29,f59])).

fof(f51,plain,
    ( sK1 = k3_partfun1(sK1,sK0,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f34,f44])).

fof(f34,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | sK1 = k3_partfun1(sK1,X2,X3) )
    | ~ spl2_1 ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

fof(f57,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f52,f47,f42,f29,f54])).

fof(f47,plain,
    ( spl2_4
  <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f52,plain,
    ( k1_tarski(sK1) != k5_partfun1(sK0,sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | spl2_4 ),
    inference(backward_demodulation,[],[f49,f51])).

fof(f49,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f50,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

fof(f45,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (31490)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (31482)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (31462)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (31462)Refutation not found, incomplete strategy% (31462)------------------------------
% 0.21/0.51  % (31462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31462)Memory used [KB]: 1663
% 0.21/0.51  % (31462)Time elapsed: 0.100 s
% 0.21/0.51  % (31462)------------------------------
% 0.21/0.51  % (31462)------------------------------
% 0.21/0.51  % (31482)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f32,f40,f45,f50,f57,f62,f74,f78,f88,f93,f98,f105,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_9 | spl2_10 | ~spl2_11 | ~spl2_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    $false | (~spl2_1 | ~spl2_9 | spl2_10 | ~spl2_11 | ~spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f114,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_funct_1(sK1) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    spl2_1 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | (~spl2_9 | spl2_10 | ~spl2_11 | ~spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl2_11 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1) | (~spl2_9 | spl2_10 | ~spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl2_9 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1) | (spl2_10 | ~spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v1_partfun1(sK1,k1_xboole_0) | spl2_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl2_10 <=> v1_partfun1(sK1,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    v1_partfun1(sK1,k1_xboole_0) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1) | ~spl2_12),
% 0.21/0.51    inference(superposition,[],[f27,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl2_12 <=> sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X1] : (v1_partfun1(k3_partfun1(X2,k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | v1_partfun1(k3_partfun1(X2,X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_partfun1(k3_partfun1(X2,X0,X1),X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_partfun1(k3_partfun1(X2,X0,X1),X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  % (31469)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (31477)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (31477)Refutation not found, incomplete strategy% (31477)------------------------------
% 0.21/0.52  % (31477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31477)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31477)Memory used [KB]: 6140
% 0.21/0.52  % (31477)Time elapsed: 0.002 s
% 0.21/0.52  % (31477)------------------------------
% 0.21/0.52  % (31477)------------------------------
% 0.21/0.52  % (31474)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (31463)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (31468)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (31483)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (31471)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl2_12 | ~spl2_6 | ~spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f82,f67,f59,f102])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl2_6 <=> sK1 = k3_partfun1(sK1,sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl2_7 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_6 | ~spl2_7)),
% 0.21/0.52    inference(backward_demodulation,[],[f61,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    sK1 = k3_partfun1(sK1,sK0,sK0) | ~spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl2_11 | ~spl2_3 | ~spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f80,f67,f42,f95])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_3 | ~spl2_7)),
% 0.21/0.52    inference(backward_demodulation,[],[f44,f69])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f42])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~spl2_10 | ~spl2_7 | spl2_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f83,f71,f67,f90])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl2_8 <=> v1_partfun1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~v1_partfun1(sK1,k1_xboole_0) | (~spl2_7 | spl2_8)),
% 0.21/0.52    inference(backward_demodulation,[],[f72,f69])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ~v1_partfun1(sK1,sK0) | spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl2_9 | ~spl2_2 | ~spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f79,f67,f37,f85])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_2 | ~spl2_7)),
% 0.21/0.52    inference(backward_demodulation,[],[f39,f69])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f37])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_3 | spl2_5 | ~spl2_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    $false | (~spl2_1 | ~spl2_3 | spl2_5 | ~spl2_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    k1_tarski(sK1) != k5_partfun1(sK0,sK0,sK1) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl2_5 <=> k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_8)),
% 0.21/0.52    inference(resolution,[],[f75,f44])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_tarski(sK1) = k5_partfun1(sK0,X0,sK1)) ) | (~spl2_1 | ~spl2_8)),
% 0.21/0.52    inference(resolution,[],[f73,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_partfun1(sK1,X0) | k1_tarski(sK1) = k5_partfun1(X0,X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f31,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    v1_partfun1(sK1,sK0) | ~spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl2_7 | spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f65,f59,f42,f37,f29,f71,f67])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v1_partfun1(sK1,sK0) | k1_xboole_0 = sK0 | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f64,f61])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f39])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0) | (~spl2_1 | ~spl2_3)),
% 0.21/0.52    inference(resolution,[],[f35,f44])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK1,X4,X5) | k1_xboole_0 = X5 | v1_partfun1(k3_partfun1(sK1,X4,X5),X4)) ) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f31,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(k3_partfun1(X2,X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl2_6 | ~spl2_1 | ~spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f42,f29,f59])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    sK1 = k3_partfun1(sK1,sK0,sK0) | (~spl2_1 | ~spl2_3)),
% 0.21/0.52    inference(resolution,[],[f34,f44])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | sK1 = k3_partfun1(sK1,X2,X3)) ) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f31,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_partfun1(X2,X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~spl2_5 | ~spl2_1 | ~spl2_3 | spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f47,f42,f29,f54])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl2_4 <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    k1_tarski(sK1) != k5_partfun1(sK0,sK0,sK1) | (~spl2_1 | ~spl2_3 | spl2_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f49,f51])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) | spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f47])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f16,f29])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (31482)------------------------------
% 0.21/0.52  % (31482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31482)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (31482)Memory used [KB]: 10746
% 0.21/0.52  % (31482)Time elapsed: 0.091 s
% 0.21/0.52  % (31482)------------------------------
% 0.21/0.52  % (31482)------------------------------
% 0.21/0.52  % (31464)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31461)Success in time 0.164 s
%------------------------------------------------------------------------------
