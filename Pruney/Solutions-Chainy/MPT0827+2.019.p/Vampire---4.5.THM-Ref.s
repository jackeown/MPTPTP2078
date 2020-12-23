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
% DateTime   : Thu Dec  3 12:56:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 183 expanded)
%              Number of leaves         :   30 (  84 expanded)
%              Depth                    :    7
%              Number of atoms          :  330 ( 557 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f55,f59,f63,f67,f71,f75,f79,f87,f91,f106,f110,f131,f143,f171,f183,f202,f209,f218,f225])).

fof(f225,plain,
    ( spl4_2
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl4_2
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f223,f142])).

fof(f142,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_22
  <=> r1_tarski(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f223,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl4_2
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f40,f217])).

fof(f217,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl4_34
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f40,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_2
  <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f218,plain,
    ( spl4_34
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f212,f89,f48,f215])).

fof(f48,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

% (15929)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f89,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f212,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f209,plain,
    ( spl4_1
    | ~ spl4_29
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl4_1
    | ~ spl4_29
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f207,f182])).

fof(f182,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_29
  <=> r1_tarski(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f207,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_1
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f36,f201])).

fof(f201,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_32
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f36,plain,
    ( ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

% (15934)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f34,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f202,plain,
    ( spl4_32
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f196,f85,f48,f199])).

fof(f85,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f196,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(resolution,[],[f86,f50])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f183,plain,
    ( spl4_29
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f178,f169,f103,f43,f180])).

fof(f43,plain,
    ( spl4_3
  <=> r1_tarski(k6_relat_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f103,plain,
    ( spl4_16
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f169,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k1_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f178,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f177,f105])).

fof(f105,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f177,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(resolution,[],[f170,f45])).

fof(f45,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        | r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( spl4_27
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f167,f108,f65,f57,f169])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f108,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k1_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f160,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | v1_relat_1(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f108])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k1_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(superposition,[],[f66,f58])).

fof(f58,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f143,plain,
    ( spl4_22
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f138,f129,f103,f43,f140])).

fof(f129,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k2_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f138,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f137,f105])).

fof(f137,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_20 ),
    inference(resolution,[],[f130,f45])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        | r1_tarski(X0,k2_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( spl4_20
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f127,f108,f61,f53,f129])).

fof(f53,plain,
    ( spl4_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f61,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k2_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f120,f109])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k2_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f62,f54])).

fof(f54,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f110,plain,
    ( spl4_17
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f100,f77,f69,f108])).

fof(f69,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f77,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(resolution,[],[f70,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f106,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f101,f73,f69,f48,f103])).

fof(f73,plain,
    ( spl4_10
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f101,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f99,f74])).

fof(f74,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f99,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(resolution,[],[f70,f50])).

fof(f91,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f32,f89])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f87,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f31,f85])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f79,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f75,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

% (15933)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f67,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f63,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f55,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f46,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f22,f38,f34])).

fof(f22,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:51:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (15938)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (15938)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f226,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f41,f46,f51,f55,f59,f63,f67,f71,f75,f79,f87,f91,f106,f110,f131,f143,f171,f183,f202,f209,f218,f225])).
% 0.22/0.43  fof(f225,plain,(
% 0.22/0.43    spl4_2 | ~spl4_22 | ~spl4_34),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.43  fof(f224,plain,(
% 0.22/0.43    $false | (spl4_2 | ~spl4_22 | ~spl4_34)),
% 0.22/0.43    inference(subsumption_resolution,[],[f223,f142])).
% 0.22/0.43  fof(f142,plain,(
% 0.22/0.43    r1_tarski(sK2,k2_relat_1(sK3)) | ~spl4_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f140])).
% 0.22/0.43  fof(f140,plain,(
% 0.22/0.43    spl4_22 <=> r1_tarski(sK2,k2_relat_1(sK3))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.43  fof(f223,plain,(
% 0.22/0.43    ~r1_tarski(sK2,k2_relat_1(sK3)) | (spl4_2 | ~spl4_34)),
% 0.22/0.43    inference(backward_demodulation,[],[f40,f217])).
% 0.22/0.43  fof(f217,plain,(
% 0.22/0.43    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl4_34),
% 0.22/0.43    inference(avatar_component_clause,[],[f215])).
% 0.22/0.43  fof(f215,plain,(
% 0.22/0.43    spl4_34 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | spl4_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl4_2 <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.43  fof(f218,plain,(
% 0.22/0.43    spl4_34 | ~spl4_4 | ~spl4_14),
% 0.22/0.43    inference(avatar_split_clause,[],[f212,f89,f48,f215])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.43  % (15929)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    spl4_14 <=> ! [X1,X0,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.43  fof(f212,plain,(
% 0.22/0.43    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | (~spl4_4 | ~spl4_14)),
% 0.22/0.43    inference(resolution,[],[f90,f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl4_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f89])).
% 0.22/0.43  fof(f209,plain,(
% 0.22/0.43    spl4_1 | ~spl4_29 | ~spl4_32),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f208])).
% 0.22/0.43  fof(f208,plain,(
% 0.22/0.43    $false | (spl4_1 | ~spl4_29 | ~spl4_32)),
% 0.22/0.43    inference(subsumption_resolution,[],[f207,f182])).
% 0.22/0.43  fof(f182,plain,(
% 0.22/0.43    r1_tarski(sK2,k1_relat_1(sK3)) | ~spl4_29),
% 0.22/0.43    inference(avatar_component_clause,[],[f180])).
% 0.22/0.43  fof(f180,plain,(
% 0.22/0.43    spl4_29 <=> r1_tarski(sK2,k1_relat_1(sK3))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.43  fof(f207,plain,(
% 0.22/0.43    ~r1_tarski(sK2,k1_relat_1(sK3)) | (spl4_1 | ~spl4_32)),
% 0.22/0.43    inference(backward_demodulation,[],[f36,f201])).
% 0.22/0.43  fof(f201,plain,(
% 0.22/0.43    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_32),
% 0.22/0.43    inference(avatar_component_clause,[],[f199])).
% 0.22/0.43  fof(f199,plain,(
% 0.22/0.43    spl4_32 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) | spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  % (15934)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl4_1 <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f202,plain,(
% 0.22/0.43    spl4_32 | ~spl4_4 | ~spl4_13),
% 0.22/0.43    inference(avatar_split_clause,[],[f196,f85,f48,f199])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    spl4_13 <=> ! [X1,X0,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.43  fof(f196,plain,(
% 0.22/0.43    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | (~spl4_4 | ~spl4_13)),
% 0.22/0.43    inference(resolution,[],[f86,f50])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) ) | ~spl4_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f85])).
% 0.22/0.43  fof(f183,plain,(
% 0.22/0.43    spl4_29 | ~spl4_3 | ~spl4_16 | ~spl4_27),
% 0.22/0.43    inference(avatar_split_clause,[],[f178,f169,f103,f43,f180])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl4_3 <=> r1_tarski(k6_relat_1(sK2),sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    spl4_16 <=> v1_relat_1(sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.43  fof(f169,plain,(
% 0.22/0.43    spl4_27 <=> ! [X1,X0] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.43  fof(f178,plain,(
% 0.22/0.43    r1_tarski(sK2,k1_relat_1(sK3)) | (~spl4_3 | ~spl4_16 | ~spl4_27)),
% 0.22/0.43    inference(subsumption_resolution,[],[f177,f105])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    v1_relat_1(sK3) | ~spl4_16),
% 0.22/0.43    inference(avatar_component_clause,[],[f103])).
% 0.22/0.43  fof(f177,plain,(
% 0.22/0.43    r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_27)),
% 0.22/0.43    inference(resolution,[],[f170,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    r1_tarski(k6_relat_1(sK2),sK3) | ~spl4_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f43])).
% 0.22/0.43  fof(f170,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_27),
% 0.22/0.43    inference(avatar_component_clause,[],[f169])).
% 0.22/0.43  fof(f171,plain,(
% 0.22/0.43    spl4_27 | ~spl4_6 | ~spl4_8 | ~spl4_17),
% 0.22/0.43    inference(avatar_split_clause,[],[f167,f108,f65,f57,f169])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl4_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl4_8 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.43  fof(f108,plain,(
% 0.22/0.43    spl4_17 <=> ! [X1,X0] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | (~spl4_6 | ~spl4_8 | ~spl4_17)),
% 0.22/0.43    inference(subsumption_resolution,[],[f160,f109])).
% 0.22/0.43  fof(f109,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) ) | ~spl4_17),
% 0.22/0.43    inference(avatar_component_clause,[],[f108])).
% 0.22/0.43  fof(f160,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl4_6 | ~spl4_8)),
% 0.22/0.43    inference(superposition,[],[f66,f58])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f57])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f65])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    spl4_22 | ~spl4_3 | ~spl4_16 | ~spl4_20),
% 0.22/0.43    inference(avatar_split_clause,[],[f138,f129,f103,f43,f140])).
% 0.22/0.43  fof(f129,plain,(
% 0.22/0.43    spl4_20 <=> ! [X1,X0] : (r1_tarski(X0,k2_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.43  fof(f138,plain,(
% 0.22/0.43    r1_tarski(sK2,k2_relat_1(sK3)) | (~spl4_3 | ~spl4_16 | ~spl4_20)),
% 0.22/0.43    inference(subsumption_resolution,[],[f137,f105])).
% 0.22/0.43  fof(f137,plain,(
% 0.22/0.43    r1_tarski(sK2,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_20)),
% 0.22/0.43    inference(resolution,[],[f130,f45])).
% 0.22/0.43  fof(f130,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_20),
% 0.22/0.43    inference(avatar_component_clause,[],[f129])).
% 0.22/0.43  fof(f131,plain,(
% 0.22/0.43    spl4_20 | ~spl4_5 | ~spl4_7 | ~spl4_17),
% 0.22/0.43    inference(avatar_split_clause,[],[f127,f108,f61,f53,f129])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl4_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl4_7 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.43  fof(f127,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | (~spl4_5 | ~spl4_7 | ~spl4_17)),
% 0.22/0.43    inference(subsumption_resolution,[],[f120,f109])).
% 0.22/0.43  fof(f120,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl4_5 | ~spl4_7)),
% 0.22/0.43    inference(superposition,[],[f62,f54])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f61])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    spl4_17 | ~spl4_9 | ~spl4_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f100,f77,f69,f108])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl4_9 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl4_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) ) | (~spl4_9 | ~spl4_11)),
% 0.22/0.43    inference(resolution,[],[f70,f78])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f77])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f69])).
% 0.22/0.43  fof(f106,plain,(
% 0.22/0.43    spl4_16 | ~spl4_4 | ~spl4_9 | ~spl4_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f101,f73,f69,f48,f103])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    spl4_10 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    v1_relat_1(sK3) | (~spl4_4 | ~spl4_9 | ~spl4_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f99,f74])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl4_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f73])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl4_4 | ~spl4_9)),
% 0.22/0.44    inference(resolution,[],[f70,f50])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    spl4_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f89])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    spl4_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f31,f85])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl4_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f77])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.44    inference(nnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    spl4_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f73])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.44  % (15933)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl4_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f69])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl4_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f65])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl4_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f61])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl4_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f57])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl4_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f53])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    spl4_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f8])).
% 0.22/0.44  fof(f8,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl4_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f43])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    r1_tarski(k6_relat_1(sK2),sK3)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ~spl4_1 | ~spl4_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f38,f34])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (15938)------------------------------
% 0.22/0.44  % (15938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (15938)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (15938)Memory used [KB]: 6140
% 0.22/0.44  % (15938)Time elapsed: 0.030 s
% 0.22/0.44  % (15938)------------------------------
% 0.22/0.44  % (15938)------------------------------
% 0.22/0.44  % (15924)Success in time 0.078 s
%------------------------------------------------------------------------------
