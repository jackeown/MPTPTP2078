%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 171 expanded)
%              Number of leaves         :   29 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  275 ( 446 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f71,f75,f79,f84,f90,f119,f130,f135,f141,f147,f165,f173,f196,f206])).

% (17622)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f206,plain,
    ( ~ spl4_20
    | spl4_22
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl4_20
    | spl4_22
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f202,f140])).

fof(f140,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_22
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f202,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_20
    | ~ spl4_32 ),
    inference(superposition,[],[f129,f195])).

fof(f195,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_32
  <=> ! [X0] : k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f129,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK1),sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_20
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f196,plain,
    ( spl4_32
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f192,f171,f163,f57,f194])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f163,plain,
    ( spl4_26
  <=> ! [X4] : v4_relat_1(k7_relat_1(sK3,X4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f171,plain,
    ( spl4_28
  <=> ! [X6] : v1_relat_1(k7_relat_1(sK3,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f192,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2)
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f190,f172])).

fof(f172,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f171])).

fof(f190,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(resolution,[],[f164,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f164,plain,
    ( ! [X4] : v4_relat_1(k7_relat_1(sK3,X4),sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f173,plain,
    ( spl4_28
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f152,f145,f82,f171])).

fof(f82,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f145,plain,
    ( spl4_23
  <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f152,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(resolution,[],[f146,f83])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f146,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f145])).

fof(f165,plain,
    ( spl4_26
    | ~ spl4_9
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f150,f145,f69,f163])).

fof(f69,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f150,plain,
    ( ! [X4] : v4_relat_1(k7_relat_1(sK3,X4),sK2)
    | ~ spl4_9
    | ~ spl4_23 ),
    inference(resolution,[],[f146,f70])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f147,plain,
    ( spl4_23
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f143,f133,f77,f44,f145])).

fof(f44,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f77,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f133,plain,
    ( spl4_21
  <=> ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f143,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f142,f134])).

fof(f134,plain,
    ( ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f133])).

fof(f142,plain,
    ( ! [X0] : m1_subset_1(k5_relset_1(sK2,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f78,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f141,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f136,f133,f34,f138])).

fof(f34,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f136,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_1
    | ~ spl4_21 ),
    inference(superposition,[],[f36,f134])).

fof(f36,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f135,plain,
    ( spl4_21
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f131,f73,f44,f133])).

fof(f73,plain,
    ( spl4_10
  <=> ! [X1,X3,X0,X2] :
        ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f131,plain,
    ( ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f74,f46])).

fof(f74,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f130,plain,
    ( spl4_20
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f121,f117,f87,f127])).

fof(f87,plain,
    ( spl4_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f117,plain,
    ( spl4_18
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK1),sK2)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f121,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK1),sK2)
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(resolution,[],[f118,f89])).

fof(f89,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK1),sK2) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f115,f61,f39,f117])).

fof(f39,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f61,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f115,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK1),sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
        | ~ v1_relat_1(X2) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f90,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f85,f82,f44,f87])).

fof(f85,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f83,f46])).

fof(f84,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f80,f53,f49,f82])).

fof(f49,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f53,plain,
    ( spl4_5
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f79,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).

fof(f75,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f63,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f55,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f51,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:29:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (17621)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.46  % (17619)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.46  % (17624)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.46  % (17621)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f207,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f71,f75,f79,f84,f90,f119,f130,f135,f141,f147,f165,f173,f196,f206])).
% 0.21/0.46  % (17622)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    ~spl4_20 | spl4_22 | ~spl4_32),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    $false | (~spl4_20 | spl4_22 | ~spl4_32)),
% 0.21/0.46    inference(subsumption_resolution,[],[f202,f140])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    k1_xboole_0 != k7_relat_1(sK3,sK1) | spl4_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f138])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    spl4_22 <=> k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    k1_xboole_0 = k7_relat_1(sK3,sK1) | (~spl4_20 | ~spl4_32)),
% 0.21/0.46    inference(superposition,[],[f129,f195])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2)) ) | ~spl4_32),
% 0.21/0.46    inference(avatar_component_clause,[],[f194])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    spl4_32 <=> ! [X0] : k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK1),sK2) | ~spl4_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f127])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    spl4_20 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.46  fof(f196,plain,(
% 0.21/0.46    spl4_32 | ~spl4_6 | ~spl4_26 | ~spl4_28),
% 0.21/0.46    inference(avatar_split_clause,[],[f192,f171,f163,f57,f194])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl4_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    spl4_26 <=> ! [X4] : v4_relat_1(k7_relat_1(sK3,X4),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    spl4_28 <=> ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.46  fof(f192,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2)) ) | (~spl4_6 | ~spl4_26 | ~spl4_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f190,f172])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) ) | ~spl4_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f171])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),sK2) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl4_6 | ~spl4_26)),
% 0.21/0.46    inference(resolution,[],[f164,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f57])).
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    ( ! [X4] : (v4_relat_1(k7_relat_1(sK3,X4),sK2)) ) | ~spl4_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f163])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    spl4_28 | ~spl4_12 | ~spl4_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f152,f145,f82,f171])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl4_12 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    spl4_23 <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) ) | (~spl4_12 | ~spl4_23)),
% 0.21/0.46    inference(resolution,[],[f146,f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | ~spl4_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f82])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f145])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    spl4_26 | ~spl4_9 | ~spl4_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f150,f145,f69,f163])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl4_9 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    ( ! [X4] : (v4_relat_1(k7_relat_1(sK3,X4),sK2)) ) | (~spl4_9 | ~spl4_23)),
% 0.21/0.46    inference(resolution,[],[f146,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f69])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    spl4_23 | ~spl4_3 | ~spl4_11 | ~spl4_21),
% 0.21/0.46    inference(avatar_split_clause,[],[f143,f133,f77,f44,f145])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl4_11 <=> ! [X1,X3,X0,X2] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl4_21 <=> ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | (~spl4_3 | ~spl4_11 | ~spl4_21)),
% 0.21/0.46    inference(forward_demodulation,[],[f142,f134])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | ~spl4_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f133])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k5_relset_1(sK2,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | (~spl4_3 | ~spl4_11)),
% 0.21/0.46    inference(resolution,[],[f78,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    ~spl4_22 | spl4_1 | ~spl4_21),
% 0.21/0.46    inference(avatar_split_clause,[],[f136,f133,f34,f138])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl4_1 <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    k1_xboole_0 != k7_relat_1(sK3,sK1) | (spl4_1 | ~spl4_21)),
% 0.21/0.46    inference(superposition,[],[f36,f134])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    spl4_21 | ~spl4_3 | ~spl4_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f131,f73,f44,f133])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl4_10 <=> ! [X1,X3,X0,X2] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl4_3 | ~spl4_10)),
% 0.21/0.46    inference(resolution,[],[f74,f46])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) ) | ~spl4_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    spl4_20 | ~spl4_13 | ~spl4_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f121,f117,f87,f127])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl4_13 <=> v1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl4_18 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK1),sK2) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK1),sK2) | (~spl4_13 | ~spl4_18)),
% 0.21/0.46    inference(resolution,[],[f118,f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    v1_relat_1(sK3) | ~spl4_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f87])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK1),sK2)) ) | ~spl4_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f117])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    spl4_18 | ~spl4_2 | ~spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f115,f61,f39,f117])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl4_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_7 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK1),sK2) | ~v1_relat_1(X0)) ) | (~spl4_2 | ~spl4_7)),
% 0.21/0.46    inference(resolution,[],[f62,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    r1_xboole_0(sK1,sK2) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~v1_relat_1(X2)) ) | ~spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f61])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    spl4_13 | ~spl4_3 | ~spl4_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f85,f82,f44,f87])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    v1_relat_1(sK3) | (~spl4_3 | ~spl4_12)),
% 0.21/0.46    inference(resolution,[],[f83,f46])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl4_12 | ~spl4_4 | ~spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f80,f53,f49,f82])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl4_4 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl4_5 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | (~spl4_4 | ~spl4_5)),
% 0.21/0.46    inference(resolution,[],[f50,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f53])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) ) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl4_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f77])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl4_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f73])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl4_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f69])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f61])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f49])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f39])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    r1_xboole_0(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f34])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (17621)------------------------------
% 0.21/0.46  % (17621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (17621)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (17621)Memory used [KB]: 10618
% 0.21/0.46  % (17621)Time elapsed: 0.006 s
% 0.21/0.46  % (17621)------------------------------
% 0.21/0.46  % (17621)------------------------------
% 0.21/0.47  % (17612)Success in time 0.1 s
%------------------------------------------------------------------------------
