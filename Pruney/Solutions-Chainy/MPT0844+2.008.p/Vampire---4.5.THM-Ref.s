%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 160 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  276 ( 432 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f59,f63,f71,f75,f83,f87,f91,f97,f104,f116,f123,f129,f140,f146,f168,f193,f196])).

fof(f196,plain,
    ( spl4_1
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl4_1
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f194,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_26
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f194,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_1
    | ~ spl4_30 ),
    inference(superposition,[],[f40,f192])).

fof(f192,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_30
  <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f40,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f193,plain,
    ( spl4_30
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f189,f89,f48,f191])).

fof(f48,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( spl4_13
  <=> ! [X1,X3,X0,X2] :
        ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f189,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f90,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f168,plain,
    ( spl4_26
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f162,f144,f94,f165])).

fof(f94,plain,
    ( spl4_14
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f144,plain,
    ( spl4_22
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f162,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(resolution,[],[f145,f96])).

fof(f96,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl4_22
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f141,f138,f127,f144])).

fof(f127,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(k1_relat_1(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f138,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK3),X0)
        | k1_xboole_0 = k7_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f141,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(resolution,[],[f139,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK3),X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK3),X0)
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl4_21
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f136,f101,f61,f138])).

fof(f61,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f101,plain,
    ( spl4_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK3),X0)
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(resolution,[],[f62,f103])).

fof(f103,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f129,plain,
    ( spl4_19
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f125,f120,f85,f127])).

fof(f85,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f120,plain,
    ( spl4_18
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(k1_relat_1(sK3),X0) )
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(resolution,[],[f86,f122])).

fof(f122,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f123,plain,
    ( spl4_18
    | ~ spl4_5
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f118,f113,f101,f57,f120])).

fof(f57,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f113,plain,
    ( spl4_17
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f118,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_5
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f117,f103])).

fof(f117,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(resolution,[],[f115,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f115,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( spl4_17
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f111,f81,f48,f113])).

fof(f81,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f111,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(resolution,[],[f82,f50])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f104,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f99,f73,f48,f101])).

% (26493)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f73,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f99,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f74,f50])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f97,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f92,f69,f43,f94])).

fof(f43,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f69,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f92,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f91,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f87,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f35,f85])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f83,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f75,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f71,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f63,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f59,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f38])).

fof(f26,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (26497)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (26491)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.42  % (26494)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (26494)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f197,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f41,f46,f51,f59,f63,f71,f75,f83,f87,f91,f97,f104,f116,f123,f129,f140,f146,f168,f193,f196])).
% 0.21/0.43  fof(f196,plain,(
% 0.21/0.43    spl4_1 | ~spl4_26 | ~spl4_30),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f195])).
% 0.21/0.43  fof(f195,plain,(
% 0.21/0.43    $false | (spl4_1 | ~spl4_26 | ~spl4_30)),
% 0.21/0.43    inference(subsumption_resolution,[],[f194,f167])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    k1_xboole_0 = k7_relat_1(sK3,sK1) | ~spl4_26),
% 0.21/0.43    inference(avatar_component_clause,[],[f165])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    spl4_26 <=> k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.43  fof(f194,plain,(
% 0.21/0.43    k1_xboole_0 != k7_relat_1(sK3,sK1) | (spl4_1 | ~spl4_30)),
% 0.21/0.43    inference(superposition,[],[f40,f192])).
% 0.21/0.43  fof(f192,plain,(
% 0.21/0.43    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)) ) | ~spl4_30),
% 0.21/0.43    inference(avatar_component_clause,[],[f191])).
% 0.21/0.43  fof(f191,plain,(
% 0.21/0.43    spl4_30 <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl4_1 <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f193,plain,(
% 0.21/0.43    spl4_30 | ~spl4_3 | ~spl4_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f189,f89,f48,f191])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    spl4_13 <=> ! [X1,X3,X0,X2] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)) ) | (~spl4_3 | ~spl4_13)),
% 0.21/0.43    inference(resolution,[],[f90,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f48])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) ) | ~spl4_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f89])).
% 0.21/0.43  fof(f168,plain,(
% 0.21/0.43    spl4_26 | ~spl4_14 | ~spl4_22),
% 0.21/0.43    inference(avatar_split_clause,[],[f162,f144,f94,f165])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    spl4_14 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.43  fof(f144,plain,(
% 0.21/0.43    spl4_22 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0) | ~r1_xboole_0(sK2,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    k1_xboole_0 = k7_relat_1(sK3,sK1) | (~spl4_14 | ~spl4_22)),
% 0.21/0.43    inference(resolution,[],[f145,f96])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK1) | ~spl4_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f94])).
% 0.21/0.43  fof(f145,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl4_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f144])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    spl4_22 | ~spl4_19 | ~spl4_21),
% 0.21/0.43    inference(avatar_split_clause,[],[f141,f138,f127,f144])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    spl4_19 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(k1_relat_1(sK3),X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    spl4_21 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK3),X0) | k1_xboole_0 = k7_relat_1(sK3,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.43  fof(f141,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | (~spl4_19 | ~spl4_21)),
% 0.21/0.43    inference(resolution,[],[f139,f128])).
% 0.21/0.43  fof(f128,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK3),X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl4_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f127])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK3),X0) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl4_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f138])).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    spl4_21 | ~spl4_6 | ~spl4_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f136,f101,f61,f138])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl4_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    spl4_15 <=> v1_relat_1(sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK3),X0) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | (~spl4_6 | ~spl4_15)),
% 0.21/0.43    inference(resolution,[],[f62,f103])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    v1_relat_1(sK3) | ~spl4_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f101])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0) ) | ~spl4_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f61])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    spl4_19 | ~spl4_12 | ~spl4_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f125,f120,f85,f127])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl4_12 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    spl4_18 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(k1_relat_1(sK3),X0)) ) | (~spl4_12 | ~spl4_18)),
% 0.21/0.43    inference(resolution,[],[f86,f122])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    r1_tarski(k1_relat_1(sK3),sK2) | ~spl4_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f120])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl4_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f85])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    spl4_18 | ~spl4_5 | ~spl4_15 | ~spl4_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f118,f113,f101,f57,f120])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl4_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    spl4_17 <=> v4_relat_1(sK3,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    r1_tarski(k1_relat_1(sK3),sK2) | (~spl4_5 | ~spl4_15 | ~spl4_17)),
% 0.21/0.43    inference(subsumption_resolution,[],[f117,f103])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | (~spl4_5 | ~spl4_17)),
% 0.21/0.43    inference(resolution,[],[f115,f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl4_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    v4_relat_1(sK3,sK2) | ~spl4_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f113])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    spl4_17 | ~spl4_3 | ~spl4_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f111,f81,f48,f113])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl4_11 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    v4_relat_1(sK3,sK2) | (~spl4_3 | ~spl4_11)),
% 0.21/0.43    inference(resolution,[],[f82,f50])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f81])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    spl4_15 | ~spl4_3 | ~spl4_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f99,f73,f48,f101])).
% 0.21/0.43  % (26493)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl4_9 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    v1_relat_1(sK3) | (~spl4_3 | ~spl4_9)),
% 0.21/0.43    inference(resolution,[],[f74,f50])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f73])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    spl4_14 | ~spl4_2 | ~spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f92,f69,f43,f94])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl4_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl4_8 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK1) | (~spl4_2 | ~spl4_8)),
% 0.21/0.43    inference(resolution,[],[f70,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK2) | ~spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f43])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f69])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl4_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f36,f89])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f85])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl4_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f81])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl4_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f73])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f69])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f48])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f43])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f38])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (26494)------------------------------
% 0.21/0.43  % (26494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (26494)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (26494)Memory used [KB]: 10618
% 0.21/0.43  % (26494)Time elapsed: 0.008 s
% 0.21/0.43  % (26494)------------------------------
% 0.21/0.43  % (26494)------------------------------
% 0.21/0.43  % (26488)Success in time 0.077 s
%------------------------------------------------------------------------------
