%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 208 expanded)
%              Number of leaves         :   30 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  380 ( 664 expanded)
%              Number of equality atoms :   67 ( 103 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f82,f86,f92,f107,f111,f115,f122,f129,f150,f165,f184,f189,f197,f344,f425])).

fof(f425,plain,
    ( spl6_17
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | spl6_17
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f343,f411])).

fof(f411,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl6_17 ),
    inference(subsumption_resolution,[],[f407,f149])).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f407,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f390,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f390,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f350,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f350,plain,(
    ! [X1] :
      ( r2_hidden(sK4(X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f343,plain,
    ( v1_xboole_0(sK5)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl6_39
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f344,plain,(
    spl6_39 ),
    inference(avatar_split_clause,[],[f48,f342])).

fof(f48,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

% (5607)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f197,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | spl6_23 ),
    inference(subsumption_resolution,[],[f195,f188])).

fof(f188,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_23
  <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f195,plain,
    ( k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(resolution,[],[f194,f81])).

fof(f81,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_5
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(superposition,[],[f118,f162])).

fof(f162,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_20
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f117,f63])).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f116,f106])).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f114,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f114,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_10
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f189,plain,
    ( ~ spl6_23
    | spl6_9
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f185,f182,f109,f187])).

fof(f109,plain,
    ( spl6_9
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f182,plain,
    ( spl6_22
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f185,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl6_9
    | ~ spl6_22 ),
    inference(superposition,[],[f110,f183])).

fof(f183,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f110,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f184,plain,
    ( spl6_22
    | ~ spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f179,f90,f84,f74,f70,f62,f182])).

fof(f70,plain,
    ( spl6_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f74,plain,
    ( spl6_4
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f84,plain,
    ( spl6_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f90,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f179,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(resolution,[],[f103,f75])).

fof(f75,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f102,f71])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f102,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f101,f85])).

fof(f85,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f98,f63])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_7 ),
    inference(resolution,[],[f91,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f165,plain,
    ( spl6_20
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f163,f124,f120,f161])).

fof(f120,plain,
    ( spl6_11
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f124,plain,
    ( spl6_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f163,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(superposition,[],[f125,f121])).

fof(f121,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f125,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f150,plain,
    ( ~ spl6_17
    | spl6_2
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f133,f127,f66,f148])).

fof(f66,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f127,plain,
    ( spl6_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f133,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_2
    | ~ spl6_13 ),
    inference(superposition,[],[f67,f128])).

fof(f128,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f129,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f100,f90,f84,f127,f124])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f97,f85])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f122,plain,
    ( spl6_11
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f95,f90,f120])).

fof(f95,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f91,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,
    ( spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f94,f90,f113])).

fof(f94,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f111,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f33,f109])).

fof(f33,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

% (5616)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f107,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f93,f90,f105])).

fof(f93,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f35,f84])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,
    ( spl6_5
    | spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f78,f74,f70,f80])).

fof(f78,plain,
    ( r2_hidden(sK3,sK0)
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f77,f71])).

fof(f77,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK3,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f75,f50])).

fof(f76,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f38,f70])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (5600)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (5606)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (5611)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (5610)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (5602)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (5605)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (5601)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (5615)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (5600)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (5611)Refutation not found, incomplete strategy% (5611)------------------------------
% 0.20/0.49  % (5611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f426,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f82,f86,f92,f107,f111,f115,f122,f129,f150,f165,f184,f189,f197,f344,f425])).
% 0.20/0.49  fof(f425,plain,(
% 0.20/0.49    spl6_17 | ~spl6_39),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f423])).
% 0.20/0.49  fof(f423,plain,(
% 0.20/0.49    $false | (spl6_17 | ~spl6_39)),
% 0.20/0.49    inference(subsumption_resolution,[],[f343,f411])).
% 0.20/0.49  fof(f411,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(X0)) ) | spl6_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f407,f149])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | spl6_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f148])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl6_17 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.49  fof(f407,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f390,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X0) | ~v1_xboole_0(X1)) )),
% 0.20/0.49    inference(resolution,[],[f350,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    ( ! [X1] : (r2_hidden(sK4(X1),X1) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(resolution,[],[f50,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.49  fof(f343,plain,(
% 0.20/0.49    v1_xboole_0(sK5) | ~spl6_39),
% 0.20/0.49    inference(avatar_component_clause,[],[f342])).
% 0.20/0.49  fof(f342,plain,(
% 0.20/0.49    spl6_39 <=> v1_xboole_0(sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.20/0.49  fof(f344,plain,(
% 0.20/0.49    spl6_39),
% 0.20/0.49    inference(avatar_split_clause,[],[f48,f342])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    v1_xboole_0(sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.49  % (5607)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    ~spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_20 | spl6_23),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f196])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    $false | (~spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_20 | spl6_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f195,f188])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | spl6_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f187])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    spl6_23 <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) | (~spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_20)),
% 0.20/0.49    inference(resolution,[],[f194,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    r2_hidden(sK3,sK0) | ~spl6_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl6_5 <=> r2_hidden(sK3,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | (~spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_20)),
% 0.20/0.49    inference(superposition,[],[f118,f162])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK2) | ~spl6_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f161])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    spl6_20 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | (~spl6_1 | ~spl6_8 | ~spl6_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f117,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    v1_funct_1(sK2) | ~spl6_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl6_1 <=> v1_funct_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | (~spl6_8 | ~spl6_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f116,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl6_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl6_8 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | ~spl6_10),
% 0.20/0.49    inference(resolution,[],[f114,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl6_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl6_10 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ~spl6_23 | spl6_9 | ~spl6_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f185,f182,f109,f187])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl6_9 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    spl6_22 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | (spl6_9 | ~spl6_22)),
% 0.20/0.49    inference(superposition,[],[f110,f183])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) | ~spl6_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f182])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) | spl6_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f109])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    spl6_22 | ~spl6_1 | spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f179,f90,f84,f74,f70,f62,f182])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl6_3 <=> v1_xboole_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl6_4 <=> m1_subset_1(sK3,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl6_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) | (~spl6_1 | spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.20/0.49    inference(resolution,[],[f103,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    m1_subset_1(sK3,sK0) | ~spl6_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f102,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0) | spl6_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f70])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl6_1 | ~spl6_6 | ~spl6_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f101,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl6_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl6_1 | ~spl6_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f98,f63])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | ~spl6_7),
% 0.20/0.49    inference(resolution,[],[f91,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    spl6_20 | ~spl6_11 | ~spl6_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f163,f124,f120,f161])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl6_11 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl6_12 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK2) | (~spl6_11 | ~spl6_12)),
% 0.20/0.49    inference(superposition,[],[f125,f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f120])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f124])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ~spl6_17 | spl6_2 | ~spl6_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f133,f127,f66,f148])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl6_2 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl6_13 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | (spl6_2 | ~spl6_13)),
% 0.20/0.49    inference(superposition,[],[f67,f128])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl6_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f127])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl6_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl6_12 | spl6_13 | ~spl6_6 | ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f100,f90,f84,f127,f124])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_6 | ~spl6_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f97,f85])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl6_7),
% 0.20/0.49    inference(resolution,[],[f91,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    spl6_11 | ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f95,f90,f120])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_7),
% 0.20/0.49    inference(resolution,[],[f91,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl6_10 | ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f94,f90,f113])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl6_7),
% 0.20/0.49    inference(resolution,[],[f91,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ~spl6_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f109])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  % (5616)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl6_8 | ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f93,f90,f105])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl6_7),
% 0.20/0.49    inference(resolution,[],[f91,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f90])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl6_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f84])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    spl6_5 | spl6_3 | ~spl6_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f78,f74,f70,f80])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    r2_hidden(sK3,sK0) | (spl6_3 | ~spl6_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f77,f71])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    v1_xboole_0(sK0) | r2_hidden(sK3,sK0) | ~spl6_4),
% 0.20/0.49    inference(resolution,[],[f75,f50])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl6_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f74])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    m1_subset_1(sK3,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ~spl6_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f70])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ~spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f66])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl6_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f62])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (5600)------------------------------
% 0.20/0.49  % (5600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5600)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (5600)Memory used [KB]: 6396
% 0.20/0.49  % (5600)Time elapsed: 0.078 s
% 0.20/0.49  % (5600)------------------------------
% 0.20/0.49  % (5600)------------------------------
% 0.20/0.50  % (5599)Success in time 0.138 s
%------------------------------------------------------------------------------
