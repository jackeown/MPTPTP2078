%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 177 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  283 ( 597 expanded)
%              Number of equality atoms :  105 ( 294 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f78,f89,f101,f107,f119,f124,f139,f141])).

fof(f141,plain,
    ( spl3_11
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_11
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f118,f136])).

fof(f136,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(sK2,X1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_14
  <=> ! [X1] : k1_xboole_0 = k10_relat_1(sK2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f118,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_11
  <=> k1_xboole_0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f139,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f138,f122,f105,f76,f135])).

fof(f76,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f105,plain,
    ( spl3_10
  <=> ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f122,plain,
    ( spl3_12
  <=> ! [X0] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k10_relat_1(sK2,X0) )
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f132,f39])).

fof(f39,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f132,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(superposition,[],[f37,f126])).

fof(f126,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0)
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(resolution,[],[f123,f106])).

fof(f106,plain,
    ( ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f124,plain,
    ( ~ spl3_7
    | spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f120,f59,f122,f76])).

fof(f59,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f120,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f45,f39])).

fof(f45,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f119,plain,
    ( ~ spl3_11
    | ~ spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f115,f47,f76,f117])).

fof(f47,plain,
    ( spl3_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(sK2,sK1)
    | spl3_1 ),
    inference(forward_demodulation,[],[f114,f39])).

fof(f114,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f48,f37])).

fof(f48,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f107,plain,
    ( spl3_10
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f103,f96,f76,f105])).

fof(f96,plain,
    ( spl3_9
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl3_9 ),
    inference(superposition,[],[f83,f97])).

fof(f97,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f81,f39])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f71,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f71,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f43,f39])).

fof(f43,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f101,plain,
    ( spl3_9
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f100,f87,f76,f96])).

fof(f87,plain,
    ( spl3_8
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f92,f39])).

fof(f92,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_8 ),
    inference(superposition,[],[f28,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f85,f76,f55,f87])).

fof(f55,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2) )
    | ~ spl3_7 ),
    inference(resolution,[],[f72,f77])).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f44,f39])).

fof(f44,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f51,f76])).

fof(f51,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f52,f39])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f61,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f57,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    v1_funct_2(sK2,k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:28:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.43  % (16868)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.44  % (16888)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.44  % (16868)Refutation not found, incomplete strategy% (16868)------------------------------
% 0.19/0.44  % (16868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (16868)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (16868)Memory used [KB]: 10618
% 0.19/0.44  % (16868)Time elapsed: 0.050 s
% 0.19/0.44  % (16868)------------------------------
% 0.19/0.44  % (16868)------------------------------
% 0.19/0.44  % (16888)Refutation not found, incomplete strategy% (16888)------------------------------
% 0.19/0.44  % (16888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (16888)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (16888)Memory used [KB]: 10618
% 0.19/0.44  % (16888)Time elapsed: 0.053 s
% 0.19/0.44  % (16888)------------------------------
% 0.19/0.44  % (16888)------------------------------
% 0.19/0.45  % (16871)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.45  % (16871)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f142,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f78,f89,f101,f107,f119,f124,f139,f141])).
% 0.19/0.45  fof(f141,plain,(
% 0.19/0.45    spl3_11 | ~spl3_14),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f140])).
% 0.19/0.45  fof(f140,plain,(
% 0.19/0.45    $false | (spl3_11 | ~spl3_14)),
% 0.19/0.45    inference(subsumption_resolution,[],[f118,f136])).
% 0.19/0.45  fof(f136,plain,(
% 0.19/0.45    ( ! [X1] : (k1_xboole_0 = k10_relat_1(sK2,X1)) ) | ~spl3_14),
% 0.19/0.45    inference(avatar_component_clause,[],[f135])).
% 0.19/0.45  fof(f135,plain,(
% 0.19/0.45    spl3_14 <=> ! [X1] : k1_xboole_0 = k10_relat_1(sK2,X1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.19/0.45  fof(f118,plain,(
% 0.19/0.45    k1_xboole_0 != k10_relat_1(sK2,sK1) | spl3_11),
% 0.19/0.45    inference(avatar_component_clause,[],[f117])).
% 0.19/0.45  fof(f117,plain,(
% 0.19/0.45    spl3_11 <=> k1_xboole_0 = k10_relat_1(sK2,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.45  fof(f139,plain,(
% 0.19/0.45    spl3_14 | ~spl3_7 | ~spl3_10 | ~spl3_12),
% 0.19/0.45    inference(avatar_split_clause,[],[f138,f122,f105,f76,f135])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.45  fof(f105,plain,(
% 0.19/0.45    spl3_10 <=> ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.45  fof(f122,plain,(
% 0.19/0.45    spl3_12 <=> ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0) | ~v1_funct_2(sK2,k1_xboole_0,X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.45  fof(f138,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k10_relat_1(sK2,X0)) ) | (~spl3_10 | ~spl3_12)),
% 0.19/0.45    inference(forward_demodulation,[],[f132,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.45    inference(equality_resolution,[],[f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.46    inference(flattening,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.46    inference(nnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.46  fof(f132,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl3_10 | ~spl3_12)),
% 0.19/0.46    inference(superposition,[],[f37,f126])).
% 0.19/0.46  fof(f126,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0)) ) | (~spl3_10 | ~spl3_12)),
% 0.19/0.46    inference(resolution,[],[f123,f106])).
% 0.19/0.46  fof(f106,plain,(
% 0.19/0.46    ( ! [X0] : (v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl3_10),
% 0.19/0.46    inference(avatar_component_clause,[],[f105])).
% 0.19/0.46  fof(f123,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_funct_2(sK2,k1_xboole_0,X0) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0)) ) | ~spl3_12),
% 0.19/0.46    inference(avatar_component_clause,[],[f122])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.19/0.46  fof(f124,plain,(
% 0.19/0.46    ~spl3_7 | spl3_12 | ~spl3_4),
% 0.19/0.46    inference(avatar_split_clause,[],[f120,f59,f122,f76])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    spl3_4 <=> v1_funct_1(sK2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.46  fof(f120,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0) | ~v1_funct_2(sK2,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_4),
% 0.19/0.46    inference(resolution,[],[f73,f60])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    v1_funct_1(sK2) | ~spl3_4),
% 0.19/0.46    inference(avatar_component_clause,[],[f59])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f45,f39])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.46    inference(equality_resolution,[],[f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.46    inference(flattening,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.19/0.46  fof(f119,plain,(
% 0.19/0.46    ~spl3_11 | ~spl3_7 | spl3_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f115,f47,f76,f117])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    spl3_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(sK2,sK1) | spl3_1),
% 0.19/0.46    inference(forward_demodulation,[],[f114,f39])).
% 0.19/0.46  fof(f114,plain,(
% 0.19/0.46    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_1),
% 0.19/0.46    inference(superposition,[],[f48,f37])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f47])).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    spl3_10 | ~spl3_7 | ~spl3_9),
% 0.19/0.46    inference(avatar_split_clause,[],[f103,f96,f76,f105])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    spl3_9 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.46  fof(f103,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl3_9),
% 0.19/0.46    inference(trivial_inequality_removal,[],[f102])).
% 0.19/0.46  fof(f102,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl3_9),
% 0.19/0.46    inference(superposition,[],[f83,f97])).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_9),
% 0.19/0.46    inference(avatar_component_clause,[],[f96])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f82])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f81,f39])).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.19/0.46    inference(superposition,[],[f71,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f43,f39])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.19/0.46    inference(equality_resolution,[],[f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(nnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.46  fof(f101,plain,(
% 0.19/0.46    spl3_9 | ~spl3_7 | ~spl3_8),
% 0.19/0.46    inference(avatar_split_clause,[],[f100,f87,f76,f96])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    spl3_8 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.46  fof(f100,plain,(
% 0.19/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl3_8),
% 0.19/0.46    inference(forward_demodulation,[],[f92,f39])).
% 0.19/0.46  fof(f92,plain,(
% 0.19/0.46    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_8),
% 0.19/0.46    inference(superposition,[],[f28,f88])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK2) | ~spl3_8),
% 0.19/0.46    inference(avatar_component_clause,[],[f87])).
% 0.19/0.46  fof(f89,plain,(
% 0.19/0.46    spl3_8 | ~spl3_3 | ~spl3_7),
% 0.19/0.46    inference(avatar_split_clause,[],[f85,f76,f55,f87])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    spl3_3 <=> v1_funct_2(sK2,k1_xboole_0,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK2) | (~spl3_3 | ~spl3_7)),
% 0.19/0.46    inference(resolution,[],[f84,f56])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    v1_funct_2(sK2,k1_xboole_0,sK0) | ~spl3_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f55])).
% 0.19/0.46  fof(f84,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_funct_2(sK2,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2)) ) | ~spl3_7),
% 0.19/0.46    inference(resolution,[],[f72,f77])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_7),
% 0.19/0.46    inference(avatar_component_clause,[],[f76])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f44,f39])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.19/0.46    inference(equality_resolution,[],[f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f78,plain,(
% 0.19/0.46    spl3_7 | ~spl3_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f74,f51,f76])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_2),
% 0.19/0.46    inference(forward_demodulation,[],[f52,f39])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f51])).
% 0.19/0.46  fof(f61,plain,(
% 0.19/0.46    spl3_4),
% 0.19/0.46    inference(avatar_split_clause,[],[f21,f59])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    v1_funct_1(sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.19/0.46    inference(flattening,[],[f8])).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.46    inference(negated_conjecture,[],[f6])).
% 0.19/0.46  fof(f6,conjecture,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    spl3_3),
% 0.19/0.46    inference(avatar_split_clause,[],[f22,f55])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    v1_funct_2(sK2,k1_xboole_0,sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    spl3_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f23,f51])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ~spl3_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f24,f47])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (16871)------------------------------
% 0.19/0.46  % (16871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (16871)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (16871)Memory used [KB]: 10618
% 0.19/0.46  % (16871)Time elapsed: 0.004 s
% 0.19/0.46  % (16871)------------------------------
% 0.19/0.46  % (16871)------------------------------
% 0.19/0.46  % (16861)Success in time 0.111 s
%------------------------------------------------------------------------------
