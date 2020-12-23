%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 127 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  217 ( 345 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f80,f89,f109,f113,f117,f140,f153,f165,f175,f184])).

fof(f184,plain,
    ( ~ spl4_6
    | ~ spl4_10
    | spl4_24
    | ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_10
    | spl4_24
    | ~ spl4_27 ),
    inference(unit_resulting_resolution,[],[f79,f152,f61,f174])).

fof(f174,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = k10_relat_1(X0,X3) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_27
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = k10_relat_1(X0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f61,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_6
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f152,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl4_24
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f175,plain,
    ( spl4_27
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f166,f163,f111,f173])).

fof(f111,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f163,plain,
    ( spl4_26
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f166,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = k10_relat_1(X0,X3) )
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(resolution,[],[f164,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f164,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( spl4_26
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f148,f115,f107,f163])).

fof(f107,plain,
    ( spl4_16
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f115,plain,
    ( spl4_18
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f148,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(superposition,[],[f108,f116])).

fof(f116,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f108,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f153,plain,
    ( ~ spl4_24
    | ~ spl4_6
    | ~ spl4_18
    | spl4_22 ),
    inference(avatar_split_clause,[],[f149,f138,f115,f60,f151])).

fof(f138,plain,
    ( spl4_22
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f149,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ spl4_6
    | ~ spl4_18
    | spl4_22 ),
    inference(subsumption_resolution,[],[f146,f61])).

fof(f146,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_18
    | spl4_22 ),
    inference(superposition,[],[f139,f116])).

fof(f139,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( ~ spl4_22
    | ~ spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f121,f111,f78,f56,f48,f138])).

fof(f48,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f56,plain,
    ( spl4_5
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f121,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f57,f120])).

fof(f120,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f118,f79])).

fof(f118,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(resolution,[],[f112,f49])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f57,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f117,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f34,f115])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f113,plain,
    ( spl4_17
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f90,f87,f64,f111])).

fof(f64,plain,
    ( spl4_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f87,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f88,f65])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f109,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f33,f107])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f89,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f27,f87])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f80,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f76,f64,f52,f78])).

fof(f52,plain,
    ( spl4_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f76,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f53,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f65,f53])).

fof(f53,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f66,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f58,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f54,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f35,f52])).

fof(f35,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f50,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f48])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f23,f37])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (22969)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.43  % (22969)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f186,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f80,f89,f109,f113,f117,f140,f153,f165,f175,f184])).
% 0.20/0.43  fof(f184,plain,(
% 0.20/0.43    ~spl4_6 | ~spl4_10 | spl4_24 | ~spl4_27),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    $false | (~spl4_6 | ~spl4_10 | spl4_24 | ~spl4_27)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f79,f152,f61,f174])).
% 0.20/0.43  fof(f174,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = k10_relat_1(X0,X3)) ) | ~spl4_27),
% 0.20/0.43    inference(avatar_component_clause,[],[f173])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    spl4_27 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X1) | k1_xboole_0 = k10_relat_1(X0,X3))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl4_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl4_6 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl4_24),
% 0.20/0.43    inference(avatar_component_clause,[],[f151])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    spl4_24 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | ~spl4_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f78])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    spl4_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    spl4_27 | ~spl4_17 | ~spl4_26),
% 0.20/0.43    inference(avatar_split_clause,[],[f166,f163,f111,f173])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    spl4_17 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.43  fof(f163,plain,(
% 0.20/0.43    spl4_26 <=> ! [X1,X3,X0,X2] : (m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X1) | k1_xboole_0 = k10_relat_1(X0,X3)) ) | (~spl4_17 | ~spl4_26)),
% 0.20/0.43    inference(resolution,[],[f164,f112])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) ) | ~spl4_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f111])).
% 0.20/0.43  fof(f164,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_26),
% 0.20/0.43    inference(avatar_component_clause,[],[f163])).
% 0.20/0.43  fof(f165,plain,(
% 0.20/0.43    spl4_26 | ~spl4_16 | ~spl4_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f148,f115,f107,f163])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl4_16 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    spl4_18 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_16 | ~spl4_18)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f147])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_16 | ~spl4_18)),
% 0.20/0.43    inference(superposition,[],[f108,f116])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f115])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f107])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    ~spl4_24 | ~spl4_6 | ~spl4_18 | spl4_22),
% 0.20/0.43    inference(avatar_split_clause,[],[f149,f138,f115,f60,f151])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    spl4_22 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (~spl4_6 | ~spl4_18 | spl4_22)),
% 0.20/0.43    inference(subsumption_resolution,[],[f146,f61])).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_18 | spl4_22)),
% 0.20/0.43    inference(superposition,[],[f139,f116])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl4_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f138])).
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    ~spl4_22 | ~spl4_3 | spl4_5 | ~spl4_10 | ~spl4_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f121,f111,f78,f56,f48,f138])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl4_5 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (~spl4_3 | spl4_5 | ~spl4_10 | ~spl4_17)),
% 0.20/0.43    inference(backward_demodulation,[],[f57,f120])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_10 | ~spl4_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f118,f79])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_17)),
% 0.20/0.43    inference(resolution,[],[f112,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f48])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f56])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    spl4_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f115])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    spl4_17 | ~spl4_7 | ~spl4_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f90,f87,f64,f111])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    spl4_7 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    spl4_12 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) ) | (~spl4_7 | ~spl4_12)),
% 0.20/0.44    inference(resolution,[],[f88,f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f64])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl4_12),
% 0.20/0.44    inference(avatar_component_clause,[],[f87])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    spl4_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f33,f107])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    spl4_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f27,f87])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    spl4_10 | ~spl4_4 | ~spl4_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f76,f64,f52,f78])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    spl4_4 <=> v1_xboole_0(sK3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0) | (~spl4_4 | ~spl4_7)),
% 0.20/0.44    inference(backward_demodulation,[],[f53,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    k1_xboole_0 = sK3 | (~spl4_4 | ~spl4_7)),
% 0.20/0.44    inference(resolution,[],[f65,f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    v1_xboole_0(sK3) | ~spl4_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f52])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    spl4_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f26,f64])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    spl4_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f25,f60])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ~spl4_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f24,f56])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.20/0.44    inference(flattening,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    spl4_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f35,f52])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    v1_xboole_0(sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    spl4_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f38,f48])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.44    inference(backward_demodulation,[],[f23,f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.44    inference(equality_resolution,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (22969)------------------------------
% 0.20/0.44  % (22969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (22969)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (22969)Memory used [KB]: 10618
% 0.20/0.44  % (22969)Time elapsed: 0.031 s
% 0.20/0.44  % (22969)------------------------------
% 0.20/0.44  % (22969)------------------------------
% 0.20/0.44  % (22959)Success in time 0.086 s
%------------------------------------------------------------------------------
