%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 195 expanded)
%              Number of leaves         :   27 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  307 ( 561 expanded)
%              Number of equality atoms :   75 ( 209 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f65,f70,f75,f80,f85,f94,f110,f124,f135,f137,f157,f160,f169,f171])).

fof(f171,plain,
    ( spl4_13
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl4_13
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f120,f166])).

fof(f166,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_19
  <=> ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f120,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_13
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f169,plain,
    ( spl4_19
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f168,f155,f122,f165])).

fof(f122,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f155,plain,
    ( spl4_18
  <=> ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) )
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f162,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f162,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl4_18 ),
    inference(superposition,[],[f45,f156])).

fof(f156,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f160,plain,
    ( ~ spl4_8
    | ~ spl4_14
    | spl4_17 ),
    inference(avatar_split_clause,[],[f159,f152,f122,f83])).

fof(f83,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f152,plain,
    ( spl4_17
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f159,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | spl4_17 ),
    inference(forward_demodulation,[],[f158,f48])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ v1_xboole_0(k1_xboole_0) )
    | spl4_17 ),
    inference(resolution,[],[f153,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f153,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f157,plain,
    ( ~ spl4_12
    | ~ spl4_17
    | spl4_18
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f149,f133,f122,f155,f152,f108])).

fof(f108,plain,
    ( spl4_12
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f133,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f144,f48])).

fof(f144,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl4_15 ),
    inference(resolution,[],[f134,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f134,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f137,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f135,plain,
    ( spl4_15
    | ~ spl4_14
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f131,f91,f63,f122,f133])).

fof(f63,plain,
    ( spl4_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f130,f92])).

fof(f92,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f129,f92])).

fof(f129,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f127,f92])).

fof(f127,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f66,f64])).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f66,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f124,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f117,f91,f51,f122,f119])).

fof(f51,plain,
    ( spl4_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f117,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f116,f92])).

fof(f116,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f115,f48])).

fof(f115,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f113,f92])).

fof(f113,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f52,f45])).

fof(f52,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f110,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f98,f91,f63,f108])).

fof(f98,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(superposition,[],[f64,f92])).

fof(f94,plain,
    ( spl4_9
    | ~ spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f88,f73,f83,f91])).

fof(f73,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f88,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f87,f74])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f36,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f85,plain,
    ( spl4_8
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f81,f78,f68,f83])).

fof(f68,plain,
    ( spl4_5
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f78,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f81,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f69,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f69,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f80,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f76,f68,f78])).

fof(f76,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(resolution,[],[f35,f69])).

fof(f75,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f71,f55,f73])).

fof(f55,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f56,f48])).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f70,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f46,f68])).

fof(f46,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f28])).

fof(f28,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f65,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).

fof(f24,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f57,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f33,f51])).

fof(f33,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:55:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (1220)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (1229)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (1220)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (1221)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (1228)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f53,f57,f65,f70,f75,f80,f85,f94,f110,f124,f135,f137,f157,f160,f169,f171])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl4_13 | ~spl4_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    $false | (spl4_13 | ~spl4_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) ) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f165])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl4_19 <=> ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl4_13 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl4_19 | ~spl4_14 | ~spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f168,f155,f122,f165])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl4_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    spl4_18 <=> ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl4_18),
% 0.21/0.48    inference(forward_demodulation,[],[f162,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl4_18),
% 0.21/0.48    inference(superposition,[],[f45,f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)) ) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f155])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~spl4_8 | ~spl4_14 | spl4_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f159,f152,f122,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl4_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl4_17 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | spl4_17),
% 0.21/0.48    inference(forward_demodulation,[],[f158,f48])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_xboole_0(k1_xboole_0)) ) | spl4_17),
% 0.21/0.48    inference(resolution,[],[f153,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl4_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~spl4_12 | ~spl4_17 | spl4_18 | ~spl4_14 | ~spl4_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f149,f133,f122,f155,f152,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl4_12 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl4_15 <=> ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)) ) | ~spl4_15),
% 0.21/0.48    inference(forward_demodulation,[],[f144,f48])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl4_15),
% 0.21/0.48    inference(resolution,[],[f134,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)) ) | ~spl4_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f133])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl4_15 | ~spl4_14 | ~spl4_4 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f131,f91,f63,f122,f133])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl4_4 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl4_9 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f130,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f129,f92])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) | ~v1_funct_2(sK2,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f127,f92])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X0) | ~v1_funct_2(sK2,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_4),
% 0.21/0.48    inference(resolution,[],[f66,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f49,f48])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(equality_resolution,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~spl4_13 | ~spl4_14 | spl4_1 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f117,f91,f51,f122,f119])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl4_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f116,f92])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f115,f48])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f113,f92])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_1),
% 0.21/0.48    inference(superposition,[],[f52,f45])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl4_12 | ~spl4_4 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f91,f63,f108])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    v1_funct_1(k1_xboole_0) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(superposition,[],[f64,f92])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_9 | ~spl4_8 | ~spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f88,f73,f83,f91])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | ~spl4_6),
% 0.21/0.48    inference(resolution,[],[f87,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(resolution,[],[f36,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl4_8 | ~spl4_5 | ~spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f81,f78,f68,f83])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_5 <=> v1_xboole_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_7 <=> k1_xboole_0 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_7)),
% 0.21/0.48    inference(superposition,[],[f69,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    k1_xboole_0 = sK3 | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    v1_xboole_0(sK3) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl4_7 | ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f76,f68,f78])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k1_xboole_0 = sK3 | ~spl4_5),
% 0.21/0.48    inference(resolution,[],[f35,f69])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl4_6 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f71,f55,f73])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f56,f48])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f68])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v1_xboole_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_xboole_0(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK3)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f63])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f55])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f51])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (1220)------------------------------
% 0.21/0.48  % (1220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1220)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (1220)Memory used [KB]: 10746
% 0.21/0.48  % (1220)Time elapsed: 0.065 s
% 0.21/0.48  % (1220)------------------------------
% 0.21/0.48  % (1220)------------------------------
% 0.21/0.48  % (1213)Success in time 0.122 s
%------------------------------------------------------------------------------
