%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 398 expanded)
%              Number of leaves         :   32 ( 163 expanded)
%              Depth                    :   12
%              Number of atoms          :  592 (1319 expanded)
%              Number of equality atoms :   48 ( 101 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f117,f159,f164,f191,f196,f238,f243,f253,f268,f274,f316,f333,f359])).

fof(f359,plain,
    ( ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_21
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_21
    | spl3_22 ),
    inference(subsumption_resolution,[],[f356,f119])).

fof(f119,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f79,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f356,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_21
    | spl3_22 ),
    inference(backward_demodulation,[],[f332,f355])).

fof(f355,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f176,f354])).

fof(f354,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f353,f178])).

fof(f178,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f116,f85,f163,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f163,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_8
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f85,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f353,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1)))
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f346,f319])).

fof(f319,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f276,f296])).

fof(f296,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f242,f273,f237,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f237,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl3_14
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f273,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl3_21
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f242,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl3_15
  <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f276,plain,
    ( k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f273,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f346,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f252,f237,f267,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f267,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl3_20
  <=> v2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f252,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_17
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f176,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f116,f85,f163,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f332,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl3_22
  <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f333,plain,
    ( ~ spl3_22
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_10
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f318,f271,f235,f193,f161,f114,f98,f83,f330])).

fof(f98,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f193,plain,
    ( spl3_10
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f318,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_10
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f195,f317])).

fof(f317,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f300,f176])).

fof(f300,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f85,f100,f273,f237,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f195,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f193])).

fof(f316,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_9
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_9
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f314,f119])).

fof(f314,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_9
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f190,f313])).

fof(f313,plain,
    ( k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f303,f183])).

fof(f183,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f177,f150])).

fof(f150,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f124,f146])).

fof(f146,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f85,f90,f100,f65])).

fof(f90,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f124,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f100,f72])).

fof(f177,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f116,f85,f163,f58])).

fof(f303,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f85,f100,f273,f237,f77])).

fof(f190,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl3_9
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f274,plain,
    ( spl3_21
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f216,f98,f93,f88,f83,f271])).

fof(f93,plain,
    ( spl3_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f216,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f212,f169])).

fof(f169,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f85,f90,f95,f100,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f95,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f212,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f85,f90,f95,f100,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f268,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f179,f161,f114,f83,f265])).

fof(f179,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f116,f85,f163,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f253,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f137,f114,f83,f250])).

fof(f137,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f85,f116,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f243,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f206,f98,f93,f88,f83,f240])).

fof(f206,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f202,f169])).

fof(f202,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f85,f90,f95,f100,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_2(k2_funct_2(X0,X1),X0,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f238,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f136,f114,f83,f235])).

fof(f136,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f85,f116,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f196,plain,
    ( ~ spl3_10
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f175,f156,f98,f93,f88,f83,f193])).

fof(f156,plain,
    ( spl3_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f175,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(backward_demodulation,[],[f158,f169])).

fof(f158,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f156])).

fof(f191,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f174,f152,f98,f93,f88,f83,f188])).

fof(f152,plain,
    ( spl3_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f174,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_6 ),
    inference(backward_demodulation,[],[f154,f169])).

fof(f154,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f164,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f138,f98,f93,f83,f161])).

fof(f138,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f85,f95,f100,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f159,plain,
    ( ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f78,f156,f152])).

fof(f78,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f50,f51,f51])).

fof(f50,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f117,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f104,f98,f114])).

fof(f104,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f100,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f101,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:44:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (32502)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.43  % (32502)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f372,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f117,f159,f164,f191,f196,f238,f243,f253,f268,f274,f316,f333,f359])).
% 0.22/0.43  fof(f359,plain,(
% 0.22/0.43    ~spl3_1 | ~spl3_5 | ~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_17 | ~spl3_20 | ~spl3_21 | spl3_22),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f358])).
% 0.22/0.43  fof(f358,plain,(
% 0.22/0.43    $false | (~spl3_1 | ~spl3_5 | ~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_17 | ~spl3_20 | ~spl3_21 | spl3_22)),
% 0.22/0.43    inference(subsumption_resolution,[],[f356,f119])).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f79,f81])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.44    inference(condensation,[],[f76])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(flattening,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f53,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,axiom,(
% 0.22/0.44    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.44  fof(f356,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | (~spl3_1 | ~spl3_5 | ~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_17 | ~spl3_20 | ~spl3_21 | spl3_22)),
% 0.22/0.44    inference(backward_demodulation,[],[f332,f355])).
% 0.22/0.44  fof(f355,plain,(
% 0.22/0.44    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1)) | (~spl3_1 | ~spl3_5 | ~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_17 | ~spl3_20 | ~spl3_21)),
% 0.22/0.44    inference(backward_demodulation,[],[f176,f354])).
% 0.22/0.44  fof(f354,plain,(
% 0.22/0.44    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl3_1 | ~spl3_5 | ~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_17 | ~spl3_20 | ~spl3_21)),
% 0.22/0.44    inference(forward_demodulation,[],[f353,f178])).
% 0.22/0.44  fof(f178,plain,(
% 0.22/0.44    sK1 = k2_funct_1(k2_funct_1(sK1)) | (~spl3_1 | ~spl3_5 | ~spl3_8)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f116,f85,f163,f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    v2_funct_1(sK1) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f161])).
% 0.22/0.44  fof(f161,plain,(
% 0.22/0.44    spl3_8 <=> v2_funct_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    v1_funct_1(sK1) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f83])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    spl3_1 <=> v1_funct_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f114])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    spl3_5 <=> v1_relat_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f353,plain,(
% 0.22/0.44    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) | (~spl3_14 | ~spl3_15 | ~spl3_17 | ~spl3_20 | ~spl3_21)),
% 0.22/0.44    inference(forward_demodulation,[],[f346,f319])).
% 0.22/0.44  fof(f319,plain,(
% 0.22/0.44    sK0 = k1_relat_1(k2_funct_1(sK1)) | (~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.22/0.44    inference(backward_demodulation,[],[f276,f296])).
% 0.22/0.44  fof(f296,plain,(
% 0.22/0.44    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | (~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f242,f273,f237,f65])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.44    inference(flattening,[],[f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,axiom,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.22/0.44  fof(f237,plain,(
% 0.22/0.44    v1_funct_1(k2_funct_1(sK1)) | ~spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f235])).
% 0.22/0.44  fof(f235,plain,(
% 0.22/0.44    spl3_14 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f273,plain,(
% 0.22/0.44    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_21),
% 0.22/0.44    inference(avatar_component_clause,[],[f271])).
% 0.22/0.44  fof(f271,plain,(
% 0.22/0.44    spl3_21 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.44  fof(f242,plain,(
% 0.22/0.44    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~spl3_15),
% 0.22/0.44    inference(avatar_component_clause,[],[f240])).
% 0.22/0.44  fof(f240,plain,(
% 0.22/0.44    spl3_15 <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.44  fof(f276,plain,(
% 0.22/0.44    k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1)) | ~spl3_21),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f273,f72])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.44  fof(f346,plain,(
% 0.22/0.44    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | (~spl3_14 | ~spl3_17 | ~spl3_20)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f252,f237,f267,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.44  fof(f267,plain,(
% 0.22/0.44    v2_funct_1(k2_funct_1(sK1)) | ~spl3_20),
% 0.22/0.44    inference(avatar_component_clause,[],[f265])).
% 0.22/0.44  fof(f265,plain,(
% 0.22/0.44    spl3_20 <=> v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.44  fof(f252,plain,(
% 0.22/0.44    v1_relat_1(k2_funct_1(sK1)) | ~spl3_17),
% 0.22/0.44    inference(avatar_component_clause,[],[f250])).
% 0.22/0.44  fof(f250,plain,(
% 0.22/0.44    spl3_17 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.44  fof(f176,plain,(
% 0.22/0.44    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | (~spl3_1 | ~spl3_5 | ~spl3_8)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f116,f85,f163,f59])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f27])).
% 0.22/0.44  fof(f332,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | spl3_22),
% 0.22/0.44    inference(avatar_component_clause,[],[f330])).
% 0.22/0.44  fof(f330,plain,(
% 0.22/0.44    spl3_22 <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.44  fof(f333,plain,(
% 0.22/0.44    ~spl3_22 | ~spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_10 | ~spl3_14 | ~spl3_21),
% 0.22/0.44    inference(avatar_split_clause,[],[f318,f271,f235,f193,f161,f114,f98,f83,f330])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f193,plain,(
% 0.22/0.44    spl3_10 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f318,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | (~spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_10 | ~spl3_14 | ~spl3_21)),
% 0.22/0.44    inference(backward_demodulation,[],[f195,f317])).
% 0.22/0.44  fof(f317,plain,(
% 0.22/0.44    k6_relat_1(k2_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_14 | ~spl3_21)),
% 0.22/0.44    inference(forward_demodulation,[],[f300,f176])).
% 0.22/0.44  fof(f300,plain,(
% 0.22/0.44    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl3_1 | ~spl3_4 | ~spl3_14 | ~spl3_21)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f100,f273,f237,f77])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.44    inference(flattening,[],[f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f98])).
% 0.22/0.44  fof(f195,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f193])).
% 0.22/0.44  fof(f316,plain,(
% 0.22/0.44    ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_9 | ~spl3_14 | ~spl3_21),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f315])).
% 0.22/0.44  fof(f315,plain,(
% 0.22/0.44    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_9 | ~spl3_14 | ~spl3_21)),
% 0.22/0.44    inference(subsumption_resolution,[],[f314,f119])).
% 0.22/0.44  fof(f314,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_9 | ~spl3_14 | ~spl3_21)),
% 0.22/0.44    inference(backward_demodulation,[],[f190,f313])).
% 0.22/0.44  fof(f313,plain,(
% 0.22/0.44    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_14 | ~spl3_21)),
% 0.22/0.44    inference(forward_demodulation,[],[f303,f183])).
% 0.22/0.44  fof(f183,plain,(
% 0.22/0.44    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_8)),
% 0.22/0.44    inference(forward_demodulation,[],[f177,f150])).
% 0.22/0.44  fof(f150,plain,(
% 0.22/0.44    sK0 = k1_relat_1(sK1) | (~spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.22/0.44    inference(backward_demodulation,[],[f124,f146])).
% 0.22/0.44  fof(f146,plain,(
% 0.22/0.44    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f90,f100,f65])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    v1_funct_2(sK1,sK0,sK0) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f88])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    spl3_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | ~spl3_4),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f100,f72])).
% 0.22/0.44  fof(f177,plain,(
% 0.22/0.44    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | (~spl3_1 | ~spl3_5 | ~spl3_8)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f116,f85,f163,f58])).
% 0.22/0.44  fof(f303,plain,(
% 0.22/0.44    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl3_1 | ~spl3_4 | ~spl3_14 | ~spl3_21)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f100,f273,f237,f77])).
% 0.22/0.44  fof(f190,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f188])).
% 0.22/0.44  fof(f188,plain,(
% 0.22/0.44    spl3_9 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f274,plain,(
% 0.22/0.44    spl3_21 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f216,f98,f93,f88,f83,f271])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    spl3_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f216,plain,(
% 0.22/0.44    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.44    inference(forward_demodulation,[],[f212,f169])).
% 0.22/0.44  fof(f169,plain,(
% 0.22/0.44    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f90,f95,f100,f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.44    inference(flattening,[],[f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,axiom,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    v3_funct_2(sK1,sK0,sK0) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f93])).
% 0.22/0.44  fof(f212,plain,(
% 0.22/0.44    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f90,f95,f100,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.44    inference(flattening,[],[f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.44  fof(f268,plain,(
% 0.22/0.44    spl3_20 | ~spl3_1 | ~spl3_5 | ~spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f179,f161,f114,f83,f265])).
% 0.22/0.44  fof(f179,plain,(
% 0.22/0.44    v2_funct_1(k2_funct_1(sK1)) | (~spl3_1 | ~spl3_5 | ~spl3_8)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f116,f85,f163,f56])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.44  fof(f253,plain,(
% 0.22/0.44    spl3_17 | ~spl3_1 | ~spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f137,f114,f83,f250])).
% 0.22/0.44  fof(f137,plain,(
% 0.22/0.44    v1_relat_1(k2_funct_1(sK1)) | (~spl3_1 | ~spl3_5)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f116,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.44  fof(f243,plain,(
% 0.22/0.44    spl3_15 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f206,f98,f93,f88,f83,f240])).
% 0.22/0.44  fof(f206,plain,(
% 0.22/0.44    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.44    inference(forward_demodulation,[],[f202,f169])).
% 0.22/0.44  fof(f202,plain,(
% 0.22/0.44    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f90,f95,f100,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_2(k2_funct_2(X0,X1),X0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f31])).
% 0.22/0.44  fof(f238,plain,(
% 0.22/0.44    spl3_14 | ~spl3_1 | ~spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f136,f114,f83,f235])).
% 0.22/0.44  fof(f136,plain,(
% 0.22/0.44    v1_funct_1(k2_funct_1(sK1)) | (~spl3_1 | ~spl3_5)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f116,f55])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f196,plain,(
% 0.22/0.44    ~spl3_10 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f175,f156,f98,f93,f88,f83,f193])).
% 0.22/0.44  fof(f156,plain,(
% 0.22/0.44    spl3_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f175,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7)),
% 0.22/0.44    inference(backward_demodulation,[],[f158,f169])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f156])).
% 0.22/0.44  fof(f191,plain,(
% 0.22/0.44    ~spl3_9 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f174,f152,f98,f93,f88,f83,f188])).
% 0.22/0.44  fof(f152,plain,(
% 0.22/0.44    spl3_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f174,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_6)),
% 0.22/0.44    inference(backward_demodulation,[],[f154,f169])).
% 0.22/0.44  fof(f154,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f152])).
% 0.22/0.44  fof(f164,plain,(
% 0.22/0.44    spl3_8 | ~spl3_1 | ~spl3_3 | ~spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f138,f98,f93,f83,f161])).
% 0.22/0.44  fof(f138,plain,(
% 0.22/0.44    v2_funct_1(sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f85,f95,f100,f74])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(flattening,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.44  fof(f159,plain,(
% 0.22/0.44    ~spl3_6 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f78,f156,f152])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.22/0.44    inference(definition_unfolding,[],[f50,f51,f51])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.44    inference(flattening,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.44    inference(negated_conjecture,[],[f16])).
% 0.22/0.44  fof(f16,conjecture,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    spl3_5 | ~spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f104,f98,f114])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl3_4),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f100,f71])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f49,f98])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f48,f93])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f47,f88])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f46,f83])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    v1_funct_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (32502)------------------------------
% 0.22/0.44  % (32502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (32502)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (32502)Memory used [KB]: 11001
% 0.22/0.44  % (32502)Time elapsed: 0.016 s
% 0.22/0.44  % (32502)------------------------------
% 0.22/0.44  % (32502)------------------------------
% 0.22/0.44  % (32486)Success in time 0.082 s
%------------------------------------------------------------------------------
