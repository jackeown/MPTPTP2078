%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 356 expanded)
%              Number of leaves         :   38 ( 149 expanded)
%              Depth                    :    9
%              Number of atoms          :  545 (1292 expanded)
%              Number of equality atoms :   48 (  98 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f107,f110,f113,f125,f127,f139,f147,f155,f160,f168,f174,f186,f201,f216,f223,f228,f236,f245,f252,f254,f265,f344,f347,f358])).

fof(f358,plain,
    ( spl3_20
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl3_20
    | ~ spl3_31 ),
    inference(resolution,[],[f348,f91])).

fof(f91,plain,(
    ! [X2] : r2_relset_1(X2,X2,k6_partfun1(X2),k6_partfun1(X2)) ),
    inference(resolution,[],[f73,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f49,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f348,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl3_20
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f222,f343])).

fof(f343,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl3_31
  <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f222,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_20
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f347,plain,
    ( ~ spl3_14
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl3_14
    | spl3_30 ),
    inference(resolution,[],[f339,f189])).

fof(f189,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_14 ),
    inference(resolution,[],[f185,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f185,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_14
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f339,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl3_30
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f344,plain,
    ( ~ spl3_22
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_16
    | ~ spl3_15
    | spl3_31
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f324,f261,f341,f194,f198,f337,f96,f100,f231])).

fof(f231,plain,
    ( spl3_22
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f100,plain,
    ( spl3_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f96,plain,
    ( spl3_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f198,plain,
    ( spl3_16
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f194,plain,
    ( spl3_15
  <=> v2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f261,plain,
    ( spl3_25
  <=> sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f324,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_25 ),
    inference(superposition,[],[f111,f263])).

fof(f263,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f261])).

fof(f111,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k1_relat_1(k2_funct_1(X0)))
      | ~ v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f72,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f49])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f265,plain,
    ( ~ spl3_14
    | spl3_25
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f259,f213,f261,f183])).

fof(f213,plain,
    ( spl3_19
  <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f259,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_19 ),
    inference(superposition,[],[f65,f215])).

fof(f215,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f213])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f254,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl3_24 ),
    inference(resolution,[],[f251,f91])).

fof(f251,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl3_24
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f252,plain,
    ( ~ spl3_22
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_24
    | ~ spl3_9
    | spl3_21 ),
    inference(avatar_split_clause,[],[f247,f225,f135,f249,f96,f100,f231])).

fof(f135,plain,
    ( spl3_9
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f225,plain,
    ( spl3_21
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f247,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_9
    | spl3_21 ),
    inference(forward_demodulation,[],[f246,f137])).

fof(f137,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f246,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_21 ),
    inference(superposition,[],[f227,f72])).

fof(f227,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f225])).

fof(f245,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_11
    | spl3_16 ),
    inference(resolution,[],[f200,f156])).

fof(f156,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f146,f154])).

fof(f154,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_11
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f146,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_10
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f200,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f198])).

fof(f236,plain,(
    spl3_22 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl3_22 ),
    inference(resolution,[],[f233,f84])).

fof(f84,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f64,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f40])).

fof(f40,plain,
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f233,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f231])).

fof(f228,plain,
    ( ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_14
    | ~ spl3_21
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f218,f152,f75,f225,f183,f198,f131,f100])).

fof(f131,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f218,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl3_1
    | ~ spl3_11 ),
    inference(superposition,[],[f158,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f158,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl3_1
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f77,f154])).

fof(f77,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f223,plain,
    ( ~ spl3_16
    | ~ spl3_14
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_20
    | spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f217,f152,f79,f220,f131,f100,f183,f198])).

fof(f79,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f217,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_2
    | ~ spl3_11 ),
    inference(superposition,[],[f157,f69])).

fof(f157,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl3_2
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f81,f154])).

fof(f81,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f216,plain,
    ( ~ spl3_16
    | ~ spl3_12
    | spl3_19
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f192,f183,f213,f165,f198])).

fof(f165,plain,
    ( spl3_12
  <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f192,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_14 ),
    inference(resolution,[],[f185,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f201,plain,
    ( spl3_15
    | ~ spl3_16
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f187,f183,f171,f198,f194])).

fof(f171,plain,
    ( spl3_13
  <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f187,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_1(k2_funct_1(sK1))
    | ~ spl3_14 ),
    inference(resolution,[],[f185,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f186,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_8
    | spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f181,f152,f183,f131,f104,f118,f100])).

fof(f118,plain,
    ( spl3_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f104,plain,
    ( spl3_5
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f181,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f62,f154])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f174,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_8
    | spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f169,f152,f171,f131,f104,f118,f100])).

fof(f169,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f61,f154])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f168,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_8
    | spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f163,f152,f165,f131,f104,f118,f100])).

fof(f163,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f60,f154])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f160,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f133,f47])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f155,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | spl3_11 ),
    inference(avatar_split_clause,[],[f149,f152,f104,f118,f100])).

fof(f149,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f58,f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f147,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | spl3_10 ),
    inference(avatar_split_clause,[],[f141,f144,f104,f118,f100])).

fof(f141,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f129,f122,f135,f131])).

fof(f122,plain,
    ( spl3_7
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f65,f124])).

fof(f124,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f127,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f120,f45])).

fof(f45,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f115,f122,f118,f100])).

fof(f115,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f63,f47])).

fof(f113,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f106,f46])).

fof(f46,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f110,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f102,f44])).

fof(f44,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f107,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f93,f104,f100,f96])).

fof(f93,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f67,f47])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f48,f79,f75])).

fof(f48,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (24474)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (24471)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (24470)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (24466)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (24460)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (24463)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (24468)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (24470)Refutation not found, incomplete strategy% (24470)------------------------------
% 0.21/0.48  % (24470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24463)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f82,f107,f110,f113,f125,f127,f139,f147,f155,f160,f168,f174,f186,f201,f216,f223,f228,f236,f245,f252,f254,f265,f344,f347,f358])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    spl3_20 | ~spl3_31),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f357])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    $false | (spl3_20 | ~spl3_31)),
% 0.21/0.48    inference(resolution,[],[f348,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X2] : (r2_relset_1(X2,X2,k6_partfun1(X2),k6_partfun1(X2))) )),
% 0.21/0.48    inference(resolution,[],[f73,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f50,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.21/0.48    inference(condensation,[],[f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (spl3_20 | ~spl3_31)),
% 0.21/0.48    inference(backward_demodulation,[],[f222,f343])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl3_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f341])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    spl3_31 <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f220])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    spl3_20 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    ~spl3_14 | spl3_30),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f345])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    $false | (~spl3_14 | spl3_30)),
% 0.21/0.48    inference(resolution,[],[f339,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK1)) | ~spl3_14),
% 0.21/0.48    inference(resolution,[],[f185,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    spl3_14 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    ~v1_relat_1(k2_funct_1(sK1)) | spl3_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f337])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    spl3_30 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    ~spl3_22 | ~spl3_4 | ~spl3_3 | ~spl3_30 | ~spl3_16 | ~spl3_15 | spl3_31 | ~spl3_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f324,f261,f341,f194,f198,f337,f96,f100,f231])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl3_22 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl3_4 <=> v1_funct_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_3 <=> v2_funct_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl3_16 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    spl3_15 <=> v2_funct_1(k2_funct_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    spl3_25 <=> sK0 = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_25),
% 0.21/0.48    inference(superposition,[],[f111,f263])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    sK0 = k1_relat_1(k2_funct_1(sK1)) | ~spl3_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f261])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f72,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f55,f49])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ~spl3_14 | spl3_25 | ~spl3_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f259,f213,f261,f183])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl3_19 <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    sK0 = k1_relat_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_19),
% 0.21/0.48    inference(superposition,[],[f65,f215])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~spl3_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f213])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    spl3_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f253])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    $false | spl3_24),
% 0.21/0.48    inference(resolution,[],[f251,f91])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl3_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f249])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    spl3_24 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ~spl3_22 | ~spl3_4 | ~spl3_3 | ~spl3_24 | ~spl3_9 | spl3_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f247,f225,f135,f249,f96,f100,f231])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl3_9 <=> sK0 = k1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    spl3_21 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_9 | spl3_21)),
% 0.21/0.48    inference(forward_demodulation,[],[f246,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK1) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_21),
% 0.21/0.48    inference(superposition,[],[f227,f72])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl3_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f225])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ~spl3_10 | ~spl3_11 | spl3_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f243])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    $false | (~spl3_10 | ~spl3_11 | spl3_16)),
% 0.21/0.48    inference(resolution,[],[f200,f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_1(sK1)) | (~spl3_10 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f146,f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl3_11 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl3_10 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK1)) | spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f198])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    spl3_22),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    $false | spl3_22),
% 0.21/0.48    inference(resolution,[],[f233,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f64,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_8 | ~spl3_16 | ~spl3_14 | ~spl3_21 | spl3_1 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f218,f152,f75,f225,f183,f198,f131,f100])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (spl3_1 | ~spl3_11)),
% 0.21/0.48    inference(superposition,[],[f158,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.48    inference(flattening,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | (spl3_1 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f77,f154])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ~spl3_16 | ~spl3_14 | ~spl3_4 | ~spl3_8 | ~spl3_20 | spl3_2 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f217,f152,f79,f220,f131,f100,f183,f198])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | (spl3_2 | ~spl3_11)),
% 0.21/0.48    inference(superposition,[],[f157,f69])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | (spl3_2 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f81,f154])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ~spl3_16 | ~spl3_12 | spl3_19 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f192,f183,f213,f165,f198])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl3_12 <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~spl3_14),
% 0.21/0.48    inference(resolution,[],[f185,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl3_15 | ~spl3_16 | ~spl3_13 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f187,f183,f171,f198,f194])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl3_13 <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_1(k2_funct_1(sK1)) | ~spl3_14),
% 0.21/0.48    inference(resolution,[],[f185,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_6 | ~spl3_5 | ~spl3_8 | spl3_14 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f181,f152,f183,f131,f104,f118,f100])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    spl3_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl3_5 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_11),
% 0.21/0.48    inference(superposition,[],[f62,f154])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_6 | ~spl3_5 | ~spl3_8 | spl3_13 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f169,f152,f171,f131,f104,f118,f100])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_11),
% 0.21/0.48    inference(superposition,[],[f61,f154])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_6 | ~spl3_5 | ~spl3_8 | spl3_12 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f163,f152,f165,f131,f104,f118,f100])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_11),
% 0.21/0.48    inference(superposition,[],[f60,f154])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    $false | spl3_8),
% 0.21/0.48    inference(resolution,[],[f133,f47])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_6 | ~spl3_5 | spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f149,f152,f104,f118,f100])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f58,f47])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_6 | ~spl3_5 | spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f141,f144,f104,f118,f100])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f59,f47])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ~spl3_8 | spl3_9 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f129,f122,f135,f131])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl3_7 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 0.21/0.48    inference(superposition,[],[f65,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f122])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    $false | spl3_6),
% 0.21/0.48    inference(resolution,[],[f120,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~v1_funct_2(sK1,sK0,sK0) | spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f118])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_6 | spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f115,f122,f118,f100])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f63,f47])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    $false | spl3_5),
% 0.21/0.48    inference(resolution,[],[f106,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~v3_funct_2(sK1,sK0,sK0) | spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    $false | spl3_4),
% 0.21/0.48    inference(resolution,[],[f102,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~v1_funct_1(sK1) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl3_3 | ~spl3_4 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f93,f104,f100,f96])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f67,f47])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f79,f75])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (24463)------------------------------
% 0.21/0.48  % (24463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24463)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (24463)Memory used [KB]: 6268
% 0.21/0.48  % (24463)Time elapsed: 0.055 s
% 0.21/0.48  % (24463)------------------------------
% 0.21/0.48  % (24463)------------------------------
% 0.21/0.48  % (24458)Success in time 0.12 s
%------------------------------------------------------------------------------
