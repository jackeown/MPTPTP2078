%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:51 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 475 expanded)
%              Number of leaves         :   50 ( 196 expanded)
%              Depth                    :   13
%              Number of atoms          : 1077 (2500 expanded)
%              Number of equality atoms :  220 ( 651 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f751,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f175,f185,f191,f199,f255,f272,f385,f406,f437,f456,f484,f519,f563,f604,f621,f691,f722])).

fof(f722,plain,
    ( spl4_1
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | spl4_1
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f720,f184])).

fof(f184,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f720,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f719,f153])).

fof(f153,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f719,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f718,f455])).

fof(f455,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl4_39
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f718,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f697,f113])).

fof(f113,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f697,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f74,f616])).

fof(f616,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f614])).

fof(f614,plain,
    ( spl4_46
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f74,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f691,plain,
    ( ~ spl4_14
    | ~ spl4_16
    | ~ spl4_37
    | spl4_47 ),
    inference(avatar_contradiction_clause,[],[f690])).

fof(f690,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_37
    | spl4_47 ),
    inference(subsumption_resolution,[],[f689,f198])).

fof(f198,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_16
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f689,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ spl4_14
    | ~ spl4_37
    | spl4_47 ),
    inference(subsumption_resolution,[],[f688,f436])).

fof(f436,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl4_37
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f688,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl4_14
    | spl4_47 ),
    inference(equality_resolution,[],[f676])).

fof(f676,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(sK0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) )
    | ~ spl4_14
    | spl4_47 ),
    inference(subsumption_resolution,[],[f675,f184])).

fof(f675,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(sK0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_47 ),
    inference(superposition,[],[f620,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f620,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl4_47
  <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f621,plain,
    ( spl4_46
    | ~ spl4_47
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_35
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f611,f490,f453,f398,f267,f188,f182,f166,f151,f618,f614])).

fof(f166,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f188,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f267,plain,
    ( spl4_24
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f398,plain,
    ( spl4_35
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f490,plain,
    ( spl4_43
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f611,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_35
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f610,f400])).

fof(f400,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f398])).

fof(f610,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f609,f269])).

fof(f269,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f267])).

fof(f609,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f608,f184])).

fof(f608,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f607,f153])).

fof(f607,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f606,f190])).

fof(f190,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f606,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f605,f168])).

fof(f168,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f605,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f602,f455])).

fof(f602,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43 ),
    inference(superposition,[],[f71,f492])).

fof(f492,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f490])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f604,plain,
    ( spl4_38
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | spl4_38
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f600,f86])).

fof(f86,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f600,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | spl4_38
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f451,f492])).

fof(f451,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl4_38
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f563,plain,
    ( spl4_43
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f562,f481,f166,f156,f151,f141,f490])).

fof(f141,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f156,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f481,plain,
    ( spl4_41
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f562,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f561,f168])).

fof(f561,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f560,f158])).

fof(f158,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f560,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f559,f153])).

fof(f559,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f550,f143])).

fof(f143,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f550,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_41 ),
    inference(superposition,[],[f93,f483])).

fof(f483,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f481])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f519,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_40 ),
    inference(subsumption_resolution,[],[f517,f168])).

fof(f517,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_40 ),
    inference(subsumption_resolution,[],[f516,f158])).

fof(f516,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_40 ),
    inference(subsumption_resolution,[],[f515,f153])).

fof(f515,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_40 ),
    inference(subsumption_resolution,[],[f512,f143])).

fof(f512,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_40 ),
    inference(resolution,[],[f479,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f479,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl4_40
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f484,plain,
    ( ~ spl4_40
    | spl4_41
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f473,f172,f481,f477])).

fof(f172,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f473,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f305,f174])).

fof(f174,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f305,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f87,f176])).

fof(f176,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f89,f90])).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f456,plain,
    ( ~ spl4_38
    | spl4_39
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f447,f398,f267,f188,f182,f166,f151,f453,f449])).

fof(f447,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f446,f184])).

fof(f446,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f445,f153])).

fof(f445,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f444])).

fof(f444,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(superposition,[],[f415,f269])).

fof(f415,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | v2_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f414,f190])).

fof(f414,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | v2_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_12
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f409,f168])).

fof(f409,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | v2_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_35 ),
    inference(superposition,[],[f84,f400])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f437,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f432,f172,f166,f161,f156,f151,f146,f141,f434])).

fof(f146,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f161,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f432,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f431,f168])).

fof(f431,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f430,f163])).

fof(f163,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f430,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f429,f158])).

fof(f429,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f428,f153])).

fof(f428,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f427,f148])).

fof(f148,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f427,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f424,f143])).

fof(f424,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(resolution,[],[f407,f174])).

fof(f407,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | v2_funct_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f82,f90])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f406,plain,
    ( spl4_35
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f405,f382,f188,f166,f126,f398])).

fof(f126,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f382,plain,
    ( spl4_34
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f405,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f404,f94])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f404,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f403,f190])).

fof(f403,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f402,f168])).

fof(f402,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f391,f128])).

fof(f128,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f391,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_34 ),
    inference(superposition,[],[f72,f384])).

fof(f384,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f382])).

fof(f72,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f385,plain,
    ( spl4_34
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f380,f166,f161,f156,f136,f126,f116,f382])).

fof(f116,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f136,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f380,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f379,f168])).

fof(f379,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f378,f163])).

fof(f378,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f377,f158])).

fof(f377,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f376,f128])).

fof(f376,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f375,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f375,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f333,f138])).

fof(f138,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f70,f90])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f272,plain,
    ( spl4_24
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f271,f252,f141,f267])).

fof(f252,plain,
    ( spl4_22
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f271,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f264,f143])).

fof(f264,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_22 ),
    inference(superposition,[],[f98,f254])).

fof(f254,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f252])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f255,plain,
    ( spl4_22
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f250,f146,f141,f121,f252])).

fof(f121,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f250,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f249,f123])).

fof(f123,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f249,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f246,f148])).

fof(f246,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f75,f143])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f199,plain,
    ( spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f192,f141,f196])).

fof(f192,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f101,f143])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f191,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f186,f156,f188])).

fof(f186,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f178,f97])).

fof(f97,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f178,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f96,f158])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f185,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f180,f141,f182])).

fof(f180,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f177,f97])).

fof(f177,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f96,f143])).

fof(f175,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f170,f131,f172])).

fof(f131,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f170,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f133,f90])).

fof(f133,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f169,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f57,f166])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f164,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f58,f161])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f159,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f59,f156])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f154,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f60,f151])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f149,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f61,f146])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f144,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f62,f141])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f63,f136])).

fof(f63,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f134,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f64,f131])).

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f129,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f65,f126])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f124,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f66,f121])).

fof(f66,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f53])).

fof(f119,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f67,f116])).

fof(f67,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f68,f111])).

fof(f68,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:50:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (18661)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (18664)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (18656)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (18676)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (18657)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (18659)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (18678)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (18658)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (18670)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (18684)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (18681)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.55  % (18662)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (18660)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.55  % (18672)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (18673)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.43/0.55  % (18672)Refutation not found, incomplete strategy% (18672)------------------------------
% 1.43/0.55  % (18672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (18672)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (18672)Memory used [KB]: 10746
% 1.43/0.55  % (18672)Time elapsed: 0.137 s
% 1.43/0.55  % (18672)------------------------------
% 1.43/0.55  % (18672)------------------------------
% 1.43/0.55  % (18669)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.56  % (18679)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.56  % (18674)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.56  % (18666)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.56  % (18667)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.56  % (18683)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.56  % (18671)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.56  % (18668)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.56  % (18677)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.56  % (18663)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.57  % (18680)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.57  % (18675)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.57  % (18665)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.57  % (18682)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.58  % (18685)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.56/0.58  % (18684)Refutation not found, incomplete strategy% (18684)------------------------------
% 1.56/0.58  % (18684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (18684)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (18684)Memory used [KB]: 11001
% 1.56/0.58  % (18684)Time elapsed: 0.156 s
% 1.56/0.58  % (18684)------------------------------
% 1.56/0.58  % (18684)------------------------------
% 1.56/0.58  % (18666)Refutation not found, incomplete strategy% (18666)------------------------------
% 1.56/0.58  % (18666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (18666)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (18666)Memory used [KB]: 11001
% 1.56/0.58  % (18666)Time elapsed: 0.142 s
% 1.56/0.58  % (18666)------------------------------
% 1.56/0.58  % (18666)------------------------------
% 1.56/0.61  % (18677)Refutation found. Thanks to Tanya!
% 1.56/0.61  % SZS status Theorem for theBenchmark
% 1.56/0.61  % SZS output start Proof for theBenchmark
% 1.56/0.61  fof(f751,plain,(
% 1.56/0.61    $false),
% 1.56/0.61    inference(avatar_sat_refutation,[],[f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f175,f185,f191,f199,f255,f272,f385,f406,f437,f456,f484,f519,f563,f604,f621,f691,f722])).
% 1.56/0.61  fof(f722,plain,(
% 1.56/0.61    spl4_1 | ~spl4_9 | ~spl4_14 | ~spl4_39 | ~spl4_46),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f721])).
% 1.56/0.61  fof(f721,plain,(
% 1.56/0.61    $false | (spl4_1 | ~spl4_9 | ~spl4_14 | ~spl4_39 | ~spl4_46)),
% 1.56/0.61    inference(subsumption_resolution,[],[f720,f184])).
% 1.56/0.61  fof(f184,plain,(
% 1.56/0.61    v1_relat_1(sK3) | ~spl4_14),
% 1.56/0.61    inference(avatar_component_clause,[],[f182])).
% 1.56/0.61  fof(f182,plain,(
% 1.56/0.61    spl4_14 <=> v1_relat_1(sK3)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.56/0.61  fof(f720,plain,(
% 1.56/0.61    ~v1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_39 | ~spl4_46)),
% 1.56/0.61    inference(subsumption_resolution,[],[f719,f153])).
% 1.56/0.61  fof(f153,plain,(
% 1.56/0.61    v1_funct_1(sK3) | ~spl4_9),
% 1.56/0.61    inference(avatar_component_clause,[],[f151])).
% 1.56/0.61  fof(f151,plain,(
% 1.56/0.61    spl4_9 <=> v1_funct_1(sK3)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.56/0.61  fof(f719,plain,(
% 1.56/0.61    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_39 | ~spl4_46)),
% 1.56/0.61    inference(subsumption_resolution,[],[f718,f455])).
% 1.56/0.61  fof(f455,plain,(
% 1.56/0.61    v2_funct_1(sK3) | ~spl4_39),
% 1.56/0.61    inference(avatar_component_clause,[],[f453])).
% 1.56/0.61  fof(f453,plain,(
% 1.56/0.61    spl4_39 <=> v2_funct_1(sK3)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.56/0.61  fof(f718,plain,(
% 1.56/0.61    ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_46)),
% 1.56/0.61    inference(subsumption_resolution,[],[f697,f113])).
% 1.56/0.61  fof(f113,plain,(
% 1.56/0.61    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.56/0.61    inference(avatar_component_clause,[],[f111])).
% 1.56/0.61  fof(f111,plain,(
% 1.56/0.61    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.56/0.61  fof(f697,plain,(
% 1.56/0.61    k2_funct_1(sK2) = sK3 | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_46),
% 1.56/0.61    inference(superposition,[],[f74,f616])).
% 1.56/0.61  fof(f616,plain,(
% 1.56/0.61    sK2 = k2_funct_1(sK3) | ~spl4_46),
% 1.56/0.61    inference(avatar_component_clause,[],[f614])).
% 1.56/0.61  fof(f614,plain,(
% 1.56/0.61    spl4_46 <=> sK2 = k2_funct_1(sK3)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.56/0.61  fof(f74,plain,(
% 1.56/0.61    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f33])).
% 1.56/0.61  fof(f33,plain,(
% 1.56/0.61    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.61    inference(flattening,[],[f32])).
% 1.56/0.61  fof(f32,plain,(
% 1.56/0.61    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.61    inference(ennf_transformation,[],[f8])).
% 1.56/0.61  fof(f8,axiom,(
% 1.56/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.56/0.61  fof(f691,plain,(
% 1.56/0.61    ~spl4_14 | ~spl4_16 | ~spl4_37 | spl4_47),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f690])).
% 1.56/0.61  fof(f690,plain,(
% 1.56/0.61    $false | (~spl4_14 | ~spl4_16 | ~spl4_37 | spl4_47)),
% 1.56/0.61    inference(subsumption_resolution,[],[f689,f198])).
% 1.56/0.61  fof(f198,plain,(
% 1.56/0.61    v5_relat_1(sK3,sK0) | ~spl4_16),
% 1.56/0.61    inference(avatar_component_clause,[],[f196])).
% 1.56/0.61  fof(f196,plain,(
% 1.56/0.61    spl4_16 <=> v5_relat_1(sK3,sK0)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.56/0.61  fof(f689,plain,(
% 1.56/0.61    ~v5_relat_1(sK3,sK0) | (~spl4_14 | ~spl4_37 | spl4_47)),
% 1.56/0.61    inference(subsumption_resolution,[],[f688,f436])).
% 1.56/0.61  fof(f436,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | ~spl4_37),
% 1.56/0.61    inference(avatar_component_clause,[],[f434])).
% 1.56/0.61  fof(f434,plain,(
% 1.56/0.61    spl4_37 <=> v2_funct_2(sK3,sK0)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.56/0.61  fof(f688,plain,(
% 1.56/0.61    ~v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | (~spl4_14 | spl4_47)),
% 1.56/0.61    inference(equality_resolution,[],[f676])).
% 1.56/0.61  fof(f676,plain,(
% 1.56/0.61    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0)) ) | (~spl4_14 | spl4_47)),
% 1.56/0.61    inference(subsumption_resolution,[],[f675,f184])).
% 1.56/0.61  fof(f675,plain,(
% 1.56/0.61    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_47),
% 1.56/0.61    inference(superposition,[],[f620,f99])).
% 1.56/0.61  fof(f99,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f56])).
% 1.56/0.61  fof(f56,plain,(
% 1.56/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.56/0.61    inference(nnf_transformation,[],[f49])).
% 1.56/0.61  fof(f49,plain,(
% 1.56/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.56/0.61    inference(flattening,[],[f48])).
% 1.56/0.61  fof(f48,plain,(
% 1.56/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.56/0.61    inference(ennf_transformation,[],[f13])).
% 1.56/0.61  fof(f13,axiom,(
% 1.56/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.56/0.61  fof(f620,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | spl4_47),
% 1.56/0.61    inference(avatar_component_clause,[],[f618])).
% 1.56/0.61  fof(f618,plain,(
% 1.56/0.61    spl4_47 <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.56/0.61  fof(f621,plain,(
% 1.56/0.61    spl4_46 | ~spl4_47 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_35 | ~spl4_39 | ~spl4_43),
% 1.56/0.61    inference(avatar_split_clause,[],[f611,f490,f453,f398,f267,f188,f182,f166,f151,f618,f614])).
% 1.56/0.61  fof(f166,plain,(
% 1.56/0.61    spl4_12 <=> v1_funct_1(sK2)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.56/0.61  fof(f188,plain,(
% 1.56/0.61    spl4_15 <=> v1_relat_1(sK2)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.56/0.61  fof(f267,plain,(
% 1.56/0.61    spl4_24 <=> sK1 = k1_relat_1(sK3)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.56/0.61  fof(f398,plain,(
% 1.56/0.61    spl4_35 <=> sK1 = k2_relat_1(sK2)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.56/0.61  fof(f490,plain,(
% 1.56/0.61    spl4_43 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.56/0.61  fof(f611,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_35 | ~spl4_39 | ~spl4_43)),
% 1.56/0.61    inference(subsumption_resolution,[],[f610,f400])).
% 1.56/0.61  fof(f400,plain,(
% 1.56/0.61    sK1 = k2_relat_1(sK2) | ~spl4_35),
% 1.56/0.61    inference(avatar_component_clause,[],[f398])).
% 1.56/0.61  fof(f610,plain,(
% 1.56/0.61    sK1 != k2_relat_1(sK2) | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_39 | ~spl4_43)),
% 1.56/0.61    inference(forward_demodulation,[],[f609,f269])).
% 1.56/0.61  fof(f269,plain,(
% 1.56/0.61    sK1 = k1_relat_1(sK3) | ~spl4_24),
% 1.56/0.61    inference(avatar_component_clause,[],[f267])).
% 1.56/0.61  fof(f609,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_39 | ~spl4_43)),
% 1.56/0.61    inference(subsumption_resolution,[],[f608,f184])).
% 1.56/0.61  fof(f608,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_39 | ~spl4_43)),
% 1.56/0.61    inference(subsumption_resolution,[],[f607,f153])).
% 1.56/0.61  fof(f607,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_39 | ~spl4_43)),
% 1.56/0.61    inference(subsumption_resolution,[],[f606,f190])).
% 1.56/0.61  fof(f190,plain,(
% 1.56/0.61    v1_relat_1(sK2) | ~spl4_15),
% 1.56/0.61    inference(avatar_component_clause,[],[f188])).
% 1.56/0.61  fof(f606,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_39 | ~spl4_43)),
% 1.56/0.61    inference(subsumption_resolution,[],[f605,f168])).
% 1.56/0.61  fof(f168,plain,(
% 1.56/0.61    v1_funct_1(sK2) | ~spl4_12),
% 1.56/0.61    inference(avatar_component_clause,[],[f166])).
% 1.56/0.61  fof(f605,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_39 | ~spl4_43)),
% 1.56/0.61    inference(subsumption_resolution,[],[f602,f455])).
% 1.56/0.61  fof(f602,plain,(
% 1.56/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_43),
% 1.56/0.61    inference(superposition,[],[f71,f492])).
% 1.56/0.61  fof(f492,plain,(
% 1.56/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_43),
% 1.56/0.61    inference(avatar_component_clause,[],[f490])).
% 1.56/0.61  fof(f71,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f29])).
% 1.56/0.61  fof(f29,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.61    inference(flattening,[],[f28])).
% 1.56/0.61  fof(f28,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.61    inference(ennf_transformation,[],[f7])).
% 1.56/0.61  fof(f7,axiom,(
% 1.56/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.56/0.61  fof(f604,plain,(
% 1.56/0.61    spl4_38 | ~spl4_43),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f603])).
% 1.56/0.61  fof(f603,plain,(
% 1.56/0.61    $false | (spl4_38 | ~spl4_43)),
% 1.56/0.61    inference(subsumption_resolution,[],[f600,f86])).
% 1.56/0.61  fof(f86,plain,(
% 1.56/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f4])).
% 1.56/0.61  fof(f4,axiom,(
% 1.56/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.56/0.61  fof(f600,plain,(
% 1.56/0.61    ~v2_funct_1(k6_relat_1(sK0)) | (spl4_38 | ~spl4_43)),
% 1.56/0.61    inference(backward_demodulation,[],[f451,f492])).
% 1.56/0.61  fof(f451,plain,(
% 1.56/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_38),
% 1.56/0.61    inference(avatar_component_clause,[],[f449])).
% 1.56/0.61  fof(f449,plain,(
% 1.56/0.61    spl4_38 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.56/0.61  fof(f563,plain,(
% 1.56/0.61    spl4_43 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_41),
% 1.56/0.61    inference(avatar_split_clause,[],[f562,f481,f166,f156,f151,f141,f490])).
% 1.56/0.61  fof(f141,plain,(
% 1.56/0.61    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.56/0.61  fof(f156,plain,(
% 1.56/0.61    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.56/0.61  fof(f481,plain,(
% 1.56/0.61    spl4_41 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.56/0.61  fof(f562,plain,(
% 1.56/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_41)),
% 1.56/0.61    inference(subsumption_resolution,[],[f561,f168])).
% 1.56/0.61  fof(f561,plain,(
% 1.56/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_41)),
% 1.56/0.61    inference(subsumption_resolution,[],[f560,f158])).
% 1.56/0.61  fof(f158,plain,(
% 1.56/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.56/0.61    inference(avatar_component_clause,[],[f156])).
% 1.56/0.61  fof(f560,plain,(
% 1.56/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_41)),
% 1.56/0.61    inference(subsumption_resolution,[],[f559,f153])).
% 1.56/0.61  fof(f559,plain,(
% 1.56/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_41)),
% 1.56/0.61    inference(subsumption_resolution,[],[f550,f143])).
% 1.56/0.61  fof(f143,plain,(
% 1.56/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.56/0.61    inference(avatar_component_clause,[],[f141])).
% 1.56/0.61  fof(f550,plain,(
% 1.56/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_41),
% 1.56/0.61    inference(superposition,[],[f93,f483])).
% 1.56/0.61  fof(f483,plain,(
% 1.56/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_41),
% 1.56/0.61    inference(avatar_component_clause,[],[f481])).
% 1.56/0.61  fof(f93,plain,(
% 1.56/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f45])).
% 1.56/0.61  fof(f45,plain,(
% 1.56/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.56/0.61    inference(flattening,[],[f44])).
% 1.56/0.61  fof(f44,plain,(
% 1.56/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.56/0.61    inference(ennf_transformation,[],[f16])).
% 1.56/0.61  fof(f16,axiom,(
% 1.56/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.56/0.61  fof(f519,plain,(
% 1.56/0.61    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_40),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f518])).
% 1.56/0.61  fof(f518,plain,(
% 1.56/0.61    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_40)),
% 1.56/0.61    inference(subsumption_resolution,[],[f517,f168])).
% 1.56/0.61  fof(f517,plain,(
% 1.56/0.61    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_40)),
% 1.56/0.61    inference(subsumption_resolution,[],[f516,f158])).
% 1.56/0.61  fof(f516,plain,(
% 1.56/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_40)),
% 1.56/0.61    inference(subsumption_resolution,[],[f515,f153])).
% 1.56/0.61  fof(f515,plain,(
% 1.56/0.61    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_40)),
% 1.56/0.61    inference(subsumption_resolution,[],[f512,f143])).
% 1.56/0.61  fof(f512,plain,(
% 1.56/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_40),
% 1.56/0.61    inference(resolution,[],[f479,f92])).
% 1.56/0.61  fof(f92,plain,(
% 1.56/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f43])).
% 1.56/0.61  fof(f43,plain,(
% 1.56/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.56/0.61    inference(flattening,[],[f42])).
% 1.56/0.61  fof(f42,plain,(
% 1.56/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.56/0.61    inference(ennf_transformation,[],[f14])).
% 1.56/0.61  fof(f14,axiom,(
% 1.56/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.56/0.61  fof(f479,plain,(
% 1.56/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_40),
% 1.56/0.61    inference(avatar_component_clause,[],[f477])).
% 1.56/0.61  fof(f477,plain,(
% 1.56/0.61    spl4_40 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.56/0.61  fof(f484,plain,(
% 1.56/0.61    ~spl4_40 | spl4_41 | ~spl4_13),
% 1.56/0.61    inference(avatar_split_clause,[],[f473,f172,f481,f477])).
% 1.56/0.61  fof(f172,plain,(
% 1.56/0.61    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.56/0.61  fof(f473,plain,(
% 1.56/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.56/0.61    inference(resolution,[],[f305,f174])).
% 1.56/0.61  fof(f174,plain,(
% 1.56/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.56/0.61    inference(avatar_component_clause,[],[f172])).
% 1.56/0.61  fof(f305,plain,(
% 1.56/0.61    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.56/0.61    inference(resolution,[],[f87,f176])).
% 1.56/0.61  fof(f176,plain,(
% 1.56/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f89,f90])).
% 1.56/0.61  fof(f90,plain,(
% 1.56/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f17])).
% 1.56/0.61  fof(f17,axiom,(
% 1.56/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.56/0.61  fof(f89,plain,(
% 1.56/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f22])).
% 1.56/0.61  fof(f22,plain,(
% 1.56/0.61    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.56/0.61    inference(pure_predicate_removal,[],[f15])).
% 1.56/0.61  fof(f15,axiom,(
% 1.56/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.56/0.61  fof(f87,plain,(
% 1.56/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f55])).
% 1.56/0.61  fof(f55,plain,(
% 1.56/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.61    inference(nnf_transformation,[],[f41])).
% 1.56/0.61  fof(f41,plain,(
% 1.56/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.61    inference(flattening,[],[f40])).
% 1.56/0.61  fof(f40,plain,(
% 1.56/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.56/0.61    inference(ennf_transformation,[],[f11])).
% 1.56/0.61  fof(f11,axiom,(
% 1.56/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.56/0.61  fof(f456,plain,(
% 1.56/0.61    ~spl4_38 | spl4_39 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_35),
% 1.56/0.61    inference(avatar_split_clause,[],[f447,f398,f267,f188,f182,f166,f151,f453,f449])).
% 1.56/0.61  fof(f447,plain,(
% 1.56/0.61    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_35)),
% 1.56/0.61    inference(subsumption_resolution,[],[f446,f184])).
% 1.56/0.61  fof(f446,plain,(
% 1.56/0.61    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_24 | ~spl4_35)),
% 1.56/0.61    inference(subsumption_resolution,[],[f445,f153])).
% 1.56/0.61  fof(f445,plain,(
% 1.56/0.61    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_24 | ~spl4_35)),
% 1.56/0.61    inference(trivial_inequality_removal,[],[f444])).
% 1.56/0.61  fof(f444,plain,(
% 1.56/0.61    sK1 != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_24 | ~spl4_35)),
% 1.56/0.61    inference(superposition,[],[f415,f269])).
% 1.56/0.61  fof(f415,plain,(
% 1.56/0.61    ( ! [X0] : (k1_relat_1(X0) != sK1 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK2,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_12 | ~spl4_15 | ~spl4_35)),
% 1.56/0.61    inference(subsumption_resolution,[],[f414,f190])).
% 1.56/0.61  fof(f414,plain,(
% 1.56/0.61    ( ! [X0] : (k1_relat_1(X0) != sK1 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_12 | ~spl4_35)),
% 1.56/0.61    inference(subsumption_resolution,[],[f409,f168])).
% 1.56/0.61  fof(f409,plain,(
% 1.56/0.61    ( ! [X0] : (k1_relat_1(X0) != sK1 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK2,X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_35),
% 1.56/0.61    inference(superposition,[],[f84,f400])).
% 1.56/0.61  fof(f84,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f39])).
% 1.56/0.61  fof(f39,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.61    inference(flattening,[],[f38])).
% 1.56/0.61  fof(f38,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.61    inference(ennf_transformation,[],[f5])).
% 1.56/0.61  fof(f5,axiom,(
% 1.56/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.56/0.61  fof(f437,plain,(
% 1.56/0.61    spl4_37 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.56/0.61    inference(avatar_split_clause,[],[f432,f172,f166,f161,f156,f151,f146,f141,f434])).
% 1.56/0.61  fof(f146,plain,(
% 1.56/0.61    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.56/0.61  fof(f161,plain,(
% 1.56/0.61    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.56/0.61  fof(f432,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.56/0.61    inference(subsumption_resolution,[],[f431,f168])).
% 1.56/0.61  fof(f431,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.56/0.61    inference(subsumption_resolution,[],[f430,f163])).
% 1.56/0.61  fof(f163,plain,(
% 1.56/0.61    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.56/0.61    inference(avatar_component_clause,[],[f161])).
% 1.56/0.61  fof(f430,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.56/0.61    inference(subsumption_resolution,[],[f429,f158])).
% 1.56/0.61  fof(f429,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_13)),
% 1.56/0.61    inference(subsumption_resolution,[],[f428,f153])).
% 1.56/0.61  fof(f428,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_13)),
% 1.56/0.61    inference(subsumption_resolution,[],[f427,f148])).
% 1.56/0.61  fof(f148,plain,(
% 1.56/0.61    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.56/0.61    inference(avatar_component_clause,[],[f146])).
% 1.56/0.61  fof(f427,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.56/0.61    inference(subsumption_resolution,[],[f424,f143])).
% 1.56/0.61  fof(f424,plain,(
% 1.56/0.61    v2_funct_2(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.56/0.61    inference(resolution,[],[f407,f174])).
% 1.56/0.61  fof(f407,plain,(
% 1.56/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | v2_funct_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.56/0.61    inference(forward_demodulation,[],[f82,f90])).
% 1.56/0.61  fof(f82,plain,(
% 1.56/0.61    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f37])).
% 1.56/0.61  fof(f37,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.56/0.61    inference(flattening,[],[f36])).
% 1.56/0.61  fof(f36,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.56/0.61    inference(ennf_transformation,[],[f18])).
% 1.56/0.61  fof(f18,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.56/0.61  fof(f406,plain,(
% 1.56/0.61    spl4_35 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_34),
% 1.56/0.61    inference(avatar_split_clause,[],[f405,f382,f188,f166,f126,f398])).
% 1.56/0.61  fof(f126,plain,(
% 1.56/0.61    spl4_4 <=> v2_funct_1(sK2)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.56/0.61  fof(f382,plain,(
% 1.56/0.61    spl4_34 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.56/0.61  fof(f405,plain,(
% 1.56/0.61    sK1 = k2_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_34)),
% 1.56/0.61    inference(forward_demodulation,[],[f404,f94])).
% 1.56/0.61  fof(f94,plain,(
% 1.56/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.56/0.61    inference(cnf_transformation,[],[f3])).
% 1.56/0.61  fof(f3,axiom,(
% 1.56/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.56/0.61  fof(f404,plain,(
% 1.56/0.61    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_34)),
% 1.56/0.61    inference(subsumption_resolution,[],[f403,f190])).
% 1.56/0.61  fof(f403,plain,(
% 1.56/0.61    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_34)),
% 1.56/0.61    inference(subsumption_resolution,[],[f402,f168])).
% 1.56/0.61  fof(f402,plain,(
% 1.56/0.61    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_34)),
% 1.56/0.61    inference(subsumption_resolution,[],[f391,f128])).
% 1.56/0.61  fof(f128,plain,(
% 1.56/0.61    v2_funct_1(sK2) | ~spl4_4),
% 1.56/0.61    inference(avatar_component_clause,[],[f126])).
% 1.56/0.61  fof(f391,plain,(
% 1.56/0.61    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_34),
% 1.56/0.61    inference(superposition,[],[f72,f384])).
% 1.56/0.61  fof(f384,plain,(
% 1.56/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_34),
% 1.56/0.61    inference(avatar_component_clause,[],[f382])).
% 1.56/0.61  fof(f72,plain,(
% 1.56/0.61    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f31])).
% 1.56/0.61  fof(f31,plain,(
% 1.56/0.61    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.61    inference(flattening,[],[f30])).
% 1.56/0.61  fof(f30,plain,(
% 1.56/0.61    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.61    inference(ennf_transformation,[],[f6])).
% 1.56/0.61  fof(f6,axiom,(
% 1.56/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 1.56/0.61  fof(f385,plain,(
% 1.56/0.61    spl4_34 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.56/0.61    inference(avatar_split_clause,[],[f380,f166,f161,f156,f136,f126,f116,f382])).
% 1.56/0.61  fof(f116,plain,(
% 1.56/0.61    spl4_2 <=> k1_xboole_0 = sK1),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.56/0.61  fof(f136,plain,(
% 1.56/0.61    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.56/0.61  fof(f380,plain,(
% 1.56/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.56/0.61    inference(subsumption_resolution,[],[f379,f168])).
% 1.56/0.61  fof(f379,plain,(
% 1.56/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.56/0.61    inference(subsumption_resolution,[],[f378,f163])).
% 1.56/0.61  fof(f378,plain,(
% 1.56/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.56/0.61    inference(subsumption_resolution,[],[f377,f158])).
% 1.56/0.61  fof(f377,plain,(
% 1.56/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.56/0.61    inference(subsumption_resolution,[],[f376,f128])).
% 1.56/0.61  fof(f376,plain,(
% 1.56/0.61    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.56/0.61    inference(subsumption_resolution,[],[f375,f118])).
% 1.56/0.61  fof(f118,plain,(
% 1.56/0.61    k1_xboole_0 != sK1 | spl4_2),
% 1.56/0.61    inference(avatar_component_clause,[],[f116])).
% 1.56/0.61  fof(f375,plain,(
% 1.56/0.61    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.56/0.61    inference(trivial_inequality_removal,[],[f374])).
% 1.56/0.61  fof(f374,plain,(
% 1.56/0.61    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.56/0.61    inference(superposition,[],[f333,f138])).
% 1.56/0.61  fof(f138,plain,(
% 1.56/0.61    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.56/0.61    inference(avatar_component_clause,[],[f136])).
% 1.56/0.61  fof(f333,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.56/0.61    inference(forward_demodulation,[],[f70,f90])).
% 1.56/0.61  fof(f70,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f27])).
% 1.56/0.61  fof(f27,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.56/0.61    inference(flattening,[],[f26])).
% 1.56/0.61  fof(f26,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.56/0.61    inference(ennf_transformation,[],[f19])).
% 1.56/0.61  fof(f19,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.56/0.61  fof(f272,plain,(
% 1.56/0.61    spl4_24 | ~spl4_7 | ~spl4_22),
% 1.56/0.61    inference(avatar_split_clause,[],[f271,f252,f141,f267])).
% 1.56/0.61  fof(f252,plain,(
% 1.56/0.61    spl4_22 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.56/0.61  fof(f271,plain,(
% 1.56/0.61    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_22)),
% 1.56/0.61    inference(subsumption_resolution,[],[f264,f143])).
% 1.56/0.61  fof(f264,plain,(
% 1.56/0.61    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_22),
% 1.56/0.61    inference(superposition,[],[f98,f254])).
% 1.56/0.61  fof(f254,plain,(
% 1.56/0.61    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_22),
% 1.56/0.61    inference(avatar_component_clause,[],[f252])).
% 1.56/0.61  fof(f98,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f47])).
% 1.56/0.61  fof(f47,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.61    inference(ennf_transformation,[],[f10])).
% 1.56/0.61  fof(f10,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.56/0.61  fof(f255,plain,(
% 1.56/0.61    spl4_22 | spl4_3 | ~spl4_7 | ~spl4_8),
% 1.56/0.61    inference(avatar_split_clause,[],[f250,f146,f141,f121,f252])).
% 1.56/0.61  fof(f121,plain,(
% 1.56/0.61    spl4_3 <=> k1_xboole_0 = sK0),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.56/0.61  fof(f250,plain,(
% 1.56/0.61    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 1.56/0.61    inference(subsumption_resolution,[],[f249,f123])).
% 1.56/0.61  fof(f123,plain,(
% 1.56/0.61    k1_xboole_0 != sK0 | spl4_3),
% 1.56/0.61    inference(avatar_component_clause,[],[f121])).
% 1.56/0.61  fof(f249,plain,(
% 1.56/0.61    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 1.56/0.61    inference(subsumption_resolution,[],[f246,f148])).
% 1.56/0.61  fof(f246,plain,(
% 1.56/0.61    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 1.56/0.61    inference(resolution,[],[f75,f143])).
% 1.56/0.61  fof(f75,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.56/0.61    inference(cnf_transformation,[],[f54])).
% 1.56/0.61  fof(f54,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.61    inference(nnf_transformation,[],[f35])).
% 1.56/0.61  fof(f35,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.61    inference(flattening,[],[f34])).
% 1.56/0.61  fof(f34,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.61    inference(ennf_transformation,[],[f12])).
% 1.56/0.61  fof(f12,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.56/0.61  fof(f199,plain,(
% 1.56/0.61    spl4_16 | ~spl4_7),
% 1.56/0.61    inference(avatar_split_clause,[],[f192,f141,f196])).
% 1.56/0.61  fof(f192,plain,(
% 1.56/0.61    v5_relat_1(sK3,sK0) | ~spl4_7),
% 1.56/0.61    inference(resolution,[],[f101,f143])).
% 1.56/0.61  fof(f101,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f50])).
% 1.56/0.61  fof(f50,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.61    inference(ennf_transformation,[],[f23])).
% 1.56/0.61  fof(f23,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.56/0.61    inference(pure_predicate_removal,[],[f9])).
% 1.56/0.61  fof(f9,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.56/0.61  fof(f191,plain,(
% 1.56/0.61    spl4_15 | ~spl4_10),
% 1.56/0.61    inference(avatar_split_clause,[],[f186,f156,f188])).
% 1.56/0.61  fof(f186,plain,(
% 1.56/0.61    v1_relat_1(sK2) | ~spl4_10),
% 1.56/0.61    inference(subsumption_resolution,[],[f178,f97])).
% 1.56/0.61  fof(f97,plain,(
% 1.56/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f2])).
% 1.56/0.61  fof(f2,axiom,(
% 1.56/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.56/0.61  fof(f178,plain,(
% 1.56/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 1.56/0.61    inference(resolution,[],[f96,f158])).
% 1.56/0.61  fof(f96,plain,(
% 1.56/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f46])).
% 1.56/0.61  fof(f46,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.56/0.61    inference(ennf_transformation,[],[f1])).
% 1.56/0.61  fof(f1,axiom,(
% 1.56/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.56/0.61  fof(f185,plain,(
% 1.56/0.61    spl4_14 | ~spl4_7),
% 1.56/0.61    inference(avatar_split_clause,[],[f180,f141,f182])).
% 1.56/0.61  fof(f180,plain,(
% 1.56/0.61    v1_relat_1(sK3) | ~spl4_7),
% 1.56/0.61    inference(subsumption_resolution,[],[f177,f97])).
% 1.56/0.61  fof(f177,plain,(
% 1.56/0.61    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 1.56/0.61    inference(resolution,[],[f96,f143])).
% 1.56/0.61  fof(f175,plain,(
% 1.56/0.61    spl4_13 | ~spl4_5),
% 1.56/0.61    inference(avatar_split_clause,[],[f170,f131,f172])).
% 1.56/0.61  fof(f131,plain,(
% 1.56/0.61    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.56/0.61  fof(f170,plain,(
% 1.56/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.56/0.61    inference(backward_demodulation,[],[f133,f90])).
% 1.56/0.61  fof(f133,plain,(
% 1.56/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.56/0.61    inference(avatar_component_clause,[],[f131])).
% 1.56/0.61  fof(f169,plain,(
% 1.56/0.61    spl4_12),
% 1.56/0.61    inference(avatar_split_clause,[],[f57,f166])).
% 1.56/0.61  fof(f57,plain,(
% 1.56/0.61    v1_funct_1(sK2)),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f53,plain,(
% 1.56/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.56/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f52,f51])).
% 1.56/0.61  fof(f51,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.56/0.61    introduced(choice_axiom,[])).
% 1.56/0.61  fof(f52,plain,(
% 1.56/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.56/0.61    introduced(choice_axiom,[])).
% 1.56/0.61  fof(f25,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.56/0.61    inference(flattening,[],[f24])).
% 1.56/0.61  fof(f24,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.56/0.61    inference(ennf_transformation,[],[f21])).
% 1.56/0.61  fof(f21,negated_conjecture,(
% 1.56/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.56/0.61    inference(negated_conjecture,[],[f20])).
% 1.56/0.61  fof(f20,conjecture,(
% 1.56/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.56/0.61  fof(f164,plain,(
% 1.56/0.61    spl4_11),
% 1.56/0.61    inference(avatar_split_clause,[],[f58,f161])).
% 1.56/0.61  fof(f58,plain,(
% 1.56/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f159,plain,(
% 1.56/0.61    spl4_10),
% 1.56/0.61    inference(avatar_split_clause,[],[f59,f156])).
% 1.56/0.61  fof(f59,plain,(
% 1.56/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f154,plain,(
% 1.56/0.61    spl4_9),
% 1.56/0.61    inference(avatar_split_clause,[],[f60,f151])).
% 1.56/0.61  fof(f60,plain,(
% 1.56/0.61    v1_funct_1(sK3)),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f149,plain,(
% 1.56/0.61    spl4_8),
% 1.56/0.61    inference(avatar_split_clause,[],[f61,f146])).
% 1.56/0.61  fof(f61,plain,(
% 1.56/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f144,plain,(
% 1.56/0.61    spl4_7),
% 1.56/0.61    inference(avatar_split_clause,[],[f62,f141])).
% 1.56/0.61  fof(f62,plain,(
% 1.56/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f139,plain,(
% 1.56/0.61    spl4_6),
% 1.56/0.61    inference(avatar_split_clause,[],[f63,f136])).
% 1.56/0.61  fof(f63,plain,(
% 1.56/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f134,plain,(
% 1.56/0.61    spl4_5),
% 1.56/0.61    inference(avatar_split_clause,[],[f64,f131])).
% 1.56/0.61  fof(f64,plain,(
% 1.56/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f129,plain,(
% 1.56/0.61    spl4_4),
% 1.56/0.61    inference(avatar_split_clause,[],[f65,f126])).
% 1.56/0.61  fof(f65,plain,(
% 1.56/0.61    v2_funct_1(sK2)),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f124,plain,(
% 1.56/0.61    ~spl4_3),
% 1.56/0.61    inference(avatar_split_clause,[],[f66,f121])).
% 1.56/0.61  fof(f66,plain,(
% 1.56/0.61    k1_xboole_0 != sK0),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f119,plain,(
% 1.56/0.61    ~spl4_2),
% 1.56/0.61    inference(avatar_split_clause,[],[f67,f116])).
% 1.56/0.61  fof(f67,plain,(
% 1.56/0.61    k1_xboole_0 != sK1),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  fof(f114,plain,(
% 1.56/0.61    ~spl4_1),
% 1.56/0.61    inference(avatar_split_clause,[],[f68,f111])).
% 1.56/0.61  fof(f68,plain,(
% 1.56/0.61    k2_funct_1(sK2) != sK3),
% 1.56/0.61    inference(cnf_transformation,[],[f53])).
% 1.56/0.61  % SZS output end Proof for theBenchmark
% 1.56/0.61  % (18677)------------------------------
% 1.56/0.61  % (18677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (18677)Termination reason: Refutation
% 1.56/0.61  
% 1.56/0.61  % (18677)Memory used [KB]: 6780
% 1.56/0.61  % (18677)Time elapsed: 0.189 s
% 1.56/0.61  % (18677)------------------------------
% 1.56/0.61  % (18677)------------------------------
% 1.56/0.62  % (18655)Success in time 0.246 s
%------------------------------------------------------------------------------
