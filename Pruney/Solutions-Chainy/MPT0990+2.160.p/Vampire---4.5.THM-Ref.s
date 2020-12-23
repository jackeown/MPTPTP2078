%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:56 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 389 expanded)
%              Number of leaves         :   42 ( 157 expanded)
%              Depth                    :   16
%              Number of atoms          :  802 (2198 expanded)
%              Number of equality atoms :  203 ( 663 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f488,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f151,f161,f167,f208,f215,f225,f244,f260,f309,f325,f379,f416,f455,f487])).

fof(f487,plain,
    ( spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f485,f222])).

fof(f222,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_22
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f485,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f484,f376])).

fof(f376,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl4_36
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f484,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_40 ),
    inference(trivial_inequality_removal,[],[f483])).

fof(f483,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f482,f241])).

fof(f241,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl4_23
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f482,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f481,f166])).

fof(f166,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f481,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f480,f144])).

fof(f144,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f480,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f479,f160])).

fof(f160,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f479,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f478,f129])).

fof(f129,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f478,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f474,f89])).

fof(f89,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f474,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_40 ),
    inference(superposition,[],[f245,f415])).

fof(f415,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl4_40
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f245,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f455,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f144,f129,f134,f119,f411,f268])).

fof(f268,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f72,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f411,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl4_39
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f119,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f416,plain,
    ( ~ spl4_39
    | spl4_40
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f397,f257,f413,f409])).

fof(f257,plain,
    ( spl4_24
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f397,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_24 ),
    inference(resolution,[],[f232,f259])).

fof(f259,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f257])).

fof(f232,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f67,f152])).

fof(f152,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f69,f70])).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f379,plain,
    ( spl4_36
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f378,f318,f374])).

fof(f318,plain,
    ( spl4_27
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f378,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f361,f74])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f361,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_27 ),
    inference(superposition,[],[f74,f320])).

fof(f320,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f318])).

fof(f325,plain,
    ( spl4_27
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f324,f306,f164,f142,f102,f318])).

fof(f102,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f306,plain,
    ( spl4_26
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f324,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f323,f166])).

fof(f323,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f322,f144])).

fof(f322,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f311,f104])).

fof(f104,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f311,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f59,f308])).

fof(f308,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f306])).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f309,plain,
    ( spl4_26
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f304,f142,f137,f132,f112,f102,f92,f306])).

fof(f92,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f112,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f137,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f304,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f303,f144])).

fof(f303,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f302,f139])).

fof(f139,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f302,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f301,f134])).

fof(f301,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f300,f104])).

fof(f300,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f299,f94])).

fof(f94,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f299,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f298])).

fof(f298,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f273,f114])).

fof(f114,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f56,f70])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f260,plain,
    ( spl4_24
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f255,f148,f142,f132,f127,f117,f257])).

fof(f148,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f255,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f254,f144])).

fof(f254,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f253,f134])).

fof(f253,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f252,f129])).

fof(f252,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f249,f119])).

fof(f249,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f150,f73])).

fof(f150,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f244,plain,
    ( spl4_23
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f243,f212,f132,f239])).

fof(f212,plain,
    ( spl4_21
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f243,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f235,f134])).

fof(f235,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_21 ),
    inference(superposition,[],[f76,f214])).

fof(f214,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f212])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f225,plain,
    ( spl4_22
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f224,f205,f117,f220])).

fof(f205,plain,
    ( spl4_20
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f224,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f217,f119])).

fof(f217,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_20 ),
    inference(superposition,[],[f76,f207])).

fof(f207,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f215,plain,
    ( spl4_21
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f210,f137,f132,f92,f212])).

fof(f210,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f209,f94])).

fof(f209,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f200,f139])).

fof(f200,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f60,f134])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f208,plain,
    ( spl4_20
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f203,f122,f117,f97,f205])).

fof(f97,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f122,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f203,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f202,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f199,f124])).

fof(f124,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f199,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f60,f119])).

fof(f167,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f162,f132,f164])).

fof(f162,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f154,f78])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f154,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f77,f134])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f161,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f156,f117,f158])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f153,f78])).

fof(f153,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f77,f119])).

fof(f151,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f146,f107,f148])).

fof(f107,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f146,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f109,f70])).

fof(f109,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f145,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f43,f142])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f140,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f44,f137])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f135,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f45,f132])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f130,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f46,f127])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f125,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f47,f122])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f120,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f115,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f49,f112])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f50,f107])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f102])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f52,f97])).

fof(f52,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f92])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f87])).

fof(f54,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:09:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (29194)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (29186)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.57  % (29187)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.58  % (29193)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.58  % (29189)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (29202)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.58  % (29188)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.59  % (29203)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.59  % (29185)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.59  % (29184)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.60  % (29183)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.61  % (29195)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.61  % (29206)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.61  % (29198)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.62  % (29197)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.62  % (29204)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.62  % (29205)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.62  % (29201)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.62  % (29191)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.62  % (29196)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.63  % (29190)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.63  % (29207)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.63  % (29212)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.63  % (29200)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.63  % (29199)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.64  % (29211)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.88/0.64  % (29199)Refutation not found, incomplete strategy% (29199)------------------------------
% 1.88/0.64  % (29199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.64  % (29199)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.64  
% 1.88/0.64  % (29199)Memory used [KB]: 10746
% 1.88/0.64  % (29199)Time elapsed: 0.196 s
% 1.88/0.64  % (29199)------------------------------
% 1.88/0.64  % (29199)------------------------------
% 1.88/0.64  % (29209)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.88/0.65  % (29210)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.18/0.66  % (29192)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.27/0.67  % (29204)Refutation found. Thanks to Tanya!
% 2.27/0.67  % SZS status Theorem for theBenchmark
% 2.27/0.67  % SZS output start Proof for theBenchmark
% 2.27/0.67  fof(f488,plain,(
% 2.27/0.67    $false),
% 2.27/0.67    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f151,f161,f167,f208,f215,f225,f244,f260,f309,f325,f379,f416,f455,f487])).
% 2.27/0.67  fof(f487,plain,(
% 2.27/0.67    spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_22 | ~spl4_23 | ~spl4_36 | ~spl4_40),
% 2.27/0.67    inference(avatar_contradiction_clause,[],[f486])).
% 2.27/0.67  fof(f486,plain,(
% 2.27/0.67    $false | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_22 | ~spl4_23 | ~spl4_36 | ~spl4_40)),
% 2.27/0.67    inference(subsumption_resolution,[],[f485,f222])).
% 2.27/0.67  fof(f222,plain,(
% 2.27/0.67    sK1 = k1_relat_1(sK3) | ~spl4_22),
% 2.27/0.67    inference(avatar_component_clause,[],[f220])).
% 2.27/0.67  fof(f220,plain,(
% 2.27/0.67    spl4_22 <=> sK1 = k1_relat_1(sK3)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.27/0.67  fof(f485,plain,(
% 2.27/0.67    sK1 != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_36 | ~spl4_40)),
% 2.27/0.67    inference(forward_demodulation,[],[f484,f376])).
% 2.27/0.67  fof(f376,plain,(
% 2.27/0.67    sK1 = k2_relat_1(sK2) | ~spl4_36),
% 2.27/0.67    inference(avatar_component_clause,[],[f374])).
% 2.27/0.67  fof(f374,plain,(
% 2.27/0.67    spl4_36 <=> sK1 = k2_relat_1(sK2)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.27/0.67  fof(f484,plain,(
% 2.27/0.67    k1_relat_1(sK3) != k2_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_40)),
% 2.27/0.67    inference(trivial_inequality_removal,[],[f483])).
% 2.27/0.67  fof(f483,plain,(
% 2.27/0.67    k6_relat_1(sK0) != k6_relat_1(sK0) | k1_relat_1(sK3) != k2_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_40)),
% 2.27/0.67    inference(forward_demodulation,[],[f482,f241])).
% 2.27/0.67  fof(f241,plain,(
% 2.27/0.67    sK0 = k1_relat_1(sK2) | ~spl4_23),
% 2.27/0.67    inference(avatar_component_clause,[],[f239])).
% 2.27/0.67  fof(f239,plain,(
% 2.27/0.67    spl4_23 <=> sK0 = k1_relat_1(sK2)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.27/0.67  fof(f482,plain,(
% 2.27/0.67    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_40)),
% 2.27/0.67    inference(subsumption_resolution,[],[f481,f166])).
% 2.27/0.67  fof(f166,plain,(
% 2.27/0.67    v1_relat_1(sK2) | ~spl4_15),
% 2.27/0.67    inference(avatar_component_clause,[],[f164])).
% 2.27/0.67  fof(f164,plain,(
% 2.27/0.67    spl4_15 <=> v1_relat_1(sK2)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.27/0.67  fof(f481,plain,(
% 2.27/0.67    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_40)),
% 2.27/0.67    inference(subsumption_resolution,[],[f480,f144])).
% 2.27/0.67  fof(f144,plain,(
% 2.27/0.67    v1_funct_1(sK2) | ~spl4_12),
% 2.27/0.67    inference(avatar_component_clause,[],[f142])).
% 2.27/0.67  fof(f142,plain,(
% 2.27/0.67    spl4_12 <=> v1_funct_1(sK2)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.27/0.67  fof(f480,plain,(
% 2.27/0.67    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_14 | ~spl4_40)),
% 2.27/0.67    inference(subsumption_resolution,[],[f479,f160])).
% 2.27/0.67  fof(f160,plain,(
% 2.27/0.67    v1_relat_1(sK3) | ~spl4_14),
% 2.27/0.67    inference(avatar_component_clause,[],[f158])).
% 2.27/0.67  fof(f158,plain,(
% 2.27/0.67    spl4_14 <=> v1_relat_1(sK3)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.27/0.67  fof(f479,plain,(
% 2.27/0.67    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_40)),
% 2.27/0.67    inference(subsumption_resolution,[],[f478,f129])).
% 2.27/0.67  fof(f129,plain,(
% 2.27/0.67    v1_funct_1(sK3) | ~spl4_9),
% 2.27/0.67    inference(avatar_component_clause,[],[f127])).
% 2.27/0.67  fof(f127,plain,(
% 2.27/0.67    spl4_9 <=> v1_funct_1(sK3)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.27/0.67  fof(f478,plain,(
% 2.27/0.67    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_40)),
% 2.27/0.67    inference(subsumption_resolution,[],[f474,f89])).
% 2.27/0.67  fof(f89,plain,(
% 2.27/0.67    k2_funct_1(sK2) != sK3 | spl4_1),
% 2.27/0.67    inference(avatar_component_clause,[],[f87])).
% 2.27/0.67  fof(f87,plain,(
% 2.27/0.67    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.27/0.67  fof(f474,plain,(
% 2.27/0.67    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_40),
% 2.27/0.67    inference(superposition,[],[f245,f415])).
% 2.27/0.67  fof(f415,plain,(
% 2.27/0.67    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_40),
% 2.27/0.67    inference(avatar_component_clause,[],[f413])).
% 2.27/0.67  fof(f413,plain,(
% 2.27/0.67    spl4_40 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.27/0.67  fof(f245,plain,(
% 2.27/0.67    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.67    inference(subsumption_resolution,[],[f57,f66])).
% 2.27/0.67  fof(f66,plain,(
% 2.27/0.67    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f29])).
% 2.27/0.67  fof(f29,plain,(
% 2.27/0.67    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.67    inference(flattening,[],[f28])).
% 2.27/0.67  fof(f28,plain,(
% 2.27/0.67    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.27/0.67    inference(ennf_transformation,[],[f4])).
% 2.27/0.67  fof(f4,axiom,(
% 2.27/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 2.27/0.67  fof(f57,plain,(
% 2.27/0.67    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f23])).
% 2.27/0.67  fof(f23,plain,(
% 2.27/0.67    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.67    inference(flattening,[],[f22])).
% 2.27/0.67  fof(f22,plain,(
% 2.27/0.67    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.27/0.67    inference(ennf_transformation,[],[f6])).
% 2.27/0.67  fof(f6,axiom,(
% 2.27/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 2.27/0.67  fof(f455,plain,(
% 2.27/0.67    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39),
% 2.27/0.67    inference(avatar_contradiction_clause,[],[f438])).
% 2.27/0.67  fof(f438,plain,(
% 2.27/0.67    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39)),
% 2.27/0.67    inference(unit_resulting_resolution,[],[f144,f129,f134,f119,f411,f268])).
% 2.27/0.67  fof(f268,plain,(
% 2.27/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.27/0.67    inference(duplicate_literal_removal,[],[f267])).
% 2.27/0.67  fof(f267,plain,(
% 2.27/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.27/0.67    inference(superposition,[],[f72,f73])).
% 2.27/0.67  fof(f73,plain,(
% 2.27/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f35])).
% 2.27/0.67  fof(f35,plain,(
% 2.27/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.27/0.67    inference(flattening,[],[f34])).
% 2.27/0.67  fof(f34,plain,(
% 2.27/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.27/0.67    inference(ennf_transformation,[],[f12])).
% 2.27/0.67  fof(f12,axiom,(
% 2.27/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.27/0.67  fof(f72,plain,(
% 2.27/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f33])).
% 2.27/0.67  fof(f33,plain,(
% 2.27/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.27/0.67    inference(flattening,[],[f32])).
% 2.27/0.67  fof(f32,plain,(
% 2.27/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.27/0.67    inference(ennf_transformation,[],[f10])).
% 2.27/0.67  fof(f10,axiom,(
% 2.27/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.27/0.67  fof(f411,plain,(
% 2.27/0.67    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_39),
% 2.27/0.67    inference(avatar_component_clause,[],[f409])).
% 2.27/0.67  fof(f409,plain,(
% 2.27/0.67    spl4_39 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.27/0.67  fof(f119,plain,(
% 2.27/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 2.27/0.67    inference(avatar_component_clause,[],[f117])).
% 2.27/0.67  fof(f117,plain,(
% 2.27/0.67    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.27/0.67  fof(f134,plain,(
% 2.27/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 2.27/0.67    inference(avatar_component_clause,[],[f132])).
% 2.27/0.67  fof(f132,plain,(
% 2.27/0.67    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.27/0.67  fof(f416,plain,(
% 2.27/0.67    ~spl4_39 | spl4_40 | ~spl4_24),
% 2.27/0.67    inference(avatar_split_clause,[],[f397,f257,f413,f409])).
% 2.27/0.67  fof(f257,plain,(
% 2.27/0.67    spl4_24 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.27/0.67  fof(f397,plain,(
% 2.27/0.67    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_24),
% 2.27/0.67    inference(resolution,[],[f232,f259])).
% 2.27/0.67  fof(f259,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_24),
% 2.27/0.67    inference(avatar_component_clause,[],[f257])).
% 2.27/0.67  fof(f232,plain,(
% 2.27/0.67    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.27/0.67    inference(resolution,[],[f67,f152])).
% 2.27/0.67  fof(f152,plain,(
% 2.27/0.67    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.27/0.67    inference(forward_demodulation,[],[f69,f70])).
% 2.27/0.67  fof(f70,plain,(
% 2.27/0.67    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f13])).
% 2.27/0.67  fof(f13,axiom,(
% 2.27/0.67    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.27/0.67  fof(f69,plain,(
% 2.27/0.67    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.27/0.67    inference(cnf_transformation,[],[f17])).
% 2.27/0.67  fof(f17,plain,(
% 2.27/0.67    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.27/0.67    inference(pure_predicate_removal,[],[f11])).
% 2.27/0.67  fof(f11,axiom,(
% 2.27/0.67    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.27/0.67  fof(f67,plain,(
% 2.27/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.67    inference(cnf_transformation,[],[f42])).
% 2.27/0.67  fof(f42,plain,(
% 2.27/0.67    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.67    inference(nnf_transformation,[],[f31])).
% 2.27/0.67  fof(f31,plain,(
% 2.27/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.67    inference(flattening,[],[f30])).
% 2.27/0.67  fof(f30,plain,(
% 2.27/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.27/0.67    inference(ennf_transformation,[],[f8])).
% 2.27/0.67  fof(f8,axiom,(
% 2.27/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.27/0.67  fof(f379,plain,(
% 2.27/0.67    spl4_36 | ~spl4_27),
% 2.27/0.67    inference(avatar_split_clause,[],[f378,f318,f374])).
% 2.27/0.67  fof(f318,plain,(
% 2.27/0.67    spl4_27 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.27/0.67  fof(f378,plain,(
% 2.27/0.67    sK1 = k2_relat_1(sK2) | ~spl4_27),
% 2.27/0.67    inference(forward_demodulation,[],[f361,f74])).
% 2.27/0.67  fof(f74,plain,(
% 2.27/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.27/0.67    inference(cnf_transformation,[],[f3])).
% 2.27/0.67  fof(f3,axiom,(
% 2.27/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.27/0.67  fof(f361,plain,(
% 2.27/0.67    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~spl4_27),
% 2.27/0.67    inference(superposition,[],[f74,f320])).
% 2.27/0.67  fof(f320,plain,(
% 2.27/0.67    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~spl4_27),
% 2.27/0.67    inference(avatar_component_clause,[],[f318])).
% 2.27/0.67  fof(f325,plain,(
% 2.27/0.67    spl4_27 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26),
% 2.27/0.67    inference(avatar_split_clause,[],[f324,f306,f164,f142,f102,f318])).
% 2.27/0.67  fof(f102,plain,(
% 2.27/0.67    spl4_4 <=> v2_funct_1(sK2)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.27/0.67  fof(f306,plain,(
% 2.27/0.67    spl4_26 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.27/0.67  fof(f324,plain,(
% 2.27/0.67    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26)),
% 2.27/0.67    inference(subsumption_resolution,[],[f323,f166])).
% 2.27/0.67  fof(f323,plain,(
% 2.27/0.67    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_26)),
% 2.27/0.67    inference(subsumption_resolution,[],[f322,f144])).
% 2.27/0.67  fof(f322,plain,(
% 2.27/0.67    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_26)),
% 2.27/0.67    inference(subsumption_resolution,[],[f311,f104])).
% 2.27/0.67  fof(f104,plain,(
% 2.27/0.67    v2_funct_1(sK2) | ~spl4_4),
% 2.27/0.67    inference(avatar_component_clause,[],[f102])).
% 2.27/0.67  fof(f311,plain,(
% 2.27/0.67    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_26),
% 2.27/0.67    inference(superposition,[],[f59,f308])).
% 2.27/0.67  fof(f308,plain,(
% 2.27/0.67    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_26),
% 2.27/0.67    inference(avatar_component_clause,[],[f306])).
% 2.27/0.67  fof(f59,plain,(
% 2.27/0.67    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f25])).
% 2.27/0.67  fof(f25,plain,(
% 2.27/0.67    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.67    inference(flattening,[],[f24])).
% 2.27/0.67  fof(f24,plain,(
% 2.27/0.67    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.27/0.67    inference(ennf_transformation,[],[f5])).
% 2.27/0.67  fof(f5,axiom,(
% 2.27/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.27/0.67  fof(f309,plain,(
% 2.27/0.67    spl4_26 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.27/0.67    inference(avatar_split_clause,[],[f304,f142,f137,f132,f112,f102,f92,f306])).
% 2.27/0.67  fof(f92,plain,(
% 2.27/0.67    spl4_2 <=> k1_xboole_0 = sK1),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.27/0.67  fof(f112,plain,(
% 2.27/0.67    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.27/0.67  fof(f137,plain,(
% 2.27/0.67    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.27/0.67  fof(f304,plain,(
% 2.27/0.67    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.27/0.67    inference(subsumption_resolution,[],[f303,f144])).
% 2.27/0.67  fof(f303,plain,(
% 2.27/0.67    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.27/0.67    inference(subsumption_resolution,[],[f302,f139])).
% 2.27/0.67  fof(f139,plain,(
% 2.27/0.67    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 2.27/0.67    inference(avatar_component_clause,[],[f137])).
% 2.27/0.67  fof(f302,plain,(
% 2.27/0.67    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.27/0.67    inference(subsumption_resolution,[],[f301,f134])).
% 2.27/0.67  fof(f301,plain,(
% 2.27/0.67    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.27/0.67    inference(subsumption_resolution,[],[f300,f104])).
% 2.27/0.67  fof(f300,plain,(
% 2.27/0.67    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.27/0.67    inference(subsumption_resolution,[],[f299,f94])).
% 2.27/0.67  fof(f94,plain,(
% 2.27/0.67    k1_xboole_0 != sK1 | spl4_2),
% 2.27/0.67    inference(avatar_component_clause,[],[f92])).
% 2.27/0.67  fof(f299,plain,(
% 2.27/0.67    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.27/0.67    inference(trivial_inequality_removal,[],[f298])).
% 2.27/0.67  fof(f298,plain,(
% 2.27/0.67    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.27/0.67    inference(superposition,[],[f273,f114])).
% 2.27/0.67  fof(f114,plain,(
% 2.27/0.67    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 2.27/0.67    inference(avatar_component_clause,[],[f112])).
% 2.27/0.67  fof(f273,plain,(
% 2.27/0.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.27/0.67    inference(forward_demodulation,[],[f56,f70])).
% 2.27/0.67  fof(f56,plain,(
% 2.27/0.67    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f21])).
% 2.27/0.67  fof(f21,plain,(
% 2.27/0.67    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.27/0.67    inference(flattening,[],[f20])).
% 2.27/0.67  fof(f20,plain,(
% 2.27/0.67    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.27/0.67    inference(ennf_transformation,[],[f14])).
% 2.27/0.67  fof(f14,axiom,(
% 2.27/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.27/0.67  fof(f260,plain,(
% 2.27/0.67    spl4_24 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.27/0.67    inference(avatar_split_clause,[],[f255,f148,f142,f132,f127,f117,f257])).
% 2.27/0.67  fof(f148,plain,(
% 2.27/0.67    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.27/0.67  fof(f255,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.27/0.67    inference(subsumption_resolution,[],[f254,f144])).
% 2.27/0.67  fof(f254,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.27/0.67    inference(subsumption_resolution,[],[f253,f134])).
% 2.27/0.67  fof(f253,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.27/0.67    inference(subsumption_resolution,[],[f252,f129])).
% 2.27/0.67  fof(f252,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.27/0.67    inference(subsumption_resolution,[],[f249,f119])).
% 2.27/0.67  fof(f249,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.27/0.67    inference(superposition,[],[f150,f73])).
% 2.27/0.67  fof(f150,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.27/0.67    inference(avatar_component_clause,[],[f148])).
% 2.27/0.67  fof(f244,plain,(
% 2.27/0.67    spl4_23 | ~spl4_10 | ~spl4_21),
% 2.27/0.67    inference(avatar_split_clause,[],[f243,f212,f132,f239])).
% 2.27/0.67  fof(f212,plain,(
% 2.27/0.67    spl4_21 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.27/0.67  fof(f243,plain,(
% 2.27/0.67    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_21)),
% 2.27/0.67    inference(subsumption_resolution,[],[f235,f134])).
% 2.27/0.67  fof(f235,plain,(
% 2.27/0.67    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_21),
% 2.27/0.67    inference(superposition,[],[f76,f214])).
% 2.27/0.67  fof(f214,plain,(
% 2.27/0.67    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_21),
% 2.27/0.67    inference(avatar_component_clause,[],[f212])).
% 2.27/0.67  fof(f76,plain,(
% 2.27/0.67    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.67    inference(cnf_transformation,[],[f36])).
% 2.27/0.67  fof(f36,plain,(
% 2.27/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.67    inference(ennf_transformation,[],[f7])).
% 2.27/0.67  fof(f7,axiom,(
% 2.27/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.27/0.67  fof(f225,plain,(
% 2.27/0.67    spl4_22 | ~spl4_7 | ~spl4_20),
% 2.27/0.67    inference(avatar_split_clause,[],[f224,f205,f117,f220])).
% 2.27/0.67  fof(f205,plain,(
% 2.27/0.67    spl4_20 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.27/0.67  fof(f224,plain,(
% 2.27/0.67    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_20)),
% 2.27/0.67    inference(subsumption_resolution,[],[f217,f119])).
% 2.27/0.67  fof(f217,plain,(
% 2.27/0.67    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_20),
% 2.27/0.67    inference(superposition,[],[f76,f207])).
% 2.27/0.67  fof(f207,plain,(
% 2.27/0.67    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_20),
% 2.27/0.67    inference(avatar_component_clause,[],[f205])).
% 2.27/0.67  fof(f215,plain,(
% 2.27/0.67    spl4_21 | spl4_2 | ~spl4_10 | ~spl4_11),
% 2.27/0.67    inference(avatar_split_clause,[],[f210,f137,f132,f92,f212])).
% 2.27/0.67  fof(f210,plain,(
% 2.27/0.67    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.27/0.67    inference(subsumption_resolution,[],[f209,f94])).
% 2.27/0.67  fof(f209,plain,(
% 2.27/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 2.27/0.67    inference(subsumption_resolution,[],[f200,f139])).
% 2.27/0.67  fof(f200,plain,(
% 2.27/0.67    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 2.27/0.67    inference(resolution,[],[f60,f134])).
% 2.27/0.67  fof(f60,plain,(
% 2.27/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.27/0.67    inference(cnf_transformation,[],[f41])).
% 2.27/0.67  fof(f41,plain,(
% 2.27/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.67    inference(nnf_transformation,[],[f27])).
% 2.27/0.67  fof(f27,plain,(
% 2.27/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.67    inference(flattening,[],[f26])).
% 2.27/0.67  fof(f26,plain,(
% 2.27/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.67    inference(ennf_transformation,[],[f9])).
% 2.27/0.67  fof(f9,axiom,(
% 2.27/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.27/0.67  fof(f208,plain,(
% 2.27/0.67    spl4_20 | spl4_3 | ~spl4_7 | ~spl4_8),
% 2.27/0.67    inference(avatar_split_clause,[],[f203,f122,f117,f97,f205])).
% 2.27/0.67  fof(f97,plain,(
% 2.27/0.67    spl4_3 <=> k1_xboole_0 = sK0),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.27/0.67  fof(f122,plain,(
% 2.27/0.67    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.27/0.67  fof(f203,plain,(
% 2.27/0.67    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 2.27/0.67    inference(subsumption_resolution,[],[f202,f99])).
% 2.27/0.67  fof(f99,plain,(
% 2.27/0.67    k1_xboole_0 != sK0 | spl4_3),
% 2.27/0.67    inference(avatar_component_clause,[],[f97])).
% 2.27/0.67  fof(f202,plain,(
% 2.27/0.67    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 2.27/0.67    inference(subsumption_resolution,[],[f199,f124])).
% 2.27/0.67  fof(f124,plain,(
% 2.27/0.67    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 2.27/0.67    inference(avatar_component_clause,[],[f122])).
% 2.27/0.67  fof(f199,plain,(
% 2.27/0.67    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 2.27/0.67    inference(resolution,[],[f60,f119])).
% 2.27/0.67  fof(f167,plain,(
% 2.27/0.67    spl4_15 | ~spl4_10),
% 2.27/0.67    inference(avatar_split_clause,[],[f162,f132,f164])).
% 2.27/0.67  fof(f162,plain,(
% 2.27/0.67    v1_relat_1(sK2) | ~spl4_10),
% 2.27/0.67    inference(subsumption_resolution,[],[f154,f78])).
% 2.27/0.67  fof(f78,plain,(
% 2.27/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.27/0.67    inference(cnf_transformation,[],[f2])).
% 2.27/0.67  fof(f2,axiom,(
% 2.27/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.27/0.67  fof(f154,plain,(
% 2.27/0.67    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 2.27/0.67    inference(resolution,[],[f77,f134])).
% 2.27/0.67  fof(f77,plain,(
% 2.27/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.27/0.67    inference(cnf_transformation,[],[f37])).
% 2.27/0.67  fof(f37,plain,(
% 2.27/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.27/0.67    inference(ennf_transformation,[],[f1])).
% 2.27/0.67  fof(f1,axiom,(
% 2.27/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.27/0.67  fof(f161,plain,(
% 2.27/0.67    spl4_14 | ~spl4_7),
% 2.27/0.67    inference(avatar_split_clause,[],[f156,f117,f158])).
% 2.27/0.67  fof(f156,plain,(
% 2.27/0.67    v1_relat_1(sK3) | ~spl4_7),
% 2.27/0.67    inference(subsumption_resolution,[],[f153,f78])).
% 2.27/0.67  fof(f153,plain,(
% 2.27/0.67    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 2.27/0.67    inference(resolution,[],[f77,f119])).
% 2.27/0.67  fof(f151,plain,(
% 2.27/0.67    spl4_13 | ~spl4_5),
% 2.27/0.67    inference(avatar_split_clause,[],[f146,f107,f148])).
% 2.27/0.67  fof(f107,plain,(
% 2.27/0.67    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.27/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.27/0.67  fof(f146,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.27/0.67    inference(backward_demodulation,[],[f109,f70])).
% 2.27/0.67  fof(f109,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.27/0.67    inference(avatar_component_clause,[],[f107])).
% 2.27/0.67  fof(f145,plain,(
% 2.27/0.67    spl4_12),
% 2.27/0.67    inference(avatar_split_clause,[],[f43,f142])).
% 2.27/0.67  fof(f43,plain,(
% 2.27/0.67    v1_funct_1(sK2)),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f40,plain,(
% 2.27/0.67    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.27/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f39,f38])).
% 2.27/0.67  fof(f38,plain,(
% 2.27/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.27/0.67    introduced(choice_axiom,[])).
% 2.27/0.67  fof(f39,plain,(
% 2.27/0.67    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.27/0.67    introduced(choice_axiom,[])).
% 2.27/0.67  fof(f19,plain,(
% 2.27/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.27/0.67    inference(flattening,[],[f18])).
% 2.27/0.67  fof(f18,plain,(
% 2.27/0.67    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.27/0.67    inference(ennf_transformation,[],[f16])).
% 2.27/0.67  fof(f16,negated_conjecture,(
% 2.27/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.27/0.67    inference(negated_conjecture,[],[f15])).
% 2.27/0.67  fof(f15,conjecture,(
% 2.27/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.27/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.27/0.67  fof(f140,plain,(
% 2.27/0.67    spl4_11),
% 2.27/0.67    inference(avatar_split_clause,[],[f44,f137])).
% 2.27/0.67  fof(f44,plain,(
% 2.27/0.67    v1_funct_2(sK2,sK0,sK1)),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f135,plain,(
% 2.27/0.67    spl4_10),
% 2.27/0.67    inference(avatar_split_clause,[],[f45,f132])).
% 2.27/0.67  fof(f45,plain,(
% 2.27/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f130,plain,(
% 2.27/0.67    spl4_9),
% 2.27/0.67    inference(avatar_split_clause,[],[f46,f127])).
% 2.27/0.67  fof(f46,plain,(
% 2.27/0.67    v1_funct_1(sK3)),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f125,plain,(
% 2.27/0.67    spl4_8),
% 2.27/0.67    inference(avatar_split_clause,[],[f47,f122])).
% 2.27/0.67  fof(f47,plain,(
% 2.27/0.67    v1_funct_2(sK3,sK1,sK0)),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f120,plain,(
% 2.27/0.67    spl4_7),
% 2.27/0.67    inference(avatar_split_clause,[],[f48,f117])).
% 2.27/0.67  fof(f48,plain,(
% 2.27/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f115,plain,(
% 2.27/0.67    spl4_6),
% 2.27/0.67    inference(avatar_split_clause,[],[f49,f112])).
% 2.27/0.67  fof(f49,plain,(
% 2.27/0.67    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f110,plain,(
% 2.27/0.67    spl4_5),
% 2.27/0.67    inference(avatar_split_clause,[],[f50,f107])).
% 2.27/0.67  fof(f50,plain,(
% 2.27/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f105,plain,(
% 2.27/0.67    spl4_4),
% 2.27/0.67    inference(avatar_split_clause,[],[f51,f102])).
% 2.27/0.67  fof(f51,plain,(
% 2.27/0.67    v2_funct_1(sK2)),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f100,plain,(
% 2.27/0.67    ~spl4_3),
% 2.27/0.67    inference(avatar_split_clause,[],[f52,f97])).
% 2.27/0.67  fof(f52,plain,(
% 2.27/0.67    k1_xboole_0 != sK0),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f95,plain,(
% 2.27/0.67    ~spl4_2),
% 2.27/0.67    inference(avatar_split_clause,[],[f53,f92])).
% 2.27/0.67  fof(f53,plain,(
% 2.27/0.67    k1_xboole_0 != sK1),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  fof(f90,plain,(
% 2.27/0.67    ~spl4_1),
% 2.27/0.67    inference(avatar_split_clause,[],[f54,f87])).
% 2.27/0.67  fof(f54,plain,(
% 2.27/0.67    k2_funct_1(sK2) != sK3),
% 2.27/0.67    inference(cnf_transformation,[],[f40])).
% 2.27/0.67  % SZS output end Proof for theBenchmark
% 2.27/0.67  % (29204)------------------------------
% 2.27/0.67  % (29204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.67  % (29208)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.27/0.67  % (29204)Termination reason: Refutation
% 2.27/0.67  
% 2.27/0.67  % (29204)Memory used [KB]: 6652
% 2.27/0.67  % (29204)Time elapsed: 0.219 s
% 2.27/0.67  % (29204)------------------------------
% 2.27/0.67  % (29204)------------------------------
% 2.27/0.67  % (29182)Success in time 0.302 s
%------------------------------------------------------------------------------
