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
% DateTime   : Thu Dec  3 13:02:42 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 443 expanded)
%              Number of leaves         :   48 ( 191 expanded)
%              Depth                    :   13
%              Number of atoms          :  898 (2218 expanded)
%              Number of equality atoms :  201 ( 635 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f130,f140,f150,f155,f160,f165,f170,f175,f180,f188,f193,f217,f464,f552,f575,f586,f639,f653,f657,f748,f812,f816,f847,f1027,f1078,f1102,f1212])).

fof(f1212,plain,
    ( ~ spl4_47
    | ~ spl4_13
    | ~ spl4_1
    | ~ spl4_14
    | ~ spl4_2
    | spl4_8
    | ~ spl4_17
    | ~ spl4_68
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f1145,f1075,f840,f214,f157,f127,f190,f122,f185,f592])).

fof(f592,plain,
    ( spl4_47
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f185,plain,
    ( spl4_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f122,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f190,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f127,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f157,plain,
    ( spl4_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f214,plain,
    ( spl4_17
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f840,plain,
    ( spl4_68
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f1075,plain,
    ( spl4_90
  <=> k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1145,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_17
    | ~ spl4_68
    | ~ spl4_90 ),
    inference(trivial_inequality_removal,[],[f1144])).

fof(f1144,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_17
    | ~ spl4_68
    | ~ spl4_90 ),
    inference(forward_demodulation,[],[f1143,f216])).

fof(f216,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f214])).

fof(f1143,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_68
    | ~ spl4_90 ),
    inference(forward_demodulation,[],[f1134,f1077])).

fof(f1077,plain,
    ( k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f1075])).

fof(f1134,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_68 ),
    inference(superposition,[],[f385,f842])).

fof(f842,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f840])).

fof(f385,plain,(
    ! [X5] :
      ( k6_partfun1(k1_relat_1(X5)) != k6_partfun1(k2_relat_1(k2_funct_1(X5)))
      | k2_funct_1(k2_funct_1(X5)) = X5
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ v1_relat_1(k2_funct_1(X5))
      | ~ v2_funct_1(X5) ) ),
    inference(global_subsumption,[],[f84,f78,f372])).

fof(f372,plain,(
    ! [X5] :
      ( k6_partfun1(k1_relat_1(X5)) != k6_partfun1(k2_relat_1(k2_funct_1(X5)))
      | k2_funct_1(k2_funct_1(X5)) = X5
      | k1_relat_1(k2_funct_1(X5)) != k2_relat_1(X5)
      | ~ v2_funct_1(k2_funct_1(X5))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ v1_relat_1(k2_funct_1(X5))
      | ~ v2_funct_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f371])).

fof(f371,plain,(
    ! [X5] :
      ( k6_partfun1(k1_relat_1(X5)) != k6_partfun1(k2_relat_1(k2_funct_1(X5)))
      | k2_funct_1(k2_funct_1(X5)) = X5
      | k1_relat_1(k2_funct_1(X5)) != k2_relat_1(X5)
      | ~ v2_funct_1(k2_funct_1(X5))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ v1_relat_1(k2_funct_1(X5))
      | ~ v2_funct_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f105,f107])).

fof(f107,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f76,f93])).

fof(f93,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f76,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f75,f93])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f78,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f84,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f1102,plain,
    ( spl4_69
    | ~ spl4_90 ),
    inference(avatar_contradiction_clause,[],[f1100])).

fof(f1100,plain,
    ( $false
    | spl4_69
    | ~ spl4_90 ),
    inference(subsumption_resolution,[],[f846,f1098])).

fof(f1098,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_90 ),
    inference(forward_demodulation,[],[f1083,f110])).

fof(f110,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f100,f93])).

fof(f100,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1083,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | ~ spl4_90 ),
    inference(superposition,[],[f110,f1077])).

fof(f846,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_69 ),
    inference(avatar_component_clause,[],[f844])).

fof(f844,plain,
    ( spl4_69
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f1078,plain,
    ( ~ spl4_14
    | ~ spl4_2
    | ~ spl4_47
    | spl4_90
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1028,f1024,f1075,f592,f127,f190])).

fof(f1024,plain,
    ( spl4_87
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f1028,plain,
    ( k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_87 ),
    inference(superposition,[],[f1026,f107])).

fof(f1026,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f1024])).

fof(f1027,plain,
    ( ~ spl4_2
    | ~ spl4_7
    | ~ spl4_10
    | spl4_87
    | ~ spl4_47
    | spl4_4
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f570,f549,f137,f592,f1024,f167,f152,f127])).

fof(f152,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f167,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f137,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f549,plain,
    ( spl4_43
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f570,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_43 ),
    inference(trivial_inequality_removal,[],[f558])).

fof(f558,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_43 ),
    inference(superposition,[],[f70,f551])).

fof(f551,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f549])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f847,plain,
    ( ~ spl4_14
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_1
    | ~ spl4_47
    | spl4_68
    | ~ spl4_69
    | ~ spl4_17
    | ~ spl4_44
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f819,f636,f572,f214,f844,f840,f592,f122,f185,f127,f190])).

fof(f572,plain,
    ( spl4_44
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f636,plain,
    ( spl4_53
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f819,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_17
    | ~ spl4_44
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f818,f216])).

fof(f818,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_44
    | ~ spl4_53 ),
    inference(trivial_inequality_removal,[],[f817])).

fof(f817,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_44
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f755,f574])).

fof(f574,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f572])).

fof(f755,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_53 ),
    inference(superposition,[],[f105,f638])).

fof(f638,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f636])).

fof(f816,plain,(
    spl4_66 ),
    inference(avatar_contradiction_clause,[],[f813])).

fof(f813,plain,
    ( $false
    | spl4_66 ),
    inference(unit_resulting_resolution,[],[f270,f811])).

fof(f811,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_66 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl4_66
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f270,plain,(
    ! [X3] : v2_funct_1(k6_partfun1(X3)) ),
    inference(global_subsumption,[],[f113,f114,f269])).

fof(f269,plain,(
    ! [X3] :
      ( v2_funct_1(k6_partfun1(X3))
      | ~ v1_funct_1(k6_partfun1(X3))
      | ~ v1_relat_1(k6_partfun1(X3)) ) ),
    inference(trivial_inequality_removal,[],[f268])).

fof(f268,plain,(
    ! [X3] :
      ( k6_partfun1(X3) != k6_partfun1(X3)
      | v2_funct_1(k6_partfun1(X3))
      | ~ v1_funct_1(k6_partfun1(X3))
      | ~ v1_relat_1(k6_partfun1(X3)) ) ),
    inference(forward_demodulation,[],[f266,f111])).

fof(f111,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f99,f93])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f266,plain,(
    ! [X3] :
      ( k6_partfun1(X3) != k6_partfun1(k1_relat_1(k6_partfun1(X3)))
      | v2_funct_1(k6_partfun1(X3))
      | ~ v1_funct_1(k6_partfun1(X3))
      | ~ v1_relat_1(k6_partfun1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X3] :
      ( k6_partfun1(X3) != k6_partfun1(k1_relat_1(k6_partfun1(X3)))
      | v2_funct_1(k6_partfun1(X3))
      | ~ v1_funct_1(k6_partfun1(X3))
      | ~ v1_relat_1(k6_partfun1(X3))
      | ~ v1_funct_1(k6_partfun1(X3))
      | ~ v1_relat_1(k6_partfun1(X3)) ) ),
    inference(superposition,[],[f108,f195])).

fof(f195,plain,(
    ! [X0] : k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(global_subsumption,[],[f114,f194])).

fof(f194,plain,(
    ! [X0] :
      ( k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f109,f110])).

fof(f109,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f98,f93])).

fof(f98,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f108,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f89,f93])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f114,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f103,f93])).

fof(f103,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f113,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f104,f93])).

fof(f104,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f812,plain,
    ( spl4_47
    | spl4_4
    | ~ spl4_10
    | ~ spl4_7
    | ~ spl4_2
    | ~ spl4_66
    | ~ spl4_46
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f660,f650,f584,f809,f127,f152,f167,f137,f592])).

fof(f584,plain,
    ( spl4_46
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f650,plain,
    ( spl4_55
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f660,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_46
    | ~ spl4_55 ),
    inference(superposition,[],[f585,f652])).

fof(f652,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f650])).

fof(f585,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | k1_xboole_0 = X0
        | v2_funct_1(X1) )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f584])).

fof(f748,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | spl4_52 ),
    inference(avatar_contradiction_clause,[],[f722])).

fof(f722,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | spl4_52 ),
    inference(unit_resulting_resolution,[],[f124,f129,f164,f169,f634,f434])).

fof(f434,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,(
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
    inference(superposition,[],[f95,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f634,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl4_52
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f169,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f164,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f129,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f124,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f657,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | spl4_54 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | spl4_54 ),
    inference(unit_resulting_resolution,[],[f124,f129,f164,f169,f648,f95])).

fof(f648,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_54 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl4_54
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f653,plain,
    ( ~ spl4_54
    | spl4_55
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f625,f177,f650,f646])).

fof(f177,plain,
    ( spl4_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f625,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_12 ),
    inference(resolution,[],[f299,f179])).

fof(f179,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f299,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f90,f112])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f102,f93])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f639,plain,
    ( ~ spl4_52
    | spl4_53
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f626,f461,f636,f632])).

fof(f461,plain,
    ( spl4_36
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f626,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_36 ),
    inference(resolution,[],[f299,f463])).

fof(f463,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f461])).

fof(f586,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | ~ spl4_9
    | spl4_46
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f556,f172,f584,f162,f147,f122])).

fof(f147,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f172,plain,
    ( spl4_11
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f556,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f553])).

fof(f553,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_11 ),
    inference(superposition,[],[f87,f174])).

fof(f174,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f575,plain,
    ( ~ spl4_10
    | spl4_44
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f557,f549,f572,f167])).

fof(f557,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_43 ),
    inference(superposition,[],[f551,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f552,plain,
    ( ~ spl4_2
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_9
    | spl4_43
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f515,f177,f549,f162,f147,f122,f167,f152,f127])).

fof(f515,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_12 ),
    inference(resolution,[],[f92,f179])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f464,plain,
    ( ~ spl4_1
    | ~ spl4_9
    | ~ spl4_2
    | ~ spl4_10
    | spl4_36
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f414,f177,f461,f167,f127,f162,f122])).

fof(f414,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f179,f96])).

fof(f217,plain,
    ( ~ spl4_9
    | spl4_17
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f211,f172,f214,f162])).

fof(f211,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f97,f174])).

fof(f193,plain,
    ( spl4_14
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f182,f167,f190])).

fof(f182,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(resolution,[],[f101,f169])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f188,plain,
    ( spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f181,f162,f185])).

fof(f181,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(resolution,[],[f101,f164])).

fof(f180,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f65,f177])).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f55,f54])).

fof(f54,plain,
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

fof(f55,plain,
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f175,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f64,f172])).

fof(f64,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f170,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f63,f167])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f165,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f60,f162])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f160,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f69,f157])).

fof(f69,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f155,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f62,f152])).

fof(f62,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f150,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f59,f147])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f140,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f67,f137])).

fof(f67,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f130,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f61,f127])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f125,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f58,f122])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (20516)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.47  % (20523)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (20538)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (20530)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (20536)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (20528)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (20521)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (20520)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (20517)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (20514)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (20539)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (20513)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (20518)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (20515)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (20524)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (20522)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (20519)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (20542)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (20541)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (20534)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (20526)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (20540)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (20537)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (20529)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (20529)Refutation not found, incomplete strategy% (20529)------------------------------
% 0.21/0.55  % (20529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20529)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20529)Memory used [KB]: 10746
% 0.21/0.55  % (20529)Time elapsed: 0.150 s
% 0.21/0.55  % (20529)------------------------------
% 0.21/0.55  % (20529)------------------------------
% 1.52/0.55  % (20531)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.52/0.55  % (20533)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.56  % (20525)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.52/0.56  % (20532)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.52/0.56  % (20527)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.57  % (20535)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.13/0.65  % (20536)Refutation found. Thanks to Tanya!
% 2.13/0.65  % SZS status Theorem for theBenchmark
% 2.13/0.65  % SZS output start Proof for theBenchmark
% 2.13/0.65  fof(f1213,plain,(
% 2.13/0.65    $false),
% 2.13/0.65    inference(avatar_sat_refutation,[],[f125,f130,f140,f150,f155,f160,f165,f170,f175,f180,f188,f193,f217,f464,f552,f575,f586,f639,f653,f657,f748,f812,f816,f847,f1027,f1078,f1102,f1212])).
% 2.13/0.65  fof(f1212,plain,(
% 2.13/0.65    ~spl4_47 | ~spl4_13 | ~spl4_1 | ~spl4_14 | ~spl4_2 | spl4_8 | ~spl4_17 | ~spl4_68 | ~spl4_90),
% 2.13/0.65    inference(avatar_split_clause,[],[f1145,f1075,f840,f214,f157,f127,f190,f122,f185,f592])).
% 2.13/0.65  fof(f592,plain,(
% 2.13/0.65    spl4_47 <=> v2_funct_1(sK3)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 2.13/0.65  fof(f185,plain,(
% 2.13/0.65    spl4_13 <=> v1_relat_1(sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.13/0.65  fof(f122,plain,(
% 2.13/0.65    spl4_1 <=> v1_funct_1(sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.13/0.65  fof(f190,plain,(
% 2.13/0.65    spl4_14 <=> v1_relat_1(sK3)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.13/0.65  fof(f127,plain,(
% 2.13/0.65    spl4_2 <=> v1_funct_1(sK3)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.13/0.65  fof(f157,plain,(
% 2.13/0.65    spl4_8 <=> k2_funct_1(sK2) = sK3),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.13/0.65  fof(f214,plain,(
% 2.13/0.65    spl4_17 <=> sK1 = k2_relat_1(sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.13/0.65  fof(f840,plain,(
% 2.13/0.65    spl4_68 <=> sK2 = k2_funct_1(sK3)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 2.13/0.65  fof(f1075,plain,(
% 2.13/0.65    spl4_90 <=> k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 2.13/0.65  fof(f1145,plain,(
% 2.13/0.65    k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl4_17 | ~spl4_68 | ~spl4_90)),
% 2.13/0.65    inference(trivial_inequality_removal,[],[f1144])).
% 2.13/0.65  fof(f1144,plain,(
% 2.13/0.65    k6_partfun1(sK1) != k6_partfun1(sK1) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl4_17 | ~spl4_68 | ~spl4_90)),
% 2.13/0.65    inference(forward_demodulation,[],[f1143,f216])).
% 2.13/0.65  fof(f216,plain,(
% 2.13/0.65    sK1 = k2_relat_1(sK2) | ~spl4_17),
% 2.13/0.65    inference(avatar_component_clause,[],[f214])).
% 2.13/0.65  fof(f1143,plain,(
% 2.13/0.65    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl4_68 | ~spl4_90)),
% 2.13/0.65    inference(forward_demodulation,[],[f1134,f1077])).
% 2.13/0.65  fof(f1077,plain,(
% 2.13/0.65    k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3)) | ~spl4_90),
% 2.13/0.65    inference(avatar_component_clause,[],[f1075])).
% 2.13/0.65  fof(f1134,plain,(
% 2.13/0.65    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | ~spl4_68),
% 2.13/0.65    inference(superposition,[],[f385,f842])).
% 2.13/0.65  fof(f842,plain,(
% 2.13/0.65    sK2 = k2_funct_1(sK3) | ~spl4_68),
% 2.13/0.65    inference(avatar_component_clause,[],[f840])).
% 2.34/0.67  fof(f385,plain,(
% 2.34/0.67    ( ! [X5] : (k6_partfun1(k1_relat_1(X5)) != k6_partfun1(k2_relat_1(k2_funct_1(X5))) | k2_funct_1(k2_funct_1(X5)) = X5 | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~v1_funct_1(k2_funct_1(X5)) | ~v1_relat_1(k2_funct_1(X5)) | ~v2_funct_1(X5)) )),
% 2.34/0.67    inference(global_subsumption,[],[f84,f78,f372])).
% 2.34/0.67  fof(f372,plain,(
% 2.34/0.67    ( ! [X5] : (k6_partfun1(k1_relat_1(X5)) != k6_partfun1(k2_relat_1(k2_funct_1(X5))) | k2_funct_1(k2_funct_1(X5)) = X5 | k1_relat_1(k2_funct_1(X5)) != k2_relat_1(X5) | ~v2_funct_1(k2_funct_1(X5)) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~v1_funct_1(k2_funct_1(X5)) | ~v1_relat_1(k2_funct_1(X5)) | ~v2_funct_1(X5)) )),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f371])).
% 2.34/0.67  fof(f371,plain,(
% 2.34/0.67    ( ! [X5] : (k6_partfun1(k1_relat_1(X5)) != k6_partfun1(k2_relat_1(k2_funct_1(X5))) | k2_funct_1(k2_funct_1(X5)) = X5 | k1_relat_1(k2_funct_1(X5)) != k2_relat_1(X5) | ~v2_funct_1(k2_funct_1(X5)) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~v1_funct_1(k2_funct_1(X5)) | ~v1_relat_1(k2_funct_1(X5)) | ~v2_funct_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 2.34/0.67    inference(superposition,[],[f105,f107])).
% 2.34/0.67  fof(f107,plain,(
% 2.34/0.67    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f76,f93])).
% 2.34/0.67  fof(f93,plain,(
% 2.34/0.67    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f16])).
% 2.34/0.67  fof(f16,axiom,(
% 2.34/0.67    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.34/0.67  fof(f76,plain,(
% 2.34/0.67    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f32])).
% 2.34/0.67  fof(f32,plain,(
% 2.34/0.67    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/0.67    inference(flattening,[],[f31])).
% 2.34/0.67  fof(f31,plain,(
% 2.34/0.67    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f8])).
% 2.34/0.67  fof(f8,axiom,(
% 2.34/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.34/0.67  fof(f105,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f75,f93])).
% 2.34/0.67  fof(f75,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f30])).
% 2.34/0.67  fof(f30,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/0.67    inference(flattening,[],[f29])).
% 2.34/0.67  fof(f29,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f9])).
% 2.34/0.67  fof(f9,axiom,(
% 2.34/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 2.34/0.67  fof(f78,plain,(
% 2.34/0.67    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f34])).
% 2.34/0.67  fof(f34,plain,(
% 2.34/0.67    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/0.67    inference(flattening,[],[f33])).
% 2.34/0.67  fof(f33,plain,(
% 2.34/0.67    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f7])).
% 2.34/0.67  fof(f7,axiom,(
% 2.34/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.34/0.67  fof(f84,plain,(
% 2.34/0.67    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f38])).
% 2.34/0.67  fof(f38,plain,(
% 2.34/0.67    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/0.67    inference(flattening,[],[f37])).
% 2.34/0.67  fof(f37,plain,(
% 2.34/0.67    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f5])).
% 2.34/0.67  fof(f5,axiom,(
% 2.34/0.67    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 2.34/0.67  fof(f1102,plain,(
% 2.34/0.67    spl4_69 | ~spl4_90),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f1100])).
% 2.34/0.67  fof(f1100,plain,(
% 2.34/0.67    $false | (spl4_69 | ~spl4_90)),
% 2.34/0.67    inference(subsumption_resolution,[],[f846,f1098])).
% 2.34/0.67  fof(f1098,plain,(
% 2.34/0.67    sK1 = k1_relat_1(sK3) | ~spl4_90),
% 2.34/0.67    inference(forward_demodulation,[],[f1083,f110])).
% 2.34/0.67  fof(f110,plain,(
% 2.34/0.67    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.34/0.67    inference(definition_unfolding,[],[f100,f93])).
% 2.34/0.67  fof(f100,plain,(
% 2.34/0.67    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.34/0.67    inference(cnf_transformation,[],[f1])).
% 2.34/0.67  fof(f1,axiom,(
% 2.34/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.34/0.67  fof(f1083,plain,(
% 2.34/0.67    k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) | ~spl4_90),
% 2.34/0.67    inference(superposition,[],[f110,f1077])).
% 2.34/0.67  fof(f846,plain,(
% 2.34/0.67    sK1 != k1_relat_1(sK3) | spl4_69),
% 2.34/0.67    inference(avatar_component_clause,[],[f844])).
% 2.34/0.67  fof(f844,plain,(
% 2.34/0.67    spl4_69 <=> sK1 = k1_relat_1(sK3)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 2.34/0.67  fof(f1078,plain,(
% 2.34/0.67    ~spl4_14 | ~spl4_2 | ~spl4_47 | spl4_90 | ~spl4_87),
% 2.34/0.67    inference(avatar_split_clause,[],[f1028,f1024,f1075,f592,f127,f190])).
% 2.34/0.67  fof(f1024,plain,(
% 2.34/0.67    spl4_87 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 2.34/0.67  fof(f1028,plain,(
% 2.34/0.67    k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_87),
% 2.34/0.67    inference(superposition,[],[f1026,f107])).
% 2.34/0.67  fof(f1026,plain,(
% 2.34/0.67    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_87),
% 2.34/0.67    inference(avatar_component_clause,[],[f1024])).
% 2.34/0.67  fof(f1027,plain,(
% 2.34/0.67    ~spl4_2 | ~spl4_7 | ~spl4_10 | spl4_87 | ~spl4_47 | spl4_4 | ~spl4_43),
% 2.34/0.67    inference(avatar_split_clause,[],[f570,f549,f137,f592,f1024,f167,f152,f127])).
% 2.34/0.67  fof(f152,plain,(
% 2.34/0.67    spl4_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.34/0.67  fof(f167,plain,(
% 2.34/0.67    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.34/0.67  fof(f137,plain,(
% 2.34/0.67    spl4_4 <=> k1_xboole_0 = sK0),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.34/0.67  fof(f549,plain,(
% 2.34/0.67    spl4_43 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 2.34/0.67  fof(f570,plain,(
% 2.34/0.67    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_43),
% 2.34/0.67    inference(trivial_inequality_removal,[],[f558])).
% 2.34/0.67  fof(f558,plain,(
% 2.34/0.67    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_43),
% 2.34/0.67    inference(superposition,[],[f70,f551])).
% 2.34/0.67  fof(f551,plain,(
% 2.34/0.67    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_43),
% 2.34/0.67    inference(avatar_component_clause,[],[f549])).
% 2.34/0.67  fof(f70,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f26])).
% 2.34/0.67  fof(f26,plain,(
% 2.34/0.67    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.34/0.67    inference(flattening,[],[f25])).
% 2.34/0.67  fof(f25,plain,(
% 2.34/0.67    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.34/0.67    inference(ennf_transformation,[],[f20])).
% 2.34/0.67  fof(f20,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.34/0.67  fof(f847,plain,(
% 2.34/0.67    ~spl4_14 | ~spl4_2 | ~spl4_13 | ~spl4_1 | ~spl4_47 | spl4_68 | ~spl4_69 | ~spl4_17 | ~spl4_44 | ~spl4_53),
% 2.34/0.67    inference(avatar_split_clause,[],[f819,f636,f572,f214,f844,f840,f592,f122,f185,f127,f190])).
% 2.34/0.67  fof(f572,plain,(
% 2.34/0.67    spl4_44 <=> sK0 = k2_relat_1(sK3)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.34/0.67  fof(f636,plain,(
% 2.34/0.67    spl4_53 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.34/0.67  fof(f819,plain,(
% 2.34/0.67    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_17 | ~spl4_44 | ~spl4_53)),
% 2.34/0.67    inference(forward_demodulation,[],[f818,f216])).
% 2.34/0.67  fof(f818,plain,(
% 2.34/0.67    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_44 | ~spl4_53)),
% 2.34/0.67    inference(trivial_inequality_removal,[],[f817])).
% 2.34/0.67  fof(f817,plain,(
% 2.34/0.67    k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_44 | ~spl4_53)),
% 2.34/0.67    inference(forward_demodulation,[],[f755,f574])).
% 2.34/0.67  fof(f574,plain,(
% 2.34/0.67    sK0 = k2_relat_1(sK3) | ~spl4_44),
% 2.34/0.67    inference(avatar_component_clause,[],[f572])).
% 2.34/0.67  fof(f755,plain,(
% 2.34/0.67    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_53),
% 2.34/0.67    inference(superposition,[],[f105,f638])).
% 2.34/0.67  fof(f638,plain,(
% 2.34/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_53),
% 2.34/0.67    inference(avatar_component_clause,[],[f636])).
% 2.34/0.67  fof(f816,plain,(
% 2.34/0.67    spl4_66),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f813])).
% 2.34/0.67  fof(f813,plain,(
% 2.34/0.67    $false | spl4_66),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f270,f811])).
% 2.34/0.67  fof(f811,plain,(
% 2.34/0.67    ~v2_funct_1(k6_partfun1(sK0)) | spl4_66),
% 2.34/0.67    inference(avatar_component_clause,[],[f809])).
% 2.34/0.67  fof(f809,plain,(
% 2.34/0.67    spl4_66 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 2.34/0.67  fof(f270,plain,(
% 2.34/0.67    ( ! [X3] : (v2_funct_1(k6_partfun1(X3))) )),
% 2.34/0.67    inference(global_subsumption,[],[f113,f114,f269])).
% 2.34/0.67  fof(f269,plain,(
% 2.34/0.67    ( ! [X3] : (v2_funct_1(k6_partfun1(X3)) | ~v1_funct_1(k6_partfun1(X3)) | ~v1_relat_1(k6_partfun1(X3))) )),
% 2.34/0.67    inference(trivial_inequality_removal,[],[f268])).
% 2.34/0.67  fof(f268,plain,(
% 2.34/0.67    ( ! [X3] : (k6_partfun1(X3) != k6_partfun1(X3) | v2_funct_1(k6_partfun1(X3)) | ~v1_funct_1(k6_partfun1(X3)) | ~v1_relat_1(k6_partfun1(X3))) )),
% 2.34/0.67    inference(forward_demodulation,[],[f266,f111])).
% 2.34/0.67  fof(f111,plain,(
% 2.34/0.67    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.34/0.67    inference(definition_unfolding,[],[f99,f93])).
% 2.34/0.67  fof(f99,plain,(
% 2.34/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.34/0.67    inference(cnf_transformation,[],[f1])).
% 2.34/0.67  fof(f266,plain,(
% 2.34/0.67    ( ! [X3] : (k6_partfun1(X3) != k6_partfun1(k1_relat_1(k6_partfun1(X3))) | v2_funct_1(k6_partfun1(X3)) | ~v1_funct_1(k6_partfun1(X3)) | ~v1_relat_1(k6_partfun1(X3))) )),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f260])).
% 2.34/0.67  fof(f260,plain,(
% 2.34/0.67    ( ! [X3] : (k6_partfun1(X3) != k6_partfun1(k1_relat_1(k6_partfun1(X3))) | v2_funct_1(k6_partfun1(X3)) | ~v1_funct_1(k6_partfun1(X3)) | ~v1_relat_1(k6_partfun1(X3)) | ~v1_funct_1(k6_partfun1(X3)) | ~v1_relat_1(k6_partfun1(X3))) )),
% 2.34/0.67    inference(superposition,[],[f108,f195])).
% 2.34/0.67  fof(f195,plain,(
% 2.34/0.67    ( ! [X0] : (k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0))) )),
% 2.34/0.67    inference(global_subsumption,[],[f114,f194])).
% 2.34/0.67  fof(f194,plain,(
% 2.34/0.67    ( ! [X0] : (k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 2.34/0.67    inference(superposition,[],[f109,f110])).
% 2.34/0.67  fof(f109,plain,(
% 2.34/0.67    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f98,f93])).
% 2.34/0.67  fof(f98,plain,(
% 2.34/0.67    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f52])).
% 2.34/0.67  fof(f52,plain,(
% 2.34/0.67    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.34/0.67    inference(ennf_transformation,[],[f2])).
% 2.34/0.67  fof(f2,axiom,(
% 2.34/0.67    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.34/0.67  fof(f108,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f89,f93])).
% 2.34/0.67  fof(f89,plain,(
% 2.34/0.67    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f42])).
% 2.34/0.67  fof(f42,plain,(
% 2.34/0.67    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/0.67    inference(flattening,[],[f41])).
% 2.34/0.67  fof(f41,plain,(
% 2.34/0.67    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f6])).
% 2.34/0.67  fof(f6,axiom,(
% 2.34/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 2.34/0.67  fof(f114,plain,(
% 2.34/0.67    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.34/0.67    inference(definition_unfolding,[],[f103,f93])).
% 2.34/0.67  fof(f103,plain,(
% 2.34/0.67    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f4])).
% 2.34/0.67  fof(f4,axiom,(
% 2.34/0.67    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.34/0.67  fof(f113,plain,(
% 2.34/0.67    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.34/0.67    inference(definition_unfolding,[],[f104,f93])).
% 2.34/0.67  fof(f104,plain,(
% 2.34/0.67    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f4])).
% 2.34/0.67  fof(f812,plain,(
% 2.34/0.67    spl4_47 | spl4_4 | ~spl4_10 | ~spl4_7 | ~spl4_2 | ~spl4_66 | ~spl4_46 | ~spl4_55),
% 2.34/0.67    inference(avatar_split_clause,[],[f660,f650,f584,f809,f127,f152,f167,f137,f592])).
% 2.34/0.67  fof(f584,plain,(
% 2.34/0.67    spl4_46 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.34/0.67  fof(f650,plain,(
% 2.34/0.67    spl4_55 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 2.34/0.67  fof(f660,plain,(
% 2.34/0.67    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_46 | ~spl4_55)),
% 2.34/0.67    inference(superposition,[],[f585,f652])).
% 2.34/0.67  fof(f652,plain,(
% 2.34/0.67    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_55),
% 2.34/0.67    inference(avatar_component_clause,[],[f650])).
% 2.34/0.67  fof(f585,plain,(
% 2.34/0.67    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | k1_xboole_0 = X0 | v2_funct_1(X1)) ) | ~spl4_46),
% 2.34/0.67    inference(avatar_component_clause,[],[f584])).
% 2.34/0.67  fof(f748,plain,(
% 2.34/0.67    ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | spl4_52),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f722])).
% 2.34/0.67  fof(f722,plain,(
% 2.34/0.67    $false | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | spl4_52)),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f124,f129,f164,f169,f634,f434])).
% 2.34/0.67  fof(f434,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f433])).
% 2.34/0.67  fof(f433,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.34/0.67    inference(superposition,[],[f95,f96])).
% 2.34/0.67  fof(f96,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f50])).
% 2.34/0.67  fof(f50,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.34/0.67    inference(flattening,[],[f49])).
% 2.34/0.67  fof(f49,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.34/0.67    inference(ennf_transformation,[],[f15])).
% 2.34/0.67  fof(f15,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.34/0.67  fof(f95,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f48])).
% 2.34/0.67  fof(f48,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.34/0.67    inference(flattening,[],[f47])).
% 2.34/0.67  fof(f47,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.34/0.67    inference(ennf_transformation,[],[f14])).
% 2.34/0.67  fof(f14,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.34/0.67  fof(f634,plain,(
% 2.34/0.67    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_52),
% 2.34/0.67    inference(avatar_component_clause,[],[f632])).
% 2.34/0.67  fof(f632,plain,(
% 2.34/0.67    spl4_52 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.34/0.67  fof(f169,plain,(
% 2.34/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 2.34/0.67    inference(avatar_component_clause,[],[f167])).
% 2.34/0.67  fof(f164,plain,(
% 2.34/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_9),
% 2.34/0.67    inference(avatar_component_clause,[],[f162])).
% 2.34/0.67  fof(f162,plain,(
% 2.34/0.67    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.34/0.67  fof(f129,plain,(
% 2.34/0.67    v1_funct_1(sK3) | ~spl4_2),
% 2.34/0.67    inference(avatar_component_clause,[],[f127])).
% 2.34/0.67  fof(f124,plain,(
% 2.34/0.67    v1_funct_1(sK2) | ~spl4_1),
% 2.34/0.67    inference(avatar_component_clause,[],[f122])).
% 2.34/0.67  fof(f657,plain,(
% 2.34/0.67    ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | spl4_54),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f654])).
% 2.34/0.67  fof(f654,plain,(
% 2.34/0.67    $false | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | spl4_54)),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f124,f129,f164,f169,f648,f95])).
% 2.34/0.67  fof(f648,plain,(
% 2.34/0.67    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_54),
% 2.34/0.67    inference(avatar_component_clause,[],[f646])).
% 2.34/0.67  fof(f646,plain,(
% 2.34/0.67    spl4_54 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 2.34/0.67  fof(f653,plain,(
% 2.34/0.67    ~spl4_54 | spl4_55 | ~spl4_12),
% 2.34/0.67    inference(avatar_split_clause,[],[f625,f177,f650,f646])).
% 2.34/0.67  fof(f177,plain,(
% 2.34/0.67    spl4_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.34/0.67  fof(f625,plain,(
% 2.34/0.67    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_12),
% 2.34/0.67    inference(resolution,[],[f299,f179])).
% 2.34/0.67  fof(f179,plain,(
% 2.34/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_12),
% 2.34/0.67    inference(avatar_component_clause,[],[f177])).
% 2.34/0.67  fof(f299,plain,(
% 2.34/0.67    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.34/0.67    inference(resolution,[],[f90,f112])).
% 2.34/0.67  fof(f112,plain,(
% 2.34/0.67    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.34/0.67    inference(definition_unfolding,[],[f102,f93])).
% 2.34/0.67  fof(f102,plain,(
% 2.34/0.67    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f13])).
% 2.34/0.67  fof(f13,axiom,(
% 2.34/0.67    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.34/0.67  fof(f90,plain,(
% 2.34/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f57])).
% 2.34/0.67  fof(f57,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.67    inference(nnf_transformation,[],[f44])).
% 2.34/0.67  fof(f44,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.67    inference(flattening,[],[f43])).
% 2.34/0.67  fof(f43,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.34/0.67    inference(ennf_transformation,[],[f12])).
% 2.34/0.67  fof(f12,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.34/0.67  fof(f639,plain,(
% 2.34/0.67    ~spl4_52 | spl4_53 | ~spl4_36),
% 2.34/0.67    inference(avatar_split_clause,[],[f626,f461,f636,f632])).
% 2.34/0.67  fof(f461,plain,(
% 2.34/0.67    spl4_36 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.34/0.67  fof(f626,plain,(
% 2.34/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_36),
% 2.34/0.67    inference(resolution,[],[f299,f463])).
% 2.34/0.67  fof(f463,plain,(
% 2.34/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl4_36),
% 2.34/0.67    inference(avatar_component_clause,[],[f461])).
% 2.34/0.67  fof(f586,plain,(
% 2.34/0.67    ~spl4_1 | ~spl4_6 | ~spl4_9 | spl4_46 | ~spl4_11),
% 2.34/0.67    inference(avatar_split_clause,[],[f556,f172,f584,f162,f147,f122])).
% 2.34/0.67  fof(f147,plain,(
% 2.34/0.67    spl4_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.34/0.67  fof(f172,plain,(
% 2.34/0.67    spl4_11 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.34/0.67  fof(f556,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_11),
% 2.34/0.67    inference(trivial_inequality_removal,[],[f553])).
% 2.34/0.67  fof(f553,plain,(
% 2.34/0.67    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_11),
% 2.34/0.67    inference(superposition,[],[f87,f174])).
% 2.34/0.67  fof(f174,plain,(
% 2.34/0.67    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_11),
% 2.34/0.67    inference(avatar_component_clause,[],[f172])).
% 2.34/0.67  fof(f87,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f40])).
% 2.34/0.67  fof(f40,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.34/0.67    inference(flattening,[],[f39])).
% 2.34/0.67  fof(f39,plain,(
% 2.34/0.67    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.34/0.67    inference(ennf_transformation,[],[f18])).
% 2.34/0.67  fof(f18,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.34/0.67  fof(f575,plain,(
% 2.34/0.67    ~spl4_10 | spl4_44 | ~spl4_43),
% 2.34/0.67    inference(avatar_split_clause,[],[f557,f549,f572,f167])).
% 2.34/0.67  fof(f557,plain,(
% 2.34/0.67    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_43),
% 2.34/0.67    inference(superposition,[],[f551,f97])).
% 2.34/0.67  fof(f97,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f51])).
% 2.34/0.67  fof(f51,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.67    inference(ennf_transformation,[],[f11])).
% 2.34/0.67  fof(f11,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.34/0.67  fof(f552,plain,(
% 2.34/0.67    ~spl4_2 | ~spl4_7 | ~spl4_10 | ~spl4_1 | ~spl4_6 | ~spl4_9 | spl4_43 | ~spl4_12),
% 2.34/0.67    inference(avatar_split_clause,[],[f515,f177,f549,f162,f147,f122,f167,f152,f127])).
% 2.34/0.67  fof(f515,plain,(
% 2.34/0.67    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_12),
% 2.34/0.67    inference(resolution,[],[f92,f179])).
% 2.34/0.67  fof(f92,plain,(
% 2.34/0.67    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f46])).
% 2.34/0.67  fof(f46,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.34/0.67    inference(flattening,[],[f45])).
% 2.34/0.67  fof(f45,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.34/0.67    inference(ennf_transformation,[],[f17])).
% 2.34/0.67  fof(f17,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.34/0.67  fof(f464,plain,(
% 2.34/0.67    ~spl4_1 | ~spl4_9 | ~spl4_2 | ~spl4_10 | spl4_36 | ~spl4_12),
% 2.34/0.67    inference(avatar_split_clause,[],[f414,f177,f461,f167,f127,f162,f122])).
% 2.34/0.67  fof(f414,plain,(
% 2.34/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_12),
% 2.34/0.67    inference(superposition,[],[f179,f96])).
% 2.34/0.67  fof(f217,plain,(
% 2.34/0.67    ~spl4_9 | spl4_17 | ~spl4_11),
% 2.34/0.67    inference(avatar_split_clause,[],[f211,f172,f214,f162])).
% 2.34/0.67  fof(f211,plain,(
% 2.34/0.67    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 2.34/0.67    inference(superposition,[],[f97,f174])).
% 2.34/0.67  fof(f193,plain,(
% 2.34/0.67    spl4_14 | ~spl4_10),
% 2.34/0.67    inference(avatar_split_clause,[],[f182,f167,f190])).
% 2.34/0.67  fof(f182,plain,(
% 2.34/0.67    v1_relat_1(sK3) | ~spl4_10),
% 2.34/0.67    inference(resolution,[],[f101,f169])).
% 2.34/0.67  fof(f101,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f53])).
% 2.34/0.67  fof(f53,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.67    inference(ennf_transformation,[],[f10])).
% 2.34/0.67  fof(f10,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.34/0.67  fof(f188,plain,(
% 2.34/0.67    spl4_13 | ~spl4_9),
% 2.34/0.67    inference(avatar_split_clause,[],[f181,f162,f185])).
% 2.34/0.67  fof(f181,plain,(
% 2.34/0.67    v1_relat_1(sK2) | ~spl4_9),
% 2.34/0.67    inference(resolution,[],[f101,f164])).
% 2.34/0.67  fof(f180,plain,(
% 2.34/0.67    spl4_12),
% 2.34/0.67    inference(avatar_split_clause,[],[f65,f177])).
% 2.34/0.67  fof(f65,plain,(
% 2.34/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f56,plain,(
% 2.34/0.67    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.34/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f55,f54])).
% 2.34/0.67  fof(f54,plain,(
% 2.34/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.34/0.67    introduced(choice_axiom,[])).
% 2.34/0.67  fof(f55,plain,(
% 2.34/0.67    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.34/0.67    introduced(choice_axiom,[])).
% 2.34/0.67  fof(f24,plain,(
% 2.34/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.34/0.67    inference(flattening,[],[f23])).
% 2.34/0.67  fof(f23,plain,(
% 2.34/0.67    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.34/0.67    inference(ennf_transformation,[],[f22])).
% 2.34/0.67  fof(f22,negated_conjecture,(
% 2.34/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.34/0.67    inference(negated_conjecture,[],[f21])).
% 2.34/0.67  fof(f21,conjecture,(
% 2.34/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.34/0.67  fof(f175,plain,(
% 2.34/0.67    spl4_11),
% 2.34/0.67    inference(avatar_split_clause,[],[f64,f172])).
% 2.34/0.67  fof(f64,plain,(
% 2.34/0.67    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f170,plain,(
% 2.34/0.67    spl4_10),
% 2.34/0.67    inference(avatar_split_clause,[],[f63,f167])).
% 2.34/0.67  fof(f63,plain,(
% 2.34/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f165,plain,(
% 2.34/0.67    spl4_9),
% 2.34/0.67    inference(avatar_split_clause,[],[f60,f162])).
% 2.34/0.67  fof(f60,plain,(
% 2.34/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f160,plain,(
% 2.34/0.67    ~spl4_8),
% 2.34/0.67    inference(avatar_split_clause,[],[f69,f157])).
% 2.34/0.67  fof(f69,plain,(
% 2.34/0.67    k2_funct_1(sK2) != sK3),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f155,plain,(
% 2.34/0.67    spl4_7),
% 2.34/0.67    inference(avatar_split_clause,[],[f62,f152])).
% 2.34/0.67  fof(f62,plain,(
% 2.34/0.67    v1_funct_2(sK3,sK1,sK0)),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f150,plain,(
% 2.34/0.67    spl4_6),
% 2.34/0.67    inference(avatar_split_clause,[],[f59,f147])).
% 2.34/0.67  fof(f59,plain,(
% 2.34/0.67    v1_funct_2(sK2,sK0,sK1)),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f140,plain,(
% 2.34/0.67    ~spl4_4),
% 2.34/0.67    inference(avatar_split_clause,[],[f67,f137])).
% 2.34/0.67  fof(f67,plain,(
% 2.34/0.67    k1_xboole_0 != sK0),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f130,plain,(
% 2.34/0.67    spl4_2),
% 2.34/0.67    inference(avatar_split_clause,[],[f61,f127])).
% 2.34/0.67  fof(f61,plain,(
% 2.34/0.67    v1_funct_1(sK3)),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  fof(f125,plain,(
% 2.34/0.67    spl4_1),
% 2.34/0.67    inference(avatar_split_clause,[],[f58,f122])).
% 2.34/0.67  fof(f58,plain,(
% 2.34/0.67    v1_funct_1(sK2)),
% 2.34/0.67    inference(cnf_transformation,[],[f56])).
% 2.34/0.67  % SZS output end Proof for theBenchmark
% 2.34/0.67  % (20536)------------------------------
% 2.34/0.67  % (20536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.67  % (20536)Termination reason: Refutation
% 2.34/0.67  
% 2.34/0.67  % (20536)Memory used [KB]: 12281
% 2.34/0.67  % (20536)Time elapsed: 0.198 s
% 2.34/0.67  % (20536)------------------------------
% 2.34/0.67  % (20536)------------------------------
% 2.34/0.68  % (20512)Success in time 0.32 s
%------------------------------------------------------------------------------
