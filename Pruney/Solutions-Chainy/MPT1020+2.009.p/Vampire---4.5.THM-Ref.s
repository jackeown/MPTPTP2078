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
% DateTime   : Thu Dec  3 13:05:41 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  352 ( 888 expanded)
%              Number of leaves         :   80 ( 376 expanded)
%              Depth                    :   11
%              Number of atoms          : 1245 (3687 expanded)
%              Number of equality atoms :  118 ( 263 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f107,f143,f156,f158,f160,f162,f177,f189,f198,f200,f202,f251,f256,f268,f274,f285,f316,f322,f352,f361,f363,f381,f438,f443,f448,f458,f463,f468,f470,f486,f541,f546,f551,f561,f566,f571,f573,f592,f605,f620,f630,f680,f709,f711,f713,f726,f745,f830,f865,f867,f875,f880,f885,f898,f911,f918,f927,f994,f1008,f1064,f1078,f1137])).

fof(f1137,plain,
    ( ~ spl3_24
    | ~ spl3_58 ),
    inference(avatar_contradiction_clause,[],[f1134])).

fof(f1134,plain,
    ( $false
    | ~ spl3_24
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f118,f1080])).

fof(f1080,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_24
    | ~ spl3_58 ),
    inference(superposition,[],[f259,f531])).

fof(f531,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl3_58
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f259,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ spl3_24 ),
    inference(superposition,[],[f49,f255])).

fof(f255,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl3_24
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f49,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f118,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f86,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f1078,plain,
    ( spl3_58
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_111
    | ~ spl3_116
    | ~ spl3_117
    | ~ spl3_123 ),
    inference(avatar_split_clause,[],[f1077,f1061,f923,f907,f877,f153,f91,f140,f145,f100,f529])).

fof(f100,plain,
    ( spl3_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f145,plain,
    ( spl3_7
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f140,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f91,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f153,plain,
    ( spl3_9
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f877,plain,
    ( spl3_111
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).

fof(f907,plain,
    ( spl3_116
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).

fof(f923,plain,
    ( spl3_117
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_117])])).

fof(f1061,plain,
    ( spl3_123
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).

fof(f1077,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_111
    | ~ spl3_116
    | ~ spl3_117
    | ~ spl3_123 ),
    inference(trivial_inequality_removal,[],[f1076])).

fof(f1076,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_111
    | ~ spl3_116
    | ~ spl3_117
    | ~ spl3_123 ),
    inference(forward_demodulation,[],[f1075,f879])).

fof(f879,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_111 ),
    inference(avatar_component_clause,[],[f877])).

fof(f1075,plain,
    ( sK0 != k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_116
    | ~ spl3_117
    | ~ spl3_123 ),
    inference(forward_demodulation,[],[f1074,f909])).

fof(f909,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_116 ),
    inference(avatar_component_clause,[],[f907])).

fof(f1074,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_117
    | ~ spl3_123 ),
    inference(trivial_inequality_removal,[],[f1073])).

fof(f1073,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_117
    | ~ spl3_123 ),
    inference(forward_demodulation,[],[f1072,f925])).

fof(f925,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_117 ),
    inference(avatar_component_clause,[],[f923])).

fof(f1072,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_123 ),
    inference(superposition,[],[f62,f1063])).

fof(f1063,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK1)
    | ~ spl3_123 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f1064,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | spl3_123
    | ~ spl3_40
    | ~ spl3_110 ),
    inference(avatar_split_clause,[],[f1059,f872,f417,f1061,f140,f132,f91])).

fof(f132,plain,
    ( spl3_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f417,plain,
    ( spl3_40
  <=> sK1 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f872,plain,
    ( spl3_110
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).

fof(f1059,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_40
    | ~ spl3_110 ),
    inference(forward_demodulation,[],[f1047,f874])).

fof(f874,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_110 ),
    inference(avatar_component_clause,[],[f872])).

fof(f1047,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_40 ),
    inference(superposition,[],[f60,f419])).

fof(f419,plain,
    ( sK1 = k2_funct_1(sK2)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f417])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1008,plain,
    ( spl3_40
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_69
    | ~ spl3_110
    | ~ spl3_116
    | ~ spl3_117 ),
    inference(avatar_split_clause,[],[f1007,f923,f907,f872,f608,f140,f100,f153,f132,f91,f417])).

fof(f608,plain,
    ( spl3_69
  <=> k6_relat_1(sK0) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f1007,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_69
    | ~ spl3_110
    | ~ spl3_116
    | ~ spl3_117 ),
    inference(trivial_inequality_removal,[],[f1006])).

fof(f1006,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_69
    | ~ spl3_110
    | ~ spl3_116
    | ~ spl3_117 ),
    inference(forward_demodulation,[],[f1005,f925])).

fof(f1005,plain,
    ( sK0 != k2_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_69
    | ~ spl3_110
    | ~ spl3_116 ),
    inference(forward_demodulation,[],[f1004,f874])).

fof(f1004,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_69
    | ~ spl3_116 ),
    inference(trivial_inequality_removal,[],[f1003])).

fof(f1003,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_69
    | ~ spl3_116 ),
    inference(forward_demodulation,[],[f1002,f909])).

fof(f1002,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_69 ),
    inference(superposition,[],[f62,f610])).

fof(f610,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f608])).

fof(f994,plain,
    ( ~ spl3_9
    | ~ spl3_35
    | ~ spl3_6
    | ~ spl3_37
    | spl3_69
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f991,f282,f608,f354,f140,f345,f153])).

fof(f345,plain,
    ( spl3_35
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f354,plain,
    ( spl3_37
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f282,plain,
    ( spl3_28
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f991,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_28 ),
    inference(superposition,[],[f78,f284])).

fof(f284,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f282])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f927,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | spl3_117
    | ~ spl3_113 ),
    inference(avatar_split_clause,[],[f920,f891,f923,f153,f145,f100])).

fof(f891,plain,
    ( spl3_113
  <=> sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).

fof(f920,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_113 ),
    inference(superposition,[],[f58,f893])).

fof(f893,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl3_113 ),
    inference(avatar_component_clause,[],[f891])).

fof(f58,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f918,plain,
    ( ~ spl3_71
    | spl3_114 ),
    inference(avatar_contradiction_clause,[],[f915])).

fof(f915,plain,
    ( $false
    | ~ spl3_71
    | spl3_114 ),
    inference(subsumption_resolution,[],[f783,f897])).

fof(f897,plain,
    ( ~ v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0)
    | spl3_114 ),
    inference(avatar_component_clause,[],[f895])).

fof(f895,plain,
    ( spl3_114
  <=> v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f783,plain,
    ( v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0)
    | ~ spl3_71 ),
    inference(resolution,[],[f629,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f629,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl3_71
  <=> m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f911,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | spl3_116
    | ~ spl3_112 ),
    inference(avatar_split_clause,[],[f904,f882,f907,f140,f132,f91])).

fof(f882,plain,
    ( spl3_112
  <=> sK0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).

fof(f904,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_112 ),
    inference(superposition,[],[f58,f884])).

fof(f884,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_112 ),
    inference(avatar_component_clause,[],[f882])).

fof(f898,plain,
    ( ~ spl3_66
    | ~ spl3_59
    | ~ spl3_60
    | spl3_113
    | ~ spl3_88
    | ~ spl3_114
    | ~ spl3_102 ),
    inference(avatar_split_clause,[],[f888,f827,f895,f742,f891,f538,f534,f568])).

fof(f568,plain,
    ( spl3_66
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f534,plain,
    ( spl3_59
  <=> v2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f538,plain,
    ( spl3_60
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f742,plain,
    ( spl3_88
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f827,plain,
    ( spl3_102
  <=> v2_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).

fof(f888,plain,
    ( ~ v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK1)))
    | sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_102 ),
    inference(resolution,[],[f829,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(k2_funct_1(X0),X1)
      | ~ v5_relat_1(k2_funct_1(X0),X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | k1_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f65,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f829,plain,
    ( v2_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0)
    | ~ spl3_102 ),
    inference(avatar_component_clause,[],[f827])).

fof(f885,plain,
    ( ~ spl3_50
    | ~ spl3_43
    | ~ spl3_44
    | spl3_112
    | ~ spl3_85
    | ~ spl3_87
    | ~ spl3_79 ),
    inference(avatar_split_clause,[],[f870,f677,f719,f706,f882,f435,f431,f465])).

fof(f465,plain,
    ( spl3_50
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f431,plain,
    ( spl3_43
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f435,plain,
    ( spl3_44
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f706,plain,
    ( spl3_85
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f719,plain,
    ( spl3_87
  <=> v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f677,plain,
    ( spl3_79
  <=> v2_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f870,plain,
    ( ~ v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | sK0 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_79 ),
    inference(resolution,[],[f122,f679])).

fof(f679,plain,
    ( v2_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f677])).

fof(f880,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | spl3_111
    | ~ spl3_66
    | ~ spl3_68
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f869,f543,f598,f568,f877,f153,f145,f100])).

fof(f598,plain,
    ( spl3_68
  <=> v5_relat_1(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f543,plain,
    ( spl3_61
  <=> v2_funct_2(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f869,plain,
    ( ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK0 = k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_61 ),
    inference(resolution,[],[f122,f545])).

fof(f545,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f543])).

fof(f875,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | spl3_110
    | ~ spl3_50
    | ~ spl3_52
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f868,f440,f479,f465,f872,f140,f132,f91])).

fof(f479,plain,
    ( spl3_52
  <=> v5_relat_1(k2_funct_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f440,plain,
    ( spl3_45
  <=> v2_funct_2(k2_funct_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f868,plain,
    ( ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | sK0 = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_45 ),
    inference(resolution,[],[f122,f442])).

fof(f442,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f440])).

fof(f867,plain,
    ( ~ spl3_62
    | ~ spl3_64
    | spl3_100 ),
    inference(avatar_contradiction_clause,[],[f866])).

fof(f866,plain,
    ( $false
    | ~ spl3_62
    | ~ spl3_64
    | spl3_100 ),
    inference(subsumption_resolution,[],[f623,f820])).

fof(f820,plain,
    ( ~ v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0)
    | spl3_100 ),
    inference(avatar_component_clause,[],[f818])).

fof(f818,plain,
    ( spl3_100
  <=> v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).

fof(f623,plain,
    ( v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0)
    | ~ spl3_62
    | ~ spl3_64 ),
    inference(superposition,[],[f550,f560])).

fof(f560,plain,
    ( k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f558])).

fof(f558,plain,
    ( spl3_64
  <=> k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f550,plain,
    ( v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0)
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl3_62
  <=> v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f865,plain,
    ( ~ spl3_64
    | ~ spl3_65
    | spl3_101 ),
    inference(avatar_contradiction_clause,[],[f864])).

fof(f864,plain,
    ( $false
    | ~ spl3_64
    | ~ spl3_65
    | spl3_101 ),
    inference(subsumption_resolution,[],[f624,f824])).

fof(f824,plain,
    ( ~ v1_funct_1(k2_funct_1(k2_funct_1(sK1)))
    | spl3_101 ),
    inference(avatar_component_clause,[],[f822])).

fof(f822,plain,
    ( spl3_101
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f624,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK1)))
    | ~ spl3_64
    | ~ spl3_65 ),
    inference(superposition,[],[f565,f560])).

fof(f565,plain,
    ( v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f563])).

fof(f563,plain,
    ( spl3_65
  <=> v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f830,plain,
    ( spl3_102
    | ~ spl3_100
    | ~ spl3_101
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f785,f627,f822,f818,f827])).

fof(f785,plain,
    ( ~ v1_funct_1(k2_funct_1(k2_funct_1(sK1)))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0)
    | v2_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0)
    | ~ spl3_71 ),
    inference(resolution,[],[f629,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f745,plain,
    ( ~ spl3_60
    | ~ spl3_26
    | ~ spl3_34
    | spl3_88
    | ~ spl3_38
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f740,f558,f358,f742,f319,f271,f538])).

fof(f271,plain,
    ( spl3_26
  <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f319,plain,
    ( spl3_34
  <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f358,plain,
    ( spl3_38
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f740,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK1)))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_38
    | ~ spl3_64 ),
    inference(forward_demodulation,[],[f732,f560])).

fof(f732,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v1_relat_1(k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ spl3_38 ),
    inference(resolution,[],[f328,f360])).

fof(f360,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f358])).

fof(f328,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v3_funct_2(X0,X1,X1)
      | ~ v1_funct_2(X0,X1,X1)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_2(X1,X0)) ) ),
    inference(resolution,[],[f70,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
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
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f726,plain,
    ( ~ spl3_70
    | spl3_87 ),
    inference(avatar_contradiction_clause,[],[f723])).

fof(f723,plain,
    ( $false
    | ~ spl3_70
    | spl3_87 ),
    inference(subsumption_resolution,[],[f635,f721])).

fof(f721,plain,
    ( ~ v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0)
    | spl3_87 ),
    inference(avatar_component_clause,[],[f719])).

fof(f635,plain,
    ( v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_70 ),
    inference(resolution,[],[f619,f73])).

fof(f619,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl3_70
  <=> m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f713,plain,
    ( ~ spl3_46
    | ~ spl3_48
    | spl3_77 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | ~ spl3_46
    | ~ spl3_48
    | spl3_77 ),
    inference(subsumption_resolution,[],[f613,f670])).

fof(f670,plain,
    ( ~ v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)
    | spl3_77 ),
    inference(avatar_component_clause,[],[f668])).

fof(f668,plain,
    ( spl3_77
  <=> v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f613,plain,
    ( v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(superposition,[],[f447,f457])).

fof(f457,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl3_48
  <=> k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f447,plain,
    ( v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK2)),sK0,sK0)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl3_46
  <=> v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK2)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f711,plain,
    ( ~ spl3_48
    | ~ spl3_49
    | spl3_78 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | ~ spl3_48
    | ~ spl3_49
    | spl3_78 ),
    inference(subsumption_resolution,[],[f614,f674])).

fof(f674,plain,
    ( ~ v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | spl3_78 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl3_78
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f614,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl3_48
    | ~ spl3_49 ),
    inference(superposition,[],[f462,f457])).

fof(f462,plain,
    ( v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK2)))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl3_49
  <=> v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f709,plain,
    ( spl3_85
    | ~ spl3_2
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f644,f617,f95,f706])).

fof(f95,plain,
    ( spl3_2
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f644,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl3_70 ),
    inference(resolution,[],[f619,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f680,plain,
    ( spl3_79
    | ~ spl3_77
    | ~ spl3_78
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f637,f617,f672,f668,f677])).

fof(f637,plain,
    ( ~ v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)
    | v2_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_70 ),
    inference(resolution,[],[f619,f75])).

fof(f630,plain,
    ( ~ spl3_60
    | ~ spl3_38
    | ~ spl3_34
    | ~ spl3_26
    | spl3_71
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f625,f558,f627,f271,f319,f358,f538])).

fof(f625,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_64 ),
    inference(superposition,[],[f70,f560])).

fof(f620,plain,
    ( ~ spl3_44
    | ~ spl3_36
    | ~ spl3_33
    | ~ spl3_25
    | spl3_70
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f615,f455,f617,f265,f313,f349,f435])).

fof(f349,plain,
    ( spl3_36
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f313,plain,
    ( spl3_33
  <=> v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f265,plain,
    ( spl3_25
  <=> v1_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f615,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_48 ),
    inference(superposition,[],[f70,f457])).

fof(f605,plain,
    ( ~ spl3_38
    | spl3_68 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl3_38
    | spl3_68 ),
    inference(subsumption_resolution,[],[f505,f600])).

fof(f600,plain,
    ( ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | spl3_68 ),
    inference(avatar_component_clause,[],[f598])).

fof(f505,plain,
    ( v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl3_38 ),
    inference(resolution,[],[f360,f73])).

fof(f592,plain,(
    spl3_27 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | spl3_27 ),
    inference(unit_resulting_resolution,[],[f50,f44,f47,f53,f280,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f280,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_27
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f573,plain,
    ( ~ spl3_14
    | ~ spl3_24
    | spl3_60 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_24
    | spl3_60 ),
    inference(subsumption_resolution,[],[f258,f540])).

fof(f540,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_60 ),
    inference(avatar_component_clause,[],[f538])).

fof(f258,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(superposition,[],[f193,f255])).

fof(f193,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_14
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f571,plain,
    ( spl3_66
    | ~ spl3_2
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f514,f358,f95,f568])).

fof(f514,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_38 ),
    inference(resolution,[],[f360,f57])).

fof(f566,plain,
    ( spl3_65
    | ~ spl3_60
    | ~ spl3_34
    | ~ spl3_26
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f513,f358,f271,f319,f538,f563])).

fof(f513,plain,
    ( ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ spl3_38 ),
    inference(resolution,[],[f360,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f561,plain,
    ( spl3_64
    | ~ spl3_60
    | ~ spl3_34
    | ~ spl3_26
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f512,f358,f271,f319,f538,f558])).

fof(f512,plain,
    ( ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1))
    | ~ spl3_38 ),
    inference(resolution,[],[f360,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f551,plain,
    ( spl3_62
    | ~ spl3_60
    | ~ spl3_34
    | ~ spl3_26
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f510,f358,f271,f319,f538,f548])).

fof(f510,plain,
    ( ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0)
    | ~ spl3_38 ),
    inference(resolution,[],[f360,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f546,plain,
    ( spl3_61
    | ~ spl3_34
    | ~ spl3_60
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f507,f358,f538,f319,f543])).

fof(f507,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ spl3_38 ),
    inference(resolution,[],[f360,f75])).

fof(f541,plain,
    ( spl3_59
    | ~ spl3_34
    | ~ spl3_60
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f506,f358,f538,f319,f534])).

fof(f506,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | v2_funct_1(k2_funct_1(sK1))
    | ~ spl3_38 ),
    inference(resolution,[],[f360,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f486,plain,
    ( ~ spl3_36
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f483])).

fof(f483,plain,
    ( $false
    | ~ spl3_36
    | spl3_52 ),
    inference(subsumption_resolution,[],[f402,f481])).

fof(f481,plain,
    ( ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | spl3_52 ),
    inference(avatar_component_clause,[],[f479])).

fof(f402,plain,
    ( v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ spl3_36 ),
    inference(resolution,[],[f351,f73])).

fof(f351,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f349])).

fof(f470,plain,
    ( ~ spl3_12
    | ~ spl3_23
    | spl3_44 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_23
    | spl3_44 ),
    inference(subsumption_resolution,[],[f257,f437])).

fof(f437,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f435])).

fof(f257,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(superposition,[],[f184,f250])).

fof(f250,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl3_23
  <=> k2_funct_1(sK2) = k2_funct_2(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f184,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_12
  <=> v1_funct_1(k2_funct_2(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f468,plain,
    ( spl3_50
    | ~ spl3_2
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f411,f349,f95,f465])).

fof(f411,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_36 ),
    inference(resolution,[],[f351,f57])).

fof(f463,plain,
    ( spl3_49
    | ~ spl3_44
    | ~ spl3_33
    | ~ spl3_25
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f410,f349,f265,f313,f435,f460])).

fof(f410,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK2)))
    | ~ spl3_36 ),
    inference(resolution,[],[f351,f67])).

fof(f458,plain,
    ( spl3_48
    | ~ spl3_44
    | ~ spl3_33
    | ~ spl3_25
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f409,f349,f265,f313,f435,f455])).

fof(f409,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2))
    | ~ spl3_36 ),
    inference(resolution,[],[f351,f66])).

fof(f448,plain,
    ( spl3_46
    | ~ spl3_44
    | ~ spl3_33
    | ~ spl3_25
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f407,f349,f265,f313,f435,f445])).

fof(f407,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK2)),sK0,sK0)
    | ~ spl3_36 ),
    inference(resolution,[],[f351,f69])).

fof(f443,plain,
    ( spl3_45
    | ~ spl3_33
    | ~ spl3_44
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f404,f349,f435,f313,f440])).

fof(f404,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ spl3_36 ),
    inference(resolution,[],[f351,f75])).

fof(f438,plain,
    ( spl3_43
    | ~ spl3_33
    | ~ spl3_44
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f403,f349,f435,f313,f431])).

fof(f403,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_36 ),
    inference(resolution,[],[f351,f74])).

fof(f381,plain,(
    spl3_37 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl3_37 ),
    inference(subsumption_resolution,[],[f53,f356])).

fof(f356,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f354])).

fof(f363,plain,(
    spl3_35 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl3_35 ),
    inference(subsumption_resolution,[],[f47,f347])).

fof(f347,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f345])).

fof(f361,plain,
    ( ~ spl3_9
    | ~ spl3_37
    | ~ spl3_8
    | ~ spl3_15
    | spl3_38
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f343,f253,f358,f195,f149,f354,f153])).

fof(f149,plain,
    ( spl3_8
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f195,plain,
    ( spl3_15
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f343,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_24 ),
    inference(superposition,[],[f70,f255])).

fof(f352,plain,
    ( ~ spl3_6
    | ~ spl3_35
    | ~ spl3_5
    | ~ spl3_13
    | spl3_36
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f342,f248,f349,f186,f136,f345,f140])).

fof(f136,plain,
    ( spl3_5
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f186,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f342,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_23 ),
    inference(superposition,[],[f70,f250])).

fof(f322,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | ~ spl3_15
    | spl3_34
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f317,f253,f319,f195,f149,f153])).

fof(f317,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f309,f255])).

fof(f309,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(resolution,[],[f69,f53])).

fof(f316,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | ~ spl3_13
    | spl3_33
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f311,f248,f313,f186,f136,f140])).

fof(f311,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f308,f250])).

fof(f308,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(resolution,[],[f69,f47])).

fof(f285,plain,
    ( ~ spl3_27
    | spl3_28 ),
    inference(avatar_split_clause,[],[f275,f282,f278])).

fof(f275,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f205,f81])).

fof(f81,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f54,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f48,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f205,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_relat_1(X3))
      | k6_relat_1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f77,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f56,f54])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f274,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | ~ spl3_15
    | spl3_26
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f269,f253,f271,f195,f149,f153])).

fof(f269,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f261,f255])).

fof(f261,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(resolution,[],[f68,f53])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | v1_funct_2(k2_funct_2(X0,X1),X0,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f268,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | ~ spl3_13
    | spl3_25
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f263,f248,f265,f186,f136,f140])).

fof(f263,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f260,f250])).

fof(f260,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(resolution,[],[f68,f47])).

fof(f256,plain,
    ( spl3_24
    | ~ spl3_9
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f245,f195,f149,f153,f253])).

fof(f245,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f66,f53])).

fof(f251,plain,
    ( spl3_23
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f244,f186,f136,f140,f248])).

fof(f244,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_2(sK0,sK2) ),
    inference(resolution,[],[f66,f47])).

fof(f202,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl3_15 ),
    inference(subsumption_resolution,[],[f51,f197])).

fof(f197,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f51,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f200,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f45,f188])).

fof(f188,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f198,plain,
    ( spl3_14
    | ~ spl3_9
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f179,f195,f149,f153,f191])).

fof(f179,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f67,f53])).

fof(f189,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f178,f186,f136,f140,f182])).

fof(f178,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(resolution,[],[f67,f47])).

fof(f177,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f52,f151])).

fof(f151,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f52,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f162,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f44,f142])).

fof(f142,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f160,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f46,f138])).

fof(f138,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f46,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f158,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f50,f155])).

fof(f155,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f156,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f129,f153,f149,f145])).

fof(f129,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f74,f53])).

fof(f143,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f128,f140,f136,f132])).

fof(f128,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f74,f47])).

fof(f107,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f63,f97])).

fof(f97,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f103,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f88,f95,f100])).

fof(f88,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(resolution,[],[f57,f53])).

fof(f98,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f87,f95,f91])).

fof(f87,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:53:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (12243)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (12235)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (12227)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (12220)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (12221)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (12222)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (12223)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (12225)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (12224)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (12226)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (12241)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (12247)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (12238)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (12239)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (12244)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.55  % (12229)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (12233)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.37/0.55  % (12236)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.55  % (12236)Refutation not found, incomplete strategy% (12236)------------------------------
% 1.37/0.55  % (12236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (12236)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (12236)Memory used [KB]: 10746
% 1.37/0.55  % (12236)Time elapsed: 0.149 s
% 1.37/0.55  % (12236)------------------------------
% 1.37/0.55  % (12236)------------------------------
% 1.37/0.55  % (12246)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (12231)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.56  % (12230)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.37/0.56  % (12248)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.56  % (12232)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.56  % (12242)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.52/0.56  % (12237)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.57  % (12249)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.52/0.57  % (12228)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.52/0.57  % (12240)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.57  % (12234)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.52/0.58  % (12245)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.52/0.61  % (12233)Refutation found. Thanks to Tanya!
% 1.52/0.61  % SZS status Theorem for theBenchmark
% 1.52/0.61  % SZS output start Proof for theBenchmark
% 1.52/0.61  fof(f1138,plain,(
% 1.52/0.61    $false),
% 1.52/0.61    inference(avatar_sat_refutation,[],[f98,f103,f107,f143,f156,f158,f160,f162,f177,f189,f198,f200,f202,f251,f256,f268,f274,f285,f316,f322,f352,f361,f363,f381,f438,f443,f448,f458,f463,f468,f470,f486,f541,f546,f551,f561,f566,f571,f573,f592,f605,f620,f630,f680,f709,f711,f713,f726,f745,f830,f865,f867,f875,f880,f885,f898,f911,f918,f927,f994,f1008,f1064,f1078,f1137])).
% 1.52/0.61  fof(f1137,plain,(
% 1.52/0.61    ~spl3_24 | ~spl3_58),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f1134])).
% 1.52/0.61  fof(f1134,plain,(
% 1.52/0.61    $false | (~spl3_24 | ~spl3_58)),
% 1.52/0.61    inference(subsumption_resolution,[],[f118,f1080])).
% 1.52/0.61  fof(f1080,plain,(
% 1.52/0.61    ~r2_relset_1(sK0,sK0,sK2,sK2) | (~spl3_24 | ~spl3_58)),
% 1.52/0.61    inference(superposition,[],[f259,f531])).
% 1.52/0.61  fof(f531,plain,(
% 1.52/0.61    sK2 = k2_funct_1(sK1) | ~spl3_58),
% 1.52/0.61    inference(avatar_component_clause,[],[f529])).
% 1.52/0.61  fof(f529,plain,(
% 1.52/0.61    spl3_58 <=> sK2 = k2_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 1.52/0.61  fof(f259,plain,(
% 1.52/0.61    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~spl3_24),
% 1.52/0.61    inference(superposition,[],[f49,f255])).
% 1.52/0.61  fof(f255,plain,(
% 1.52/0.61    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_24),
% 1.52/0.61    inference(avatar_component_clause,[],[f253])).
% 1.52/0.61  fof(f253,plain,(
% 1.52/0.61    spl3_24 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.52/0.61  fof(f49,plain,(
% 1.52/0.61    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.52/0.61    inference(cnf_transformation,[],[f20])).
% 1.52/0.61  fof(f20,plain,(
% 1.52/0.61    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.52/0.61    inference(flattening,[],[f19])).
% 1.52/0.61  fof(f19,plain,(
% 1.52/0.61    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f18])).
% 1.52/0.61  fof(f18,negated_conjecture,(
% 1.52/0.61    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.52/0.61    inference(negated_conjecture,[],[f17])).
% 1.52/0.61  fof(f17,conjecture,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.52/0.61  fof(f118,plain,(
% 1.52/0.61    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.52/0.61    inference(resolution,[],[f86,f47])).
% 1.52/0.61  fof(f47,plain,(
% 1.52/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    inference(cnf_transformation,[],[f20])).
% 1.52/0.61  fof(f86,plain,(
% 1.52/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.52/0.61    inference(duplicate_literal_removal,[],[f85])).
% 1.52/0.61  fof(f85,plain,(
% 1.52/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.52/0.61    inference(equality_resolution,[],[f76])).
% 1.52/0.61  fof(f76,plain,(
% 1.52/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f39])).
% 1.52/0.61  fof(f39,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(flattening,[],[f38])).
% 1.52/0.61  fof(f38,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.52/0.61    inference(ennf_transformation,[],[f8])).
% 1.52/0.61  fof(f8,axiom,(
% 1.52/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.52/0.61  fof(f1078,plain,(
% 1.52/0.61    spl3_58 | ~spl3_3 | ~spl3_7 | ~spl3_6 | ~spl3_1 | ~spl3_9 | ~spl3_111 | ~spl3_116 | ~spl3_117 | ~spl3_123),
% 1.52/0.61    inference(avatar_split_clause,[],[f1077,f1061,f923,f907,f877,f153,f91,f140,f145,f100,f529])).
% 1.52/0.61  fof(f100,plain,(
% 1.52/0.61    spl3_3 <=> v1_relat_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.52/0.61  fof(f145,plain,(
% 1.52/0.61    spl3_7 <=> v2_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.52/0.61  fof(f140,plain,(
% 1.52/0.61    spl3_6 <=> v1_funct_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.52/0.61  fof(f91,plain,(
% 1.52/0.61    spl3_1 <=> v1_relat_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.52/0.61  fof(f153,plain,(
% 1.52/0.61    spl3_9 <=> v1_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.52/0.61  fof(f877,plain,(
% 1.52/0.61    spl3_111 <=> sK0 = k1_relat_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).
% 1.52/0.61  fof(f907,plain,(
% 1.52/0.61    spl3_116 <=> sK0 = k2_relat_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).
% 1.52/0.61  fof(f923,plain,(
% 1.52/0.61    spl3_117 <=> sK0 = k2_relat_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_117])])).
% 1.52/0.61  fof(f1061,plain,(
% 1.52/0.61    spl3_123 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).
% 1.52/0.61  fof(f1077,plain,(
% 1.52/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_111 | ~spl3_116 | ~spl3_117 | ~spl3_123)),
% 1.52/0.61    inference(trivial_inequality_removal,[],[f1076])).
% 1.52/0.61  fof(f1076,plain,(
% 1.52/0.61    sK0 != sK0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_111 | ~spl3_116 | ~spl3_117 | ~spl3_123)),
% 1.52/0.61    inference(forward_demodulation,[],[f1075,f879])).
% 1.52/0.61  fof(f879,plain,(
% 1.52/0.61    sK0 = k1_relat_1(sK1) | ~spl3_111),
% 1.52/0.61    inference(avatar_component_clause,[],[f877])).
% 1.52/0.61  fof(f1075,plain,(
% 1.52/0.61    sK0 != k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_116 | ~spl3_117 | ~spl3_123)),
% 1.52/0.61    inference(forward_demodulation,[],[f1074,f909])).
% 1.52/0.61  fof(f909,plain,(
% 1.52/0.61    sK0 = k2_relat_1(sK2) | ~spl3_116),
% 1.52/0.61    inference(avatar_component_clause,[],[f907])).
% 1.52/0.61  fof(f1074,plain,(
% 1.52/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_117 | ~spl3_123)),
% 1.52/0.61    inference(trivial_inequality_removal,[],[f1073])).
% 1.52/0.61  fof(f1073,plain,(
% 1.52/0.61    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_117 | ~spl3_123)),
% 1.52/0.61    inference(forward_demodulation,[],[f1072,f925])).
% 1.52/0.61  fof(f925,plain,(
% 1.52/0.61    sK0 = k2_relat_1(sK1) | ~spl3_117),
% 1.52/0.61    inference(avatar_component_clause,[],[f923])).
% 1.52/0.61  fof(f1072,plain,(
% 1.52/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | ~spl3_123),
% 1.52/0.61    inference(superposition,[],[f62,f1063])).
% 1.52/0.61  fof(f1063,plain,(
% 1.52/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK1) | ~spl3_123),
% 1.52/0.61    inference(avatar_component_clause,[],[f1061])).
% 1.52/0.61  fof(f62,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.52/0.61    inference(cnf_transformation,[],[f27])).
% 1.52/0.61  fof(f27,plain,(
% 1.52/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.61    inference(flattening,[],[f26])).
% 1.52/0.61  fof(f26,plain,(
% 1.52/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.61    inference(ennf_transformation,[],[f5])).
% 1.52/0.61  fof(f5,axiom,(
% 1.52/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.52/0.61  fof(f1064,plain,(
% 1.52/0.61    ~spl3_1 | ~spl3_4 | ~spl3_6 | spl3_123 | ~spl3_40 | ~spl3_110),
% 1.52/0.61    inference(avatar_split_clause,[],[f1059,f872,f417,f1061,f140,f132,f91])).
% 1.52/0.61  fof(f132,plain,(
% 1.52/0.61    spl3_4 <=> v2_funct_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.52/0.61  fof(f417,plain,(
% 1.52/0.61    spl3_40 <=> sK1 = k2_funct_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.52/0.61  fof(f872,plain,(
% 1.52/0.61    spl3_110 <=> sK0 = k1_relat_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).
% 1.52/0.61  fof(f1059,plain,(
% 1.52/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_40 | ~spl3_110)),
% 1.52/0.61    inference(forward_demodulation,[],[f1047,f874])).
% 1.52/0.61  fof(f874,plain,(
% 1.52/0.61    sK0 = k1_relat_1(sK2) | ~spl3_110),
% 1.52/0.61    inference(avatar_component_clause,[],[f872])).
% 1.52/0.61  fof(f1047,plain,(
% 1.52/0.61    k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_40),
% 1.52/0.61    inference(superposition,[],[f60,f419])).
% 1.52/0.61  fof(f419,plain,(
% 1.52/0.61    sK1 = k2_funct_1(sK2) | ~spl3_40),
% 1.52/0.61    inference(avatar_component_clause,[],[f417])).
% 1.52/0.61  fof(f60,plain,(
% 1.52/0.61    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f25])).
% 1.52/0.61  fof(f25,plain,(
% 1.52/0.61    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.61    inference(flattening,[],[f24])).
% 1.52/0.61  fof(f24,plain,(
% 1.52/0.61    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.61    inference(ennf_transformation,[],[f4])).
% 1.52/0.61  fof(f4,axiom,(
% 1.52/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.52/0.61  fof(f1008,plain,(
% 1.52/0.61    spl3_40 | ~spl3_1 | ~spl3_4 | ~spl3_9 | ~spl3_3 | ~spl3_6 | ~spl3_69 | ~spl3_110 | ~spl3_116 | ~spl3_117),
% 1.52/0.61    inference(avatar_split_clause,[],[f1007,f923,f907,f872,f608,f140,f100,f153,f132,f91,f417])).
% 1.52/0.61  fof(f608,plain,(
% 1.52/0.61    spl3_69 <=> k6_relat_1(sK0) = k5_relat_1(sK1,sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 1.52/0.61  fof(f1007,plain,(
% 1.52/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | (~spl3_69 | ~spl3_110 | ~spl3_116 | ~spl3_117)),
% 1.52/0.61    inference(trivial_inequality_removal,[],[f1006])).
% 1.52/0.61  fof(f1006,plain,(
% 1.52/0.61    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | (~spl3_69 | ~spl3_110 | ~spl3_116 | ~spl3_117)),
% 1.52/0.61    inference(forward_demodulation,[],[f1005,f925])).
% 1.52/0.61  fof(f1005,plain,(
% 1.52/0.61    sK0 != k2_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | (~spl3_69 | ~spl3_110 | ~spl3_116)),
% 1.52/0.61    inference(forward_demodulation,[],[f1004,f874])).
% 1.52/0.61  fof(f1004,plain,(
% 1.52/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | (~spl3_69 | ~spl3_116)),
% 1.52/0.61    inference(trivial_inequality_removal,[],[f1003])).
% 1.52/0.61  fof(f1003,plain,(
% 1.52/0.61    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | (~spl3_69 | ~spl3_116)),
% 1.52/0.61    inference(forward_demodulation,[],[f1002,f909])).
% 1.52/0.61  fof(f1002,plain,(
% 1.52/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | ~spl3_69),
% 1.52/0.61    inference(superposition,[],[f62,f610])).
% 1.52/0.61  fof(f610,plain,(
% 1.52/0.61    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~spl3_69),
% 1.52/0.61    inference(avatar_component_clause,[],[f608])).
% 1.52/0.61  fof(f994,plain,(
% 1.52/0.61    ~spl3_9 | ~spl3_35 | ~spl3_6 | ~spl3_37 | spl3_69 | ~spl3_28),
% 1.52/0.61    inference(avatar_split_clause,[],[f991,f282,f608,f354,f140,f345,f153])).
% 1.52/0.61  fof(f345,plain,(
% 1.52/0.61    spl3_35 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.52/0.61  fof(f354,plain,(
% 1.52/0.61    spl3_37 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.52/0.61  fof(f282,plain,(
% 1.52/0.61    spl3_28 <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.52/0.61  fof(f991,plain,(
% 1.52/0.61    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl3_28),
% 1.52/0.61    inference(superposition,[],[f78,f284])).
% 1.52/0.61  fof(f284,plain,(
% 1.52/0.61    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~spl3_28),
% 1.52/0.61    inference(avatar_component_clause,[],[f282])).
% 1.52/0.61  fof(f78,plain,(
% 1.52/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f41])).
% 1.52/0.61  fof(f41,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.52/0.61    inference(flattening,[],[f40])).
% 1.52/0.61  fof(f40,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.52/0.61    inference(ennf_transformation,[],[f14])).
% 1.52/0.61  fof(f14,axiom,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.52/0.61  fof(f927,plain,(
% 1.52/0.61    ~spl3_3 | ~spl3_7 | ~spl3_9 | spl3_117 | ~spl3_113),
% 1.52/0.61    inference(avatar_split_clause,[],[f920,f891,f923,f153,f145,f100])).
% 1.52/0.61  fof(f891,plain,(
% 1.52/0.61    spl3_113 <=> sK0 = k1_relat_1(k2_funct_1(sK1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).
% 1.52/0.61  fof(f920,plain,(
% 1.52/0.61    sK0 = k2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_113),
% 1.52/0.61    inference(superposition,[],[f58,f893])).
% 1.52/0.61  fof(f893,plain,(
% 1.52/0.61    sK0 = k1_relat_1(k2_funct_1(sK1)) | ~spl3_113),
% 1.52/0.61    inference(avatar_component_clause,[],[f891])).
% 1.52/0.61  fof(f58,plain,(
% 1.52/0.61    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f23])).
% 1.52/0.61  fof(f23,plain,(
% 1.52/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.61    inference(flattening,[],[f22])).
% 1.52/0.61  fof(f22,plain,(
% 1.52/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.61    inference(ennf_transformation,[],[f3])).
% 1.52/0.61  fof(f3,axiom,(
% 1.52/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.52/0.61  fof(f918,plain,(
% 1.52/0.61    ~spl3_71 | spl3_114),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f915])).
% 1.52/0.61  fof(f915,plain,(
% 1.52/0.61    $false | (~spl3_71 | spl3_114)),
% 1.52/0.61    inference(subsumption_resolution,[],[f783,f897])).
% 1.52/0.61  fof(f897,plain,(
% 1.52/0.61    ~v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0) | spl3_114),
% 1.52/0.61    inference(avatar_component_clause,[],[f895])).
% 1.52/0.61  fof(f895,plain,(
% 1.52/0.61    spl3_114 <=> v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 1.52/0.61  fof(f783,plain,(
% 1.52/0.61    v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0) | ~spl3_71),
% 1.52/0.61    inference(resolution,[],[f629,f73])).
% 1.52/0.61  fof(f73,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f35])).
% 1.52/0.61  fof(f35,plain,(
% 1.52/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(ennf_transformation,[],[f7])).
% 1.52/0.61  fof(f7,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.52/0.61  fof(f629,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_71),
% 1.52/0.61    inference(avatar_component_clause,[],[f627])).
% 1.52/0.61  fof(f627,plain,(
% 1.52/0.61    spl3_71 <=> m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 1.52/0.61  fof(f911,plain,(
% 1.52/0.61    ~spl3_1 | ~spl3_4 | ~spl3_6 | spl3_116 | ~spl3_112),
% 1.52/0.61    inference(avatar_split_clause,[],[f904,f882,f907,f140,f132,f91])).
% 1.52/0.61  fof(f882,plain,(
% 1.52/0.61    spl3_112 <=> sK0 = k1_relat_1(k2_funct_1(sK2))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).
% 1.52/0.61  fof(f904,plain,(
% 1.52/0.61    sK0 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_112),
% 1.52/0.61    inference(superposition,[],[f58,f884])).
% 1.52/0.61  fof(f884,plain,(
% 1.52/0.61    sK0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_112),
% 1.52/0.61    inference(avatar_component_clause,[],[f882])).
% 1.52/0.61  fof(f898,plain,(
% 1.52/0.61    ~spl3_66 | ~spl3_59 | ~spl3_60 | spl3_113 | ~spl3_88 | ~spl3_114 | ~spl3_102),
% 1.52/0.61    inference(avatar_split_clause,[],[f888,f827,f895,f742,f891,f538,f534,f568])).
% 1.52/0.61  fof(f568,plain,(
% 1.52/0.61    spl3_66 <=> v1_relat_1(k2_funct_1(sK1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 1.52/0.61  fof(f534,plain,(
% 1.52/0.61    spl3_59 <=> v2_funct_1(k2_funct_1(sK1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.52/0.61  fof(f538,plain,(
% 1.52/0.61    spl3_60 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.52/0.61  fof(f742,plain,(
% 1.52/0.61    spl3_88 <=> v1_relat_1(k2_funct_1(k2_funct_1(sK1)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 1.52/0.61  fof(f827,plain,(
% 1.52/0.61    spl3_102 <=> v2_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).
% 1.52/0.61  fof(f888,plain,(
% 1.52/0.61    ~v5_relat_1(k2_funct_1(k2_funct_1(sK1)),sK0) | ~v1_relat_1(k2_funct_1(k2_funct_1(sK1))) | sK0 = k1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl3_102),
% 1.52/0.61    inference(resolution,[],[f829,f122])).
% 1.52/0.61  fof(f122,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~v2_funct_2(k2_funct_1(X0),X1) | ~v5_relat_1(k2_funct_1(X0),X1) | ~v1_relat_1(k2_funct_1(X0)) | k1_relat_1(X0) = X1 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.61    inference(superposition,[],[f65,f59])).
% 1.52/0.61  fof(f59,plain,(
% 1.52/0.61    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f23])).
% 1.52/0.61  fof(f65,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v2_funct_2(X1,X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f29])).
% 1.52/0.61  fof(f29,plain,(
% 1.52/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.52/0.61    inference(flattening,[],[f28])).
% 1.52/0.61  fof(f28,plain,(
% 1.52/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f10])).
% 1.52/0.61  fof(f10,axiom,(
% 1.52/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.52/0.61  fof(f829,plain,(
% 1.52/0.61    v2_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0) | ~spl3_102),
% 1.52/0.61    inference(avatar_component_clause,[],[f827])).
% 1.52/0.61  fof(f885,plain,(
% 1.52/0.61    ~spl3_50 | ~spl3_43 | ~spl3_44 | spl3_112 | ~spl3_85 | ~spl3_87 | ~spl3_79),
% 1.52/0.61    inference(avatar_split_clause,[],[f870,f677,f719,f706,f882,f435,f431,f465])).
% 1.52/0.61  fof(f465,plain,(
% 1.52/0.61    spl3_50 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 1.52/0.61  fof(f431,plain,(
% 1.52/0.61    spl3_43 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.52/0.61  fof(f435,plain,(
% 1.52/0.61    spl3_44 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.52/0.61  fof(f706,plain,(
% 1.52/0.61    spl3_85 <=> v1_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 1.52/0.61  fof(f719,plain,(
% 1.52/0.61    spl3_87 <=> v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 1.52/0.61  fof(f677,plain,(
% 1.52/0.61    spl3_79 <=> v2_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 1.52/0.61  fof(f870,plain,(
% 1.52/0.61    ~v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(k2_funct_1(sK2))) | sK0 = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_79),
% 1.52/0.61    inference(resolution,[],[f122,f679])).
% 1.52/0.61  fof(f679,plain,(
% 1.52/0.61    v2_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0) | ~spl3_79),
% 1.52/0.61    inference(avatar_component_clause,[],[f677])).
% 1.52/0.61  fof(f880,plain,(
% 1.52/0.61    ~spl3_3 | ~spl3_7 | ~spl3_9 | spl3_111 | ~spl3_66 | ~spl3_68 | ~spl3_61),
% 1.52/0.61    inference(avatar_split_clause,[],[f869,f543,f598,f568,f877,f153,f145,f100])).
% 1.52/0.61  fof(f598,plain,(
% 1.52/0.61    spl3_68 <=> v5_relat_1(k2_funct_1(sK1),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 1.52/0.61  fof(f543,plain,(
% 1.52/0.61    spl3_61 <=> v2_funct_2(k2_funct_1(sK1),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 1.52/0.61  fof(f869,plain,(
% 1.52/0.61    ~v5_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1)) | sK0 = k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_61),
% 1.52/0.61    inference(resolution,[],[f122,f545])).
% 1.52/0.61  fof(f545,plain,(
% 1.52/0.61    v2_funct_2(k2_funct_1(sK1),sK0) | ~spl3_61),
% 1.52/0.61    inference(avatar_component_clause,[],[f543])).
% 1.52/0.61  fof(f875,plain,(
% 1.52/0.61    ~spl3_1 | ~spl3_4 | ~spl3_6 | spl3_110 | ~spl3_50 | ~spl3_52 | ~spl3_45),
% 1.52/0.61    inference(avatar_split_clause,[],[f868,f440,f479,f465,f872,f140,f132,f91])).
% 1.52/0.61  fof(f479,plain,(
% 1.52/0.61    spl3_52 <=> v5_relat_1(k2_funct_1(sK2),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.52/0.61  fof(f440,plain,(
% 1.52/0.61    spl3_45 <=> v2_funct_2(k2_funct_1(sK2),sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.52/0.61  fof(f868,plain,(
% 1.52/0.61    ~v5_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | sK0 = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_45),
% 1.52/0.61    inference(resolution,[],[f122,f442])).
% 1.52/0.61  fof(f442,plain,(
% 1.52/0.61    v2_funct_2(k2_funct_1(sK2),sK0) | ~spl3_45),
% 1.52/0.61    inference(avatar_component_clause,[],[f440])).
% 1.52/0.61  fof(f867,plain,(
% 1.52/0.61    ~spl3_62 | ~spl3_64 | spl3_100),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f866])).
% 1.52/0.61  fof(f866,plain,(
% 1.52/0.61    $false | (~spl3_62 | ~spl3_64 | spl3_100)),
% 1.52/0.61    inference(subsumption_resolution,[],[f623,f820])).
% 1.52/0.61  fof(f820,plain,(
% 1.52/0.61    ~v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0) | spl3_100),
% 1.52/0.61    inference(avatar_component_clause,[],[f818])).
% 1.52/0.61  fof(f818,plain,(
% 1.52/0.61    spl3_100 <=> v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).
% 1.52/0.61  fof(f623,plain,(
% 1.52/0.61    v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0) | (~spl3_62 | ~spl3_64)),
% 1.52/0.61    inference(superposition,[],[f550,f560])).
% 1.52/0.61  fof(f560,plain,(
% 1.52/0.61    k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1)) | ~spl3_64),
% 1.52/0.61    inference(avatar_component_clause,[],[f558])).
% 1.52/0.61  fof(f558,plain,(
% 1.52/0.61    spl3_64 <=> k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 1.52/0.61  fof(f550,plain,(
% 1.52/0.61    v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0) | ~spl3_62),
% 1.52/0.61    inference(avatar_component_clause,[],[f548])).
% 1.52/0.61  fof(f548,plain,(
% 1.52/0.61    spl3_62 <=> v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.52/0.61  fof(f865,plain,(
% 1.52/0.61    ~spl3_64 | ~spl3_65 | spl3_101),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f864])).
% 1.52/0.61  fof(f864,plain,(
% 1.52/0.61    $false | (~spl3_64 | ~spl3_65 | spl3_101)),
% 1.52/0.61    inference(subsumption_resolution,[],[f624,f824])).
% 1.52/0.61  fof(f824,plain,(
% 1.52/0.61    ~v1_funct_1(k2_funct_1(k2_funct_1(sK1))) | spl3_101),
% 1.52/0.61    inference(avatar_component_clause,[],[f822])).
% 1.52/0.61  fof(f822,plain,(
% 1.52/0.61    spl3_101 <=> v1_funct_1(k2_funct_1(k2_funct_1(sK1)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 1.52/0.61  fof(f624,plain,(
% 1.52/0.61    v1_funct_1(k2_funct_1(k2_funct_1(sK1))) | (~spl3_64 | ~spl3_65)),
% 1.52/0.61    inference(superposition,[],[f565,f560])).
% 1.52/0.61  fof(f565,plain,(
% 1.52/0.61    v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1))) | ~spl3_65),
% 1.52/0.61    inference(avatar_component_clause,[],[f563])).
% 1.52/0.61  fof(f563,plain,(
% 1.52/0.61    spl3_65 <=> v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 1.52/0.61  fof(f830,plain,(
% 1.52/0.61    spl3_102 | ~spl3_100 | ~spl3_101 | ~spl3_71),
% 1.52/0.61    inference(avatar_split_clause,[],[f785,f627,f822,f818,f827])).
% 1.52/0.61  fof(f785,plain,(
% 1.52/0.61    ~v1_funct_1(k2_funct_1(k2_funct_1(sK1))) | ~v3_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0,sK0) | v2_funct_2(k2_funct_1(k2_funct_1(sK1)),sK0) | ~spl3_71),
% 1.52/0.61    inference(resolution,[],[f629,f75])).
% 1.52/0.61  fof(f75,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f37])).
% 1.52/0.61  fof(f37,plain,(
% 1.52/0.61    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(flattening,[],[f36])).
% 1.52/0.61  fof(f36,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(ennf_transformation,[],[f9])).
% 1.52/0.61  fof(f9,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.52/0.61  fof(f745,plain,(
% 1.52/0.61    ~spl3_60 | ~spl3_26 | ~spl3_34 | spl3_88 | ~spl3_38 | ~spl3_64),
% 1.52/0.61    inference(avatar_split_clause,[],[f740,f558,f358,f742,f319,f271,f538])).
% 1.52/0.61  fof(f271,plain,(
% 1.52/0.61    spl3_26 <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.52/0.61  fof(f319,plain,(
% 1.52/0.61    spl3_34 <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.52/0.61  fof(f358,plain,(
% 1.52/0.61    spl3_38 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.52/0.61  fof(f740,plain,(
% 1.52/0.61    v1_relat_1(k2_funct_1(k2_funct_1(sK1))) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | (~spl3_38 | ~spl3_64)),
% 1.52/0.61    inference(forward_demodulation,[],[f732,f560])).
% 1.52/0.61  fof(f732,plain,(
% 1.52/0.61    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v1_relat_1(k2_funct_2(sK0,k2_funct_1(sK1))) | ~spl3_38),
% 1.52/0.61    inference(resolution,[],[f328,f360])).
% 1.52/0.61  fof(f360,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_38),
% 1.52/0.61    inference(avatar_component_clause,[],[f358])).
% 1.52/0.61  fof(f328,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(X0,X1,X1) | ~v1_funct_2(X0,X1,X1) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_2(X1,X0))) )),
% 1.52/0.61    inference(resolution,[],[f70,f71])).
% 1.52/0.61  fof(f71,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f34])).
% 1.52/0.61  fof(f34,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(ennf_transformation,[],[f6])).
% 1.52/0.61  fof(f6,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.52/0.61  fof(f70,plain,(
% 1.52/0.61    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f33])).
% 1.52/0.61  fof(f33,plain,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.52/0.61    inference(flattening,[],[f32])).
% 1.52/0.61  fof(f32,plain,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f12])).
% 1.52/0.61  fof(f12,axiom,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.52/0.61  fof(f726,plain,(
% 1.52/0.61    ~spl3_70 | spl3_87),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f723])).
% 1.52/0.61  fof(f723,plain,(
% 1.52/0.61    $false | (~spl3_70 | spl3_87)),
% 1.52/0.61    inference(subsumption_resolution,[],[f635,f721])).
% 1.52/0.61  fof(f721,plain,(
% 1.52/0.61    ~v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0) | spl3_87),
% 1.52/0.61    inference(avatar_component_clause,[],[f719])).
% 1.52/0.61  fof(f635,plain,(
% 1.52/0.61    v5_relat_1(k2_funct_1(k2_funct_1(sK2)),sK0) | ~spl3_70),
% 1.52/0.61    inference(resolution,[],[f619,f73])).
% 1.52/0.61  fof(f619,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_70),
% 1.52/0.61    inference(avatar_component_clause,[],[f617])).
% 1.52/0.61  fof(f617,plain,(
% 1.52/0.61    spl3_70 <=> m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.52/0.61  fof(f713,plain,(
% 1.52/0.61    ~spl3_46 | ~spl3_48 | spl3_77),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f712])).
% 1.52/0.61  fof(f712,plain,(
% 1.52/0.61    $false | (~spl3_46 | ~spl3_48 | spl3_77)),
% 1.52/0.61    inference(subsumption_resolution,[],[f613,f670])).
% 1.52/0.61  fof(f670,plain,(
% 1.52/0.61    ~v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) | spl3_77),
% 1.52/0.61    inference(avatar_component_clause,[],[f668])).
% 1.52/0.61  fof(f668,plain,(
% 1.52/0.61    spl3_77 <=> v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 1.52/0.61  fof(f613,plain,(
% 1.52/0.61    v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) | (~spl3_46 | ~spl3_48)),
% 1.52/0.61    inference(superposition,[],[f447,f457])).
% 1.52/0.61  fof(f457,plain,(
% 1.52/0.61    k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2)) | ~spl3_48),
% 1.52/0.61    inference(avatar_component_clause,[],[f455])).
% 1.52/0.61  fof(f455,plain,(
% 1.52/0.61    spl3_48 <=> k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.52/0.61  fof(f447,plain,(
% 1.52/0.61    v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK2)),sK0,sK0) | ~spl3_46),
% 1.52/0.61    inference(avatar_component_clause,[],[f445])).
% 1.52/0.61  fof(f445,plain,(
% 1.52/0.61    spl3_46 <=> v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK2)),sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.52/0.61  fof(f711,plain,(
% 1.52/0.61    ~spl3_48 | ~spl3_49 | spl3_78),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f710])).
% 1.52/0.61  fof(f710,plain,(
% 1.52/0.61    $false | (~spl3_48 | ~spl3_49 | spl3_78)),
% 1.52/0.61    inference(subsumption_resolution,[],[f614,f674])).
% 1.52/0.61  fof(f674,plain,(
% 1.52/0.61    ~v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | spl3_78),
% 1.52/0.61    inference(avatar_component_clause,[],[f672])).
% 1.52/0.61  fof(f672,plain,(
% 1.52/0.61    spl3_78 <=> v1_funct_1(k2_funct_1(k2_funct_1(sK2)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 1.52/0.61  fof(f614,plain,(
% 1.52/0.61    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | (~spl3_48 | ~spl3_49)),
% 1.52/0.61    inference(superposition,[],[f462,f457])).
% 1.52/0.61  fof(f462,plain,(
% 1.52/0.61    v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK2))) | ~spl3_49),
% 1.52/0.61    inference(avatar_component_clause,[],[f460])).
% 1.52/0.61  fof(f460,plain,(
% 1.52/0.61    spl3_49 <=> v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK2)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 1.52/0.61  fof(f709,plain,(
% 1.52/0.61    spl3_85 | ~spl3_2 | ~spl3_70),
% 1.52/0.61    inference(avatar_split_clause,[],[f644,f617,f95,f706])).
% 1.52/0.61  fof(f95,plain,(
% 1.52/0.61    spl3_2 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.52/0.61  fof(f644,plain,(
% 1.52/0.61    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) | ~spl3_70),
% 1.52/0.61    inference(resolution,[],[f619,f57])).
% 1.52/0.61  fof(f57,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f21])).
% 1.52/0.61  fof(f21,plain,(
% 1.52/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.61    inference(ennf_transformation,[],[f1])).
% 1.52/0.61  fof(f1,axiom,(
% 1.52/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.52/0.61  fof(f680,plain,(
% 1.52/0.61    spl3_79 | ~spl3_77 | ~spl3_78 | ~spl3_70),
% 1.52/0.61    inference(avatar_split_clause,[],[f637,f617,f672,f668,f677])).
% 1.52/0.61  fof(f637,plain,(
% 1.52/0.61    ~v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) | v2_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0) | ~spl3_70),
% 1.52/0.61    inference(resolution,[],[f619,f75])).
% 1.52/0.61  fof(f630,plain,(
% 1.52/0.61    ~spl3_60 | ~spl3_38 | ~spl3_34 | ~spl3_26 | spl3_71 | ~spl3_64),
% 1.52/0.61    inference(avatar_split_clause,[],[f625,f558,f627,f271,f319,f358,f538])).
% 1.99/0.63  fof(f625,plain,(
% 1.99/0.63    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~spl3_64),
% 1.99/0.63    inference(superposition,[],[f70,f560])).
% 1.99/0.63  fof(f620,plain,(
% 1.99/0.63    ~spl3_44 | ~spl3_36 | ~spl3_33 | ~spl3_25 | spl3_70 | ~spl3_48),
% 1.99/0.63    inference(avatar_split_clause,[],[f615,f455,f617,f265,f313,f349,f435])).
% 1.99/0.63  fof(f349,plain,(
% 1.99/0.63    spl3_36 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.99/0.63  fof(f313,plain,(
% 1.99/0.63    spl3_33 <=> v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.99/0.63  fof(f265,plain,(
% 1.99/0.63    spl3_25 <=> v1_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.99/0.63  fof(f615,plain,(
% 1.99/0.63    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~spl3_48),
% 1.99/0.63    inference(superposition,[],[f70,f457])).
% 1.99/0.63  fof(f605,plain,(
% 1.99/0.63    ~spl3_38 | spl3_68),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f602])).
% 1.99/0.63  fof(f602,plain,(
% 1.99/0.63    $false | (~spl3_38 | spl3_68)),
% 1.99/0.63    inference(subsumption_resolution,[],[f505,f600])).
% 1.99/0.63  fof(f600,plain,(
% 1.99/0.63    ~v5_relat_1(k2_funct_1(sK1),sK0) | spl3_68),
% 1.99/0.63    inference(avatar_component_clause,[],[f598])).
% 1.99/0.63  fof(f505,plain,(
% 1.99/0.63    v5_relat_1(k2_funct_1(sK1),sK0) | ~spl3_38),
% 1.99/0.63    inference(resolution,[],[f360,f73])).
% 1.99/0.63  fof(f592,plain,(
% 1.99/0.63    spl3_27),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f574])).
% 1.99/0.63  fof(f574,plain,(
% 1.99/0.63    $false | spl3_27),
% 1.99/0.63    inference(unit_resulting_resolution,[],[f50,f44,f47,f53,f280,f80])).
% 1.99/0.63  fof(f80,plain,(
% 1.99/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f43])).
% 1.99/0.63  fof(f43,plain,(
% 1.99/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.99/0.63    inference(flattening,[],[f42])).
% 1.99/0.63  fof(f42,plain,(
% 1.99/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.99/0.63    inference(ennf_transformation,[],[f11])).
% 1.99/0.63  fof(f11,axiom,(
% 1.99/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.99/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.99/0.63  fof(f280,plain,(
% 1.99/0.63    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_27),
% 1.99/0.63    inference(avatar_component_clause,[],[f278])).
% 1.99/0.63  fof(f278,plain,(
% 1.99/0.63    spl3_27 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.99/0.63  fof(f53,plain,(
% 1.99/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f44,plain,(
% 1.99/0.63    v1_funct_1(sK2)),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f50,plain,(
% 1.99/0.63    v1_funct_1(sK1)),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f573,plain,(
% 1.99/0.63    ~spl3_14 | ~spl3_24 | spl3_60),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f572])).
% 1.99/0.63  fof(f572,plain,(
% 1.99/0.63    $false | (~spl3_14 | ~spl3_24 | spl3_60)),
% 1.99/0.63    inference(subsumption_resolution,[],[f258,f540])).
% 1.99/0.63  fof(f540,plain,(
% 1.99/0.63    ~v1_funct_1(k2_funct_1(sK1)) | spl3_60),
% 1.99/0.63    inference(avatar_component_clause,[],[f538])).
% 1.99/0.63  fof(f258,plain,(
% 1.99/0.63    v1_funct_1(k2_funct_1(sK1)) | (~spl3_14 | ~spl3_24)),
% 1.99/0.63    inference(superposition,[],[f193,f255])).
% 1.99/0.63  fof(f193,plain,(
% 1.99/0.63    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl3_14),
% 1.99/0.63    inference(avatar_component_clause,[],[f191])).
% 1.99/0.63  fof(f191,plain,(
% 1.99/0.63    spl3_14 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.99/0.63  fof(f571,plain,(
% 1.99/0.63    spl3_66 | ~spl3_2 | ~spl3_38),
% 1.99/0.63    inference(avatar_split_clause,[],[f514,f358,f95,f568])).
% 1.99/0.63  fof(f514,plain,(
% 1.99/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(k2_funct_1(sK1)) | ~spl3_38),
% 1.99/0.63    inference(resolution,[],[f360,f57])).
% 1.99/0.63  fof(f566,plain,(
% 1.99/0.63    spl3_65 | ~spl3_60 | ~spl3_34 | ~spl3_26 | ~spl3_38),
% 1.99/0.63    inference(avatar_split_clause,[],[f513,f358,f271,f319,f538,f563])).
% 1.99/0.63  fof(f513,plain,(
% 1.99/0.63    ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1))) | ~spl3_38),
% 1.99/0.63    inference(resolution,[],[f360,f67])).
% 1.99/0.63  fof(f67,plain,(
% 1.99/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 1.99/0.63    inference(cnf_transformation,[],[f33])).
% 1.99/0.63  fof(f561,plain,(
% 1.99/0.63    spl3_64 | ~spl3_60 | ~spl3_34 | ~spl3_26 | ~spl3_38),
% 1.99/0.63    inference(avatar_split_clause,[],[f512,f358,f271,f319,f538,f558])).
% 1.99/0.63  fof(f512,plain,(
% 1.99/0.63    ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1)) | ~spl3_38),
% 1.99/0.63    inference(resolution,[],[f360,f66])).
% 1.99/0.63  fof(f66,plain,(
% 1.99/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f31])).
% 1.99/0.63  fof(f31,plain,(
% 1.99/0.63    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.99/0.63    inference(flattening,[],[f30])).
% 1.99/0.63  fof(f30,plain,(
% 1.99/0.63    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.99/0.63    inference(ennf_transformation,[],[f15])).
% 1.99/0.63  fof(f15,axiom,(
% 1.99/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.99/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.99/0.63  fof(f551,plain,(
% 1.99/0.63    spl3_62 | ~spl3_60 | ~spl3_34 | ~spl3_26 | ~spl3_38),
% 1.99/0.63    inference(avatar_split_clause,[],[f510,f358,f271,f319,f538,f548])).
% 1.99/0.63  fof(f510,plain,(
% 1.99/0.63    ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0) | ~spl3_38),
% 1.99/0.63    inference(resolution,[],[f360,f69])).
% 1.99/0.63  fof(f69,plain,(
% 1.99/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | v3_funct_2(k2_funct_2(X0,X1),X0,X0)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f33])).
% 1.99/0.63  fof(f546,plain,(
% 1.99/0.63    spl3_61 | ~spl3_34 | ~spl3_60 | ~spl3_38),
% 1.99/0.63    inference(avatar_split_clause,[],[f507,f358,f538,f319,f543])).
% 1.99/0.63  fof(f507,plain,(
% 1.99/0.63    ~v1_funct_1(k2_funct_1(sK1)) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | v2_funct_2(k2_funct_1(sK1),sK0) | ~spl3_38),
% 1.99/0.63    inference(resolution,[],[f360,f75])).
% 1.99/0.63  fof(f541,plain,(
% 1.99/0.63    spl3_59 | ~spl3_34 | ~spl3_60 | ~spl3_38),
% 1.99/0.63    inference(avatar_split_clause,[],[f506,f358,f538,f319,f534])).
% 1.99/0.63  fof(f506,plain,(
% 1.99/0.63    ~v1_funct_1(k2_funct_1(sK1)) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | v2_funct_1(k2_funct_1(sK1)) | ~spl3_38),
% 1.99/0.63    inference(resolution,[],[f360,f74])).
% 1.99/0.63  fof(f74,plain,(
% 1.99/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f37])).
% 1.99/0.63  fof(f486,plain,(
% 1.99/0.63    ~spl3_36 | spl3_52),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f483])).
% 1.99/0.63  fof(f483,plain,(
% 1.99/0.63    $false | (~spl3_36 | spl3_52)),
% 1.99/0.63    inference(subsumption_resolution,[],[f402,f481])).
% 1.99/0.63  fof(f481,plain,(
% 1.99/0.63    ~v5_relat_1(k2_funct_1(sK2),sK0) | spl3_52),
% 1.99/0.63    inference(avatar_component_clause,[],[f479])).
% 1.99/0.63  fof(f402,plain,(
% 1.99/0.63    v5_relat_1(k2_funct_1(sK2),sK0) | ~spl3_36),
% 1.99/0.63    inference(resolution,[],[f351,f73])).
% 1.99/0.63  fof(f351,plain,(
% 1.99/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_36),
% 1.99/0.63    inference(avatar_component_clause,[],[f349])).
% 1.99/0.63  fof(f470,plain,(
% 1.99/0.63    ~spl3_12 | ~spl3_23 | spl3_44),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f469])).
% 1.99/0.63  fof(f469,plain,(
% 1.99/0.63    $false | (~spl3_12 | ~spl3_23 | spl3_44)),
% 1.99/0.63    inference(subsumption_resolution,[],[f257,f437])).
% 1.99/0.63  fof(f437,plain,(
% 1.99/0.63    ~v1_funct_1(k2_funct_1(sK2)) | spl3_44),
% 1.99/0.63    inference(avatar_component_clause,[],[f435])).
% 1.99/0.63  fof(f257,plain,(
% 1.99/0.63    v1_funct_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_23)),
% 1.99/0.63    inference(superposition,[],[f184,f250])).
% 1.99/0.63  fof(f250,plain,(
% 1.99/0.63    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~spl3_23),
% 1.99/0.63    inference(avatar_component_clause,[],[f248])).
% 1.99/0.63  fof(f248,plain,(
% 1.99/0.63    spl3_23 <=> k2_funct_1(sK2) = k2_funct_2(sK0,sK2)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.99/0.63  fof(f184,plain,(
% 1.99/0.63    v1_funct_1(k2_funct_2(sK0,sK2)) | ~spl3_12),
% 1.99/0.63    inference(avatar_component_clause,[],[f182])).
% 1.99/0.63  fof(f182,plain,(
% 1.99/0.63    spl3_12 <=> v1_funct_1(k2_funct_2(sK0,sK2))),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.99/0.63  fof(f468,plain,(
% 1.99/0.63    spl3_50 | ~spl3_2 | ~spl3_36),
% 1.99/0.63    inference(avatar_split_clause,[],[f411,f349,f95,f465])).
% 1.99/0.63  fof(f411,plain,(
% 1.99/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_36),
% 1.99/0.63    inference(resolution,[],[f351,f57])).
% 1.99/0.63  fof(f463,plain,(
% 1.99/0.63    spl3_49 | ~spl3_44 | ~spl3_33 | ~spl3_25 | ~spl3_36),
% 1.99/0.63    inference(avatar_split_clause,[],[f410,f349,f265,f313,f435,f460])).
% 1.99/0.63  fof(f410,plain,(
% 1.99/0.63    ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK2))) | ~spl3_36),
% 1.99/0.63    inference(resolution,[],[f351,f67])).
% 1.99/0.63  fof(f458,plain,(
% 1.99/0.63    spl3_48 | ~spl3_44 | ~spl3_33 | ~spl3_25 | ~spl3_36),
% 1.99/0.63    inference(avatar_split_clause,[],[f409,f349,f265,f313,f435,f455])).
% 1.99/0.63  fof(f409,plain,(
% 1.99/0.63    ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2)) | ~spl3_36),
% 1.99/0.63    inference(resolution,[],[f351,f66])).
% 1.99/0.63  fof(f448,plain,(
% 1.99/0.63    spl3_46 | ~spl3_44 | ~spl3_33 | ~spl3_25 | ~spl3_36),
% 1.99/0.63    inference(avatar_split_clause,[],[f407,f349,f265,f313,f435,f445])).
% 1.99/0.63  fof(f407,plain,(
% 1.99/0.63    ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK2)),sK0,sK0) | ~spl3_36),
% 1.99/0.63    inference(resolution,[],[f351,f69])).
% 1.99/0.63  fof(f443,plain,(
% 1.99/0.63    spl3_45 | ~spl3_33 | ~spl3_44 | ~spl3_36),
% 1.99/0.63    inference(avatar_split_clause,[],[f404,f349,f435,f313,f440])).
% 1.99/0.63  fof(f404,plain,(
% 1.99/0.63    ~v1_funct_1(k2_funct_1(sK2)) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | v2_funct_2(k2_funct_1(sK2),sK0) | ~spl3_36),
% 1.99/0.63    inference(resolution,[],[f351,f75])).
% 1.99/0.63  fof(f438,plain,(
% 1.99/0.63    spl3_43 | ~spl3_33 | ~spl3_44 | ~spl3_36),
% 1.99/0.63    inference(avatar_split_clause,[],[f403,f349,f435,f313,f431])).
% 1.99/0.63  fof(f403,plain,(
% 1.99/0.63    ~v1_funct_1(k2_funct_1(sK2)) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | v2_funct_1(k2_funct_1(sK2)) | ~spl3_36),
% 1.99/0.63    inference(resolution,[],[f351,f74])).
% 1.99/0.63  fof(f381,plain,(
% 1.99/0.63    spl3_37),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f380])).
% 1.99/0.63  fof(f380,plain,(
% 1.99/0.63    $false | spl3_37),
% 1.99/0.63    inference(subsumption_resolution,[],[f53,f356])).
% 1.99/0.63  fof(f356,plain,(
% 1.99/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_37),
% 1.99/0.63    inference(avatar_component_clause,[],[f354])).
% 1.99/0.63  fof(f363,plain,(
% 1.99/0.63    spl3_35),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f362])).
% 1.99/0.63  fof(f362,plain,(
% 1.99/0.63    $false | spl3_35),
% 1.99/0.63    inference(subsumption_resolution,[],[f47,f347])).
% 1.99/0.63  fof(f347,plain,(
% 1.99/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_35),
% 1.99/0.63    inference(avatar_component_clause,[],[f345])).
% 1.99/0.63  fof(f361,plain,(
% 1.99/0.63    ~spl3_9 | ~spl3_37 | ~spl3_8 | ~spl3_15 | spl3_38 | ~spl3_24),
% 1.99/0.63    inference(avatar_split_clause,[],[f343,f253,f358,f195,f149,f354,f153])).
% 1.99/0.63  fof(f149,plain,(
% 1.99/0.63    spl3_8 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.99/0.63  fof(f195,plain,(
% 1.99/0.63    spl3_15 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.99/0.63  fof(f343,plain,(
% 1.99/0.63    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl3_24),
% 1.99/0.63    inference(superposition,[],[f70,f255])).
% 1.99/0.63  fof(f352,plain,(
% 1.99/0.63    ~spl3_6 | ~spl3_35 | ~spl3_5 | ~spl3_13 | spl3_36 | ~spl3_23),
% 1.99/0.63    inference(avatar_split_clause,[],[f342,f248,f349,f186,f136,f345,f140])).
% 1.99/0.63  fof(f136,plain,(
% 1.99/0.63    spl3_5 <=> v3_funct_2(sK2,sK0,sK0)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.99/0.63  fof(f186,plain,(
% 1.99/0.63    spl3_13 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.99/0.63  fof(f342,plain,(
% 1.99/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~spl3_23),
% 1.99/0.63    inference(superposition,[],[f70,f250])).
% 1.99/0.63  fof(f322,plain,(
% 1.99/0.63    ~spl3_9 | ~spl3_8 | ~spl3_15 | spl3_34 | ~spl3_24),
% 1.99/0.63    inference(avatar_split_clause,[],[f317,f253,f319,f195,f149,f153])).
% 1.99/0.63  fof(f317,plain,(
% 1.99/0.63    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_24),
% 1.99/0.63    inference(forward_demodulation,[],[f309,f255])).
% 1.99/0.63  fof(f309,plain,(
% 1.99/0.63    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 1.99/0.63    inference(resolution,[],[f69,f53])).
% 1.99/0.63  fof(f316,plain,(
% 1.99/0.63    ~spl3_6 | ~spl3_5 | ~spl3_13 | spl3_33 | ~spl3_23),
% 1.99/0.63    inference(avatar_split_clause,[],[f311,f248,f313,f186,f136,f140])).
% 1.99/0.63  fof(f311,plain,(
% 1.99/0.63    v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~spl3_23),
% 1.99/0.63    inference(forward_demodulation,[],[f308,f250])).
% 1.99/0.63  fof(f308,plain,(
% 1.99/0.63    ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 1.99/0.63    inference(resolution,[],[f69,f47])).
% 1.99/0.63  fof(f285,plain,(
% 1.99/0.63    ~spl3_27 | spl3_28),
% 1.99/0.63    inference(avatar_split_clause,[],[f275,f282,f278])).
% 1.99/0.63  fof(f275,plain,(
% 1.99/0.63    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.99/0.63    inference(resolution,[],[f205,f81])).
% 1.99/0.63  fof(f81,plain,(
% 1.99/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.99/0.63    inference(definition_unfolding,[],[f48,f54])).
% 1.99/0.63  fof(f54,plain,(
% 1.99/0.63    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f16])).
% 1.99/0.63  fof(f16,axiom,(
% 1.99/0.63    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.99/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.99/0.63  fof(f48,plain,(
% 1.99/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f205,plain,(
% 1.99/0.63    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_relat_1(X3)) | k6_relat_1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.99/0.63    inference(resolution,[],[f77,f82])).
% 1.99/0.63  fof(f82,plain,(
% 1.99/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.99/0.63    inference(definition_unfolding,[],[f56,f54])).
% 1.99/0.63  fof(f56,plain,(
% 1.99/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.99/0.63    inference(cnf_transformation,[],[f13])).
% 1.99/0.63  fof(f13,axiom,(
% 1.99/0.63    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.99/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.99/0.63  fof(f77,plain,(
% 1.99/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f39])).
% 1.99/0.63  fof(f274,plain,(
% 1.99/0.63    ~spl3_9 | ~spl3_8 | ~spl3_15 | spl3_26 | ~spl3_24),
% 1.99/0.63    inference(avatar_split_clause,[],[f269,f253,f271,f195,f149,f153])).
% 1.99/0.63  fof(f269,plain,(
% 1.99/0.63    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_24),
% 1.99/0.63    inference(forward_demodulation,[],[f261,f255])).
% 1.99/0.63  fof(f261,plain,(
% 1.99/0.63    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 1.99/0.63    inference(resolution,[],[f68,f53])).
% 1.99/0.63  fof(f68,plain,(
% 1.99/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | v1_funct_2(k2_funct_2(X0,X1),X0,X0)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f33])).
% 1.99/0.63  fof(f268,plain,(
% 1.99/0.63    ~spl3_6 | ~spl3_5 | ~spl3_13 | spl3_25 | ~spl3_23),
% 1.99/0.63    inference(avatar_split_clause,[],[f263,f248,f265,f186,f136,f140])).
% 1.99/0.63  fof(f263,plain,(
% 1.99/0.63    v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~spl3_23),
% 1.99/0.63    inference(forward_demodulation,[],[f260,f250])).
% 1.99/0.63  fof(f260,plain,(
% 1.99/0.63    ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 1.99/0.63    inference(resolution,[],[f68,f47])).
% 1.99/0.63  fof(f256,plain,(
% 1.99/0.63    spl3_24 | ~spl3_9 | ~spl3_8 | ~spl3_15),
% 1.99/0.63    inference(avatar_split_clause,[],[f245,f195,f149,f153,f253])).
% 1.99/0.63  fof(f245,plain,(
% 1.99/0.63    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.99/0.63    inference(resolution,[],[f66,f53])).
% 1.99/0.63  fof(f251,plain,(
% 1.99/0.63    spl3_23 | ~spl3_6 | ~spl3_5 | ~spl3_13),
% 1.99/0.63    inference(avatar_split_clause,[],[f244,f186,f136,f140,f248])).
% 1.99/0.63  fof(f244,plain,(
% 1.99/0.63    ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k2_funct_2(sK0,sK2)),
% 1.99/0.63    inference(resolution,[],[f66,f47])).
% 1.99/0.63  fof(f202,plain,(
% 1.99/0.63    spl3_15),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f201])).
% 1.99/0.63  fof(f201,plain,(
% 1.99/0.63    $false | spl3_15),
% 1.99/0.63    inference(subsumption_resolution,[],[f51,f197])).
% 1.99/0.63  fof(f197,plain,(
% 1.99/0.63    ~v1_funct_2(sK1,sK0,sK0) | spl3_15),
% 1.99/0.63    inference(avatar_component_clause,[],[f195])).
% 1.99/0.63  fof(f51,plain,(
% 1.99/0.63    v1_funct_2(sK1,sK0,sK0)),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f200,plain,(
% 1.99/0.63    spl3_13),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f199])).
% 1.99/0.63  fof(f199,plain,(
% 1.99/0.63    $false | spl3_13),
% 1.99/0.63    inference(subsumption_resolution,[],[f45,f188])).
% 1.99/0.63  fof(f188,plain,(
% 1.99/0.63    ~v1_funct_2(sK2,sK0,sK0) | spl3_13),
% 1.99/0.63    inference(avatar_component_clause,[],[f186])).
% 1.99/0.63  fof(f45,plain,(
% 1.99/0.63    v1_funct_2(sK2,sK0,sK0)),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f198,plain,(
% 1.99/0.63    spl3_14 | ~spl3_9 | ~spl3_8 | ~spl3_15),
% 1.99/0.63    inference(avatar_split_clause,[],[f179,f195,f149,f153,f191])).
% 1.99/0.63  fof(f179,plain,(
% 1.99/0.63    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.99/0.63    inference(resolution,[],[f67,f53])).
% 1.99/0.63  fof(f189,plain,(
% 1.99/0.63    spl3_12 | ~spl3_6 | ~spl3_5 | ~spl3_13),
% 1.99/0.63    inference(avatar_split_clause,[],[f178,f186,f136,f140,f182])).
% 1.99/0.63  fof(f178,plain,(
% 1.99/0.63    ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_2(sK0,sK2))),
% 1.99/0.63    inference(resolution,[],[f67,f47])).
% 1.99/0.63  fof(f177,plain,(
% 1.99/0.63    spl3_8),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f176])).
% 1.99/0.63  fof(f176,plain,(
% 1.99/0.63    $false | spl3_8),
% 1.99/0.63    inference(subsumption_resolution,[],[f52,f151])).
% 1.99/0.63  fof(f151,plain,(
% 1.99/0.63    ~v3_funct_2(sK1,sK0,sK0) | spl3_8),
% 1.99/0.63    inference(avatar_component_clause,[],[f149])).
% 1.99/0.63  fof(f52,plain,(
% 1.99/0.63    v3_funct_2(sK1,sK0,sK0)),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f162,plain,(
% 1.99/0.63    spl3_6),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f161])).
% 1.99/0.63  fof(f161,plain,(
% 1.99/0.63    $false | spl3_6),
% 1.99/0.63    inference(subsumption_resolution,[],[f44,f142])).
% 1.99/0.63  fof(f142,plain,(
% 1.99/0.63    ~v1_funct_1(sK2) | spl3_6),
% 1.99/0.63    inference(avatar_component_clause,[],[f140])).
% 1.99/0.63  fof(f160,plain,(
% 1.99/0.63    spl3_5),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f159])).
% 1.99/0.63  fof(f159,plain,(
% 1.99/0.63    $false | spl3_5),
% 1.99/0.63    inference(subsumption_resolution,[],[f46,f138])).
% 1.99/0.63  fof(f138,plain,(
% 1.99/0.63    ~v3_funct_2(sK2,sK0,sK0) | spl3_5),
% 1.99/0.63    inference(avatar_component_clause,[],[f136])).
% 1.99/0.63  fof(f46,plain,(
% 1.99/0.63    v3_funct_2(sK2,sK0,sK0)),
% 1.99/0.63    inference(cnf_transformation,[],[f20])).
% 1.99/0.63  fof(f158,plain,(
% 1.99/0.63    spl3_9),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f157])).
% 1.99/0.63  fof(f157,plain,(
% 1.99/0.63    $false | spl3_9),
% 1.99/0.63    inference(subsumption_resolution,[],[f50,f155])).
% 1.99/0.63  fof(f155,plain,(
% 1.99/0.63    ~v1_funct_1(sK1) | spl3_9),
% 1.99/0.63    inference(avatar_component_clause,[],[f153])).
% 1.99/0.63  fof(f156,plain,(
% 1.99/0.63    spl3_7 | ~spl3_8 | ~spl3_9),
% 1.99/0.63    inference(avatar_split_clause,[],[f129,f153,f149,f145])).
% 1.99/0.63  fof(f129,plain,(
% 1.99/0.63    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_1(sK1)),
% 1.99/0.63    inference(resolution,[],[f74,f53])).
% 1.99/0.63  fof(f143,plain,(
% 1.99/0.63    spl3_4 | ~spl3_5 | ~spl3_6),
% 1.99/0.63    inference(avatar_split_clause,[],[f128,f140,f136,f132])).
% 1.99/0.63  fof(f128,plain,(
% 1.99/0.63    ~v1_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | v2_funct_1(sK2)),
% 1.99/0.63    inference(resolution,[],[f74,f47])).
% 1.99/0.63  fof(f107,plain,(
% 1.99/0.63    spl3_2),
% 1.99/0.63    inference(avatar_contradiction_clause,[],[f104])).
% 1.99/0.63  fof(f104,plain,(
% 1.99/0.63    $false | spl3_2),
% 1.99/0.63    inference(unit_resulting_resolution,[],[f63,f97])).
% 1.99/0.63  fof(f97,plain,(
% 1.99/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_2),
% 1.99/0.63    inference(avatar_component_clause,[],[f95])).
% 1.99/0.63  fof(f63,plain,(
% 1.99/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.99/0.63    inference(cnf_transformation,[],[f2])).
% 1.99/0.63  fof(f2,axiom,(
% 1.99/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.99/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.99/0.63  fof(f103,plain,(
% 1.99/0.63    spl3_3 | ~spl3_2),
% 1.99/0.63    inference(avatar_split_clause,[],[f88,f95,f100])).
% 1.99/0.63  fof(f88,plain,(
% 1.99/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1)),
% 1.99/0.63    inference(resolution,[],[f57,f53])).
% 1.99/0.63  fof(f98,plain,(
% 1.99/0.63    spl3_1 | ~spl3_2),
% 1.99/0.63    inference(avatar_split_clause,[],[f87,f95,f91])).
% 1.99/0.63  fof(f87,plain,(
% 1.99/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK2)),
% 1.99/0.63    inference(resolution,[],[f57,f47])).
% 1.99/0.63  % SZS output end Proof for theBenchmark
% 1.99/0.63  % (12233)------------------------------
% 1.99/0.63  % (12233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.63  % (12233)Termination reason: Refutation
% 1.99/0.63  
% 1.99/0.63  % (12233)Memory used [KB]: 7036
% 1.99/0.63  % (12233)Time elapsed: 0.206 s
% 1.99/0.63  % (12233)------------------------------
% 1.99/0.63  % (12233)------------------------------
% 1.99/0.63  % (12219)Success in time 0.263 s
%------------------------------------------------------------------------------
