%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:41 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 459 expanded)
%              Number of leaves         :   55 ( 217 expanded)
%              Depth                    :   10
%              Number of atoms          :  738 (1973 expanded)
%              Number of equality atoms :   98 ( 169 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f770,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f107,f112,f117,f122,f127,f141,f155,f160,f165,f175,f180,f185,f195,f200,f207,f257,f267,f296,f319,f325,f328,f329,f367,f372,f382,f387,f403,f408,f472,f492,f534,f618,f655,f722,f740,f745,f766,f769])).

fof(f769,plain,
    ( ~ spl3_83
    | spl3_75
    | ~ spl3_82
    | ~ spl3_70
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f768,f763,f532,f737,f652,f742])).

fof(f742,plain,
    ( spl3_83
  <=> v5_relat_1(k2_funct_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f652,plain,
    ( spl3_75
  <=> sK1 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f737,plain,
    ( spl3_82
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f532,plain,
    ( spl3_70
  <=> ! [X1] :
        ( sK1 = X1
        | ~ v1_relat_1(X1)
        | k1_xboole_0 != k2_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f763,plain,
    ( spl3_87
  <=> v2_funct_2(k2_funct_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f768,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(sK1)
    | ~ v5_relat_1(k2_funct_1(sK1),k1_xboole_0)
    | ~ spl3_70
    | ~ spl3_87 ),
    inference(trivial_inequality_removal,[],[f767])).

fof(f767,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(sK1)
    | k1_xboole_0 != k1_xboole_0
    | ~ v5_relat_1(k2_funct_1(sK1),k1_xboole_0)
    | ~ spl3_70
    | ~ spl3_87 ),
    inference(resolution,[],[f765,f538])).

fof(f538,plain,
    ( ! [X2,X1] :
        ( ~ v2_funct_2(X1,X2)
        | ~ v1_relat_1(X1)
        | sK1 = X1
        | k1_xboole_0 != X2
        | ~ v5_relat_1(X1,X2) )
    | ~ spl3_70 ),
    inference(duplicate_literal_removal,[],[f536])).

fof(f536,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X2
        | ~ v1_relat_1(X1)
        | sK1 = X1
        | ~ v2_funct_2(X1,X2)
        | ~ v5_relat_1(X1,X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_70 ),
    inference(superposition,[],[f533,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f533,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_relat_1(X1)
        | ~ v1_relat_1(X1)
        | sK1 = X1 )
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f532])).

fof(f765,plain,
    ( v2_funct_2(k2_funct_1(sK1),k1_xboole_0)
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f763])).

fof(f766,plain,
    ( spl3_87
    | ~ spl3_31
    | ~ spl3_60
    | ~ spl3_81 ),
    inference(avatar_split_clause,[],[f730,f719,f469,f264,f763])).

fof(f264,plain,
    ( spl3_31
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f469,plain,
    ( spl3_60
  <=> v3_funct_2(k2_funct_1(sK1),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f719,plain,
    ( spl3_81
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f730,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_2(k2_funct_1(sK1),k1_xboole_0)
    | ~ spl3_81 ),
    inference(resolution,[],[f721,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f721,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f719])).

fof(f745,plain,
    ( spl3_83
    | ~ spl3_81 ),
    inference(avatar_split_clause,[],[f731,f719,f742])).

fof(f731,plain,
    ( v5_relat_1(k2_funct_1(sK1),k1_xboole_0)
    | ~ spl3_81 ),
    inference(resolution,[],[f721,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f740,plain,
    ( spl3_82
    | ~ spl3_81 ),
    inference(avatar_split_clause,[],[f732,f719,f737])).

fof(f732,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_81 ),
    inference(resolution,[],[f721,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f722,plain,
    ( ~ spl3_1
    | ~ spl3_44
    | ~ spl3_48
    | ~ spl3_51
    | spl3_81
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f495,f489,f719,f400,f384,f364,f84])).

fof(f84,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f364,plain,
    ( spl3_44
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f384,plain,
    ( spl3_48
  <=> v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f400,plain,
    ( spl3_51
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f489,plain,
    ( spl3_64
  <=> k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f495,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_64 ),
    inference(superposition,[],[f68,f491])).

fof(f491,plain,
    ( k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1)
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f489])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f655,plain,
    ( ~ spl3_75
    | ~ spl3_23
    | spl3_40 ),
    inference(avatar_split_clause,[],[f637,f312,f217,f652])).

fof(f217,plain,
    ( spl3_23
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f312,plain,
    ( spl3_40
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f637,plain,
    ( sK1 != k2_funct_1(sK1)
    | ~ spl3_23
    | spl3_40 ),
    inference(backward_demodulation,[],[f313,f219])).

fof(f219,plain,
    ( sK1 = sK2
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f313,plain,
    ( sK2 != k2_funct_1(sK1)
    | spl3_40 ),
    inference(avatar_component_clause,[],[f312])).

fof(f618,plain,
    ( ~ spl3_45
    | spl3_23
    | ~ spl3_11
    | ~ spl3_47
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f616,f532,f379,f152,f217,f369])).

fof(f369,plain,
    ( spl3_45
  <=> v5_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f152,plain,
    ( spl3_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f379,plain,
    ( spl3_47
  <=> v2_funct_2(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f616,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = sK2
    | ~ v5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_47
    | ~ spl3_70 ),
    inference(trivial_inequality_removal,[],[f615])).

fof(f615,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = sK2
    | k1_xboole_0 != k1_xboole_0
    | ~ v5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_47
    | ~ spl3_70 ),
    inference(resolution,[],[f538,f381])).

fof(f381,plain,
    ( v2_funct_2(sK2,k1_xboole_0)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f379])).

fof(f534,plain,
    ( ~ spl3_10
    | spl3_70
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f413,f405,f532,f138])).

fof(f138,plain,
    ( spl3_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f405,plain,
    ( spl3_52
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f413,plain,
    ( ! [X1] :
        ( sK1 = X1
        | k1_xboole_0 != k2_relat_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_52 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_xboole_0
        | sK1 = X1
        | k1_xboole_0 != k2_relat_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_52 ),
    inference(superposition,[],[f59,f407])).

fof(f407,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f405])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_relat_1(X1)
      | X0 = X1
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k2_relat_1(X0) = k1_xboole_0 )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

fof(f492,plain,
    ( spl3_64
    | ~ spl3_30
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f349,f316,f254,f489])).

fof(f254,plain,
    ( spl3_30
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f316,plain,
    ( spl3_41
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f349,plain,
    ( k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1)
    | ~ spl3_30
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f256,f318])).

fof(f318,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f316])).

fof(f256,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f254])).

fof(f472,plain,
    ( spl3_60
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f353,f316,f293,f469])).

fof(f293,plain,
    ( spl3_36
  <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f353,plain,
    ( v3_funct_2(k2_funct_1(sK1),k1_xboole_0,k1_xboole_0)
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f295,f318])).

fof(f295,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f293])).

fof(f408,plain,
    ( spl3_52
    | ~ spl3_41
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f388,f322,f316,f405])).

fof(f322,plain,
    ( spl3_42
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f388,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_41
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f323,f318])).

fof(f323,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f322])).

fof(f403,plain,
    ( spl3_51
    | ~ spl3_7
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f334,f316,f114,f400])).

fof(f114,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f334,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_7
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f116,f318])).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f387,plain,
    ( spl3_48
    | ~ spl3_4
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f331,f316,f99,f384])).

fof(f99,plain,
    ( spl3_4
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f331,plain,
    ( v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f101,f318])).

fof(f101,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f382,plain,
    ( spl3_47
    | ~ spl3_20
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f344,f316,f197,f379])).

fof(f197,plain,
    ( spl3_20
  <=> v2_funct_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f344,plain,
    ( v2_funct_2(sK2,k1_xboole_0)
    | ~ spl3_20
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f199,f318])).

fof(f199,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f372,plain,
    ( spl3_45
    | ~ spl3_13
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f339,f316,f162,f369])).

fof(f162,plain,
    ( spl3_13
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f339,plain,
    ( v5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f164,f318])).

fof(f164,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f367,plain,
    ( spl3_44
    | ~ spl3_3
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f330,f316,f94,f364])).

fof(f94,plain,
    ( spl3_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f330,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f96,f318])).

fof(f96,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f329,plain,
    ( sK2 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f328,plain,
    ( ~ spl3_10
    | ~ spl3_12
    | ~ spl3_19
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_19
    | spl3_42 ),
    inference(unit_resulting_resolution,[],[f140,f159,f194,f324,f62])).

fof(f324,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl3_42 ),
    inference(avatar_component_clause,[],[f322])).

fof(f194,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_19
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f159,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_12
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f140,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f325,plain,
    ( ~ spl3_7
    | ~ spl3_42
    | spl3_39 ),
    inference(avatar_split_clause,[],[f320,f308,f322,f114])).

fof(f308,plain,
    ( spl3_39
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f320,plain,
    ( sK0 != k2_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_39 ),
    inference(superposition,[],[f310,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f310,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl3_39 ),
    inference(avatar_component_clause,[],[f308])).

fof(f319,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_39
    | spl3_40
    | ~ spl3_16
    | spl3_41
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f202,f182,f316,f177,f312,f308,f119,f104,f89,f114,f94,f84])).

fof(f89,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f104,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f177,plain,
    ( spl3_16
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f182,plain,
    ( spl3_17
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_17 ),
    inference(resolution,[],[f184,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = X3
      | k2_relset_1(X0,X1,X2) != X1
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
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
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
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f184,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f296,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | spl3_36
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f261,f254,f293,f114,f99,f94,f84])).

fof(f261,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_30 ),
    inference(superposition,[],[f67,f256])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f267,plain,
    ( spl3_31
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f258,f254,f204,f264])).

fof(f204,plain,
    ( spl3_21
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f258,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f206,f256])).

fof(f206,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f204])).

fof(f257,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_30
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f129,f114,f254,f99,f94,f84])).

fof(f129,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f116,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f207,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_21
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f128,f114,f204,f99,f94,f84])).

fof(f128,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f116,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f200,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f147,f119,f109,f89,f197])).

fof(f109,plain,
    ( spl3_6
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f147,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f121,f74])).

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f195,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f133,f114,f99,f84,f192])).

fof(f133,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f116,f74])).

fof(f185,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f53,f182])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
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
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f180,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f132,f114,f99,f84,f177])).

fof(f132,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f116,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f175,plain,
    ( spl3_15
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f145,f119,f172])).

fof(f172,plain,
    ( spl3_15
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f145,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f121,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

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

fof(f165,plain,
    ( spl3_13
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f148,f119,f162])).

fof(f148,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f121,f71])).

fof(f160,plain,
    ( spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f134,f114,f157])).

fof(f134,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f116,f71])).

fof(f155,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f149,f119,f152])).

fof(f149,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f121,f69])).

fof(f141,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f135,f114,f138])).

fof(f135,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f116,f69])).

fof(f127,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f54,f124])).

fof(f124,plain,
    ( spl3_9
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f54,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f114])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f112,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f51,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f104])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f47,f99])).

fof(f47,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f49,f89])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:30:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (20219)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (20223)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (20227)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (20217)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (20224)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (20243)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (20237)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (20234)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (20216)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (20214)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (20229)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (20240)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (20226)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (20213)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (20221)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (20238)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (20242)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (20232)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (20225)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (20215)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (20241)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (20239)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (20230)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (20233)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (20230)Refutation not found, incomplete strategy% (20230)------------------------------
% 0.22/0.55  % (20230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20230)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20230)Memory used [KB]: 10746
% 0.22/0.55  % (20230)Time elapsed: 0.130 s
% 0.22/0.55  % (20230)------------------------------
% 0.22/0.55  % (20230)------------------------------
% 0.22/0.55  % (20231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (20222)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.56  % (20220)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.57  % (20235)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.57  % (20236)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.44/0.58  % (20228)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.63/0.58  % (20224)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f770,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f107,f112,f117,f122,f127,f141,f155,f160,f165,f175,f180,f185,f195,f200,f207,f257,f267,f296,f319,f325,f328,f329,f367,f372,f382,f387,f403,f408,f472,f492,f534,f618,f655,f722,f740,f745,f766,f769])).
% 1.63/0.58  fof(f769,plain,(
% 1.63/0.58    ~spl3_83 | spl3_75 | ~spl3_82 | ~spl3_70 | ~spl3_87),
% 1.63/0.58    inference(avatar_split_clause,[],[f768,f763,f532,f737,f652,f742])).
% 1.63/0.58  fof(f742,plain,(
% 1.63/0.58    spl3_83 <=> v5_relat_1(k2_funct_1(sK1),k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 1.63/0.58  fof(f652,plain,(
% 1.63/0.58    spl3_75 <=> sK1 = k2_funct_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 1.63/0.58  fof(f737,plain,(
% 1.63/0.58    spl3_82 <=> v1_relat_1(k2_funct_1(sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 1.63/0.58  fof(f532,plain,(
% 1.63/0.58    spl3_70 <=> ! [X1] : (sK1 = X1 | ~v1_relat_1(X1) | k1_xboole_0 != k2_relat_1(X1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.63/0.58  fof(f763,plain,(
% 1.63/0.58    spl3_87 <=> v2_funct_2(k2_funct_1(sK1),k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 1.63/0.58  fof(f768,plain,(
% 1.63/0.58    ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(sK1) | ~v5_relat_1(k2_funct_1(sK1),k1_xboole_0) | (~spl3_70 | ~spl3_87)),
% 1.63/0.58    inference(trivial_inequality_removal,[],[f767])).
% 1.63/0.58  fof(f767,plain,(
% 1.63/0.58    ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(sK1) | k1_xboole_0 != k1_xboole_0 | ~v5_relat_1(k2_funct_1(sK1),k1_xboole_0) | (~spl3_70 | ~spl3_87)),
% 1.63/0.58    inference(resolution,[],[f765,f538])).
% 1.63/0.58  fof(f538,plain,(
% 1.63/0.58    ( ! [X2,X1] : (~v2_funct_2(X1,X2) | ~v1_relat_1(X1) | sK1 = X1 | k1_xboole_0 != X2 | ~v5_relat_1(X1,X2)) ) | ~spl3_70),
% 1.63/0.58    inference(duplicate_literal_removal,[],[f536])).
% 1.63/0.58  fof(f536,plain,(
% 1.63/0.58    ( ! [X2,X1] : (k1_xboole_0 != X2 | ~v1_relat_1(X1) | sK1 = X1 | ~v2_funct_2(X1,X2) | ~v5_relat_1(X1,X2) | ~v1_relat_1(X1)) ) | ~spl3_70),
% 1.63/0.58    inference(superposition,[],[f533,f62])).
% 1.63/0.58  fof(f62,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f43])).
% 1.63/0.58  fof(f43,plain,(
% 1.63/0.58    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(nnf_transformation,[],[f26])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(flattening,[],[f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f10])).
% 1.63/0.58  fof(f10,axiom,(
% 1.63/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.63/0.58  fof(f533,plain,(
% 1.63/0.58    ( ! [X1] : (k1_xboole_0 != k2_relat_1(X1) | ~v1_relat_1(X1) | sK1 = X1) ) | ~spl3_70),
% 1.63/0.58    inference(avatar_component_clause,[],[f532])).
% 1.63/0.58  fof(f765,plain,(
% 1.63/0.58    v2_funct_2(k2_funct_1(sK1),k1_xboole_0) | ~spl3_87),
% 1.63/0.58    inference(avatar_component_clause,[],[f763])).
% 1.63/0.58  fof(f766,plain,(
% 1.63/0.58    spl3_87 | ~spl3_31 | ~spl3_60 | ~spl3_81),
% 1.63/0.58    inference(avatar_split_clause,[],[f730,f719,f469,f264,f763])).
% 1.63/0.58  fof(f264,plain,(
% 1.63/0.58    spl3_31 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.63/0.58  fof(f469,plain,(
% 1.63/0.58    spl3_60 <=> v3_funct_2(k2_funct_1(sK1),k1_xboole_0,k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.63/0.58  fof(f719,plain,(
% 1.63/0.58    spl3_81 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 1.63/0.58  fof(f730,plain,(
% 1.63/0.58    ~v3_funct_2(k2_funct_1(sK1),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_2(k2_funct_1(sK1),k1_xboole_0) | ~spl3_81),
% 1.63/0.58    inference(resolution,[],[f721,f74])).
% 1.63/0.58  fof(f74,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f35])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(flattening,[],[f34])).
% 1.63/0.58  fof(f34,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.63/0.58  fof(f721,plain,(
% 1.63/0.58    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_81),
% 1.63/0.58    inference(avatar_component_clause,[],[f719])).
% 1.63/0.58  fof(f745,plain,(
% 1.63/0.58    spl3_83 | ~spl3_81),
% 1.63/0.58    inference(avatar_split_clause,[],[f731,f719,f742])).
% 1.63/0.58  fof(f731,plain,(
% 1.63/0.58    v5_relat_1(k2_funct_1(sK1),k1_xboole_0) | ~spl3_81),
% 1.63/0.58    inference(resolution,[],[f721,f71])).
% 1.63/0.58  fof(f71,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f33])).
% 1.63/0.58  fof(f33,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f19])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.63/0.58    inference(pure_predicate_removal,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.63/0.58  fof(f740,plain,(
% 1.63/0.58    spl3_82 | ~spl3_81),
% 1.63/0.58    inference(avatar_split_clause,[],[f732,f719,f737])).
% 1.63/0.58  fof(f732,plain,(
% 1.63/0.58    v1_relat_1(k2_funct_1(sK1)) | ~spl3_81),
% 1.63/0.58    inference(resolution,[],[f721,f69])).
% 1.63/0.58  fof(f69,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f31])).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.63/0.58  fof(f722,plain,(
% 1.63/0.58    ~spl3_1 | ~spl3_44 | ~spl3_48 | ~spl3_51 | spl3_81 | ~spl3_64),
% 1.63/0.58    inference(avatar_split_clause,[],[f495,f489,f719,f400,f384,f364,f84])).
% 1.63/0.58  fof(f84,plain,(
% 1.63/0.58    spl3_1 <=> v1_funct_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.63/0.58  fof(f364,plain,(
% 1.63/0.58    spl3_44 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.63/0.58  fof(f384,plain,(
% 1.63/0.58    spl3_48 <=> v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.63/0.58  fof(f400,plain,(
% 1.63/0.58    spl3_51 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 1.63/0.58  fof(f489,plain,(
% 1.63/0.58    spl3_64 <=> k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 1.63/0.58  fof(f495,plain,(
% 1.63/0.58    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | ~spl3_64),
% 1.63/0.58    inference(superposition,[],[f68,f491])).
% 1.63/0.58  fof(f491,plain,(
% 1.63/0.58    k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1) | ~spl3_64),
% 1.63/0.58    inference(avatar_component_clause,[],[f489])).
% 1.63/0.58  fof(f68,plain,(
% 1.63/0.58    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f30])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.63/0.58    inference(flattening,[],[f29])).
% 1.63/0.58  fof(f29,plain,(
% 1.63/0.58    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f11])).
% 1.63/0.58  fof(f11,axiom,(
% 1.63/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.63/0.58  fof(f655,plain,(
% 1.63/0.58    ~spl3_75 | ~spl3_23 | spl3_40),
% 1.63/0.58    inference(avatar_split_clause,[],[f637,f312,f217,f652])).
% 1.63/0.58  fof(f217,plain,(
% 1.63/0.58    spl3_23 <=> sK1 = sK2),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.63/0.58  fof(f312,plain,(
% 1.63/0.58    spl3_40 <=> sK2 = k2_funct_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.63/0.58  fof(f637,plain,(
% 1.63/0.58    sK1 != k2_funct_1(sK1) | (~spl3_23 | spl3_40)),
% 1.63/0.58    inference(backward_demodulation,[],[f313,f219])).
% 1.63/0.58  fof(f219,plain,(
% 1.63/0.58    sK1 = sK2 | ~spl3_23),
% 1.63/0.58    inference(avatar_component_clause,[],[f217])).
% 1.63/0.58  fof(f313,plain,(
% 1.63/0.58    sK2 != k2_funct_1(sK1) | spl3_40),
% 1.63/0.58    inference(avatar_component_clause,[],[f312])).
% 1.63/0.58  fof(f618,plain,(
% 1.63/0.58    ~spl3_45 | spl3_23 | ~spl3_11 | ~spl3_47 | ~spl3_70),
% 1.63/0.58    inference(avatar_split_clause,[],[f616,f532,f379,f152,f217,f369])).
% 1.63/0.58  fof(f369,plain,(
% 1.63/0.58    spl3_45 <=> v5_relat_1(sK2,k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.63/0.58  fof(f152,plain,(
% 1.63/0.58    spl3_11 <=> v1_relat_1(sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.63/0.58  fof(f379,plain,(
% 1.63/0.58    spl3_47 <=> v2_funct_2(sK2,k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.63/0.58  fof(f616,plain,(
% 1.63/0.58    ~v1_relat_1(sK2) | sK1 = sK2 | ~v5_relat_1(sK2,k1_xboole_0) | (~spl3_47 | ~spl3_70)),
% 1.63/0.58    inference(trivial_inequality_removal,[],[f615])).
% 1.63/0.58  fof(f615,plain,(
% 1.63/0.58    ~v1_relat_1(sK2) | sK1 = sK2 | k1_xboole_0 != k1_xboole_0 | ~v5_relat_1(sK2,k1_xboole_0) | (~spl3_47 | ~spl3_70)),
% 1.63/0.58    inference(resolution,[],[f538,f381])).
% 1.63/0.58  fof(f381,plain,(
% 1.63/0.58    v2_funct_2(sK2,k1_xboole_0) | ~spl3_47),
% 1.63/0.58    inference(avatar_component_clause,[],[f379])).
% 1.63/0.58  fof(f534,plain,(
% 1.63/0.58    ~spl3_10 | spl3_70 | ~spl3_52),
% 1.63/0.58    inference(avatar_split_clause,[],[f413,f405,f532,f138])).
% 1.63/0.58  fof(f138,plain,(
% 1.63/0.58    spl3_10 <=> v1_relat_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.63/0.58  fof(f405,plain,(
% 1.63/0.58    spl3_52 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.63/0.58  fof(f413,plain,(
% 1.63/0.58    ( ! [X1] : (sK1 = X1 | k1_xboole_0 != k2_relat_1(X1) | ~v1_relat_1(sK1) | ~v1_relat_1(X1)) ) | ~spl3_52),
% 1.63/0.58    inference(trivial_inequality_removal,[],[f412])).
% 1.63/0.58  fof(f412,plain,(
% 1.63/0.58    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | sK1 = X1 | k1_xboole_0 != k2_relat_1(X1) | ~v1_relat_1(sK1) | ~v1_relat_1(X1)) ) | ~spl3_52),
% 1.63/0.58    inference(superposition,[],[f59,f407])).
% 1.63/0.58  fof(f407,plain,(
% 1.63/0.58    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_52),
% 1.63/0.58    inference(avatar_component_clause,[],[f405])).
% 1.63/0.58  fof(f59,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_relat_1(X1) | X0 = X1 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f23])).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (X0 = X1 | k1_xboole_0 != k2_relat_1(X1) | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.58    inference(flattening,[],[f22])).
% 1.63/0.58  fof(f22,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : ((X0 = X1 | (k1_xboole_0 != k2_relat_1(X1) | k2_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f3])).
% 1.63/0.58  fof(f3,axiom,(
% 1.63/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k2_relat_1(X0) = k1_xboole_0) => X0 = X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).
% 1.63/0.58  fof(f492,plain,(
% 1.63/0.58    spl3_64 | ~spl3_30 | ~spl3_41),
% 1.63/0.58    inference(avatar_split_clause,[],[f349,f316,f254,f489])).
% 1.63/0.58  fof(f254,plain,(
% 1.63/0.58    spl3_30 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.63/0.58  fof(f316,plain,(
% 1.63/0.58    spl3_41 <=> k1_xboole_0 = sK0),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.63/0.58  fof(f349,plain,(
% 1.63/0.58    k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1) | (~spl3_30 | ~spl3_41)),
% 1.63/0.58    inference(backward_demodulation,[],[f256,f318])).
% 1.63/0.58  fof(f318,plain,(
% 1.63/0.58    k1_xboole_0 = sK0 | ~spl3_41),
% 1.63/0.58    inference(avatar_component_clause,[],[f316])).
% 1.63/0.58  fof(f256,plain,(
% 1.63/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_30),
% 1.63/0.58    inference(avatar_component_clause,[],[f254])).
% 1.63/0.58  fof(f472,plain,(
% 1.63/0.58    spl3_60 | ~spl3_36 | ~spl3_41),
% 1.63/0.58    inference(avatar_split_clause,[],[f353,f316,f293,f469])).
% 1.63/0.58  fof(f293,plain,(
% 1.63/0.58    spl3_36 <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.63/0.58  fof(f353,plain,(
% 1.63/0.58    v3_funct_2(k2_funct_1(sK1),k1_xboole_0,k1_xboole_0) | (~spl3_36 | ~spl3_41)),
% 1.63/0.58    inference(backward_demodulation,[],[f295,f318])).
% 1.63/0.58  fof(f295,plain,(
% 1.63/0.58    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~spl3_36),
% 1.63/0.58    inference(avatar_component_clause,[],[f293])).
% 1.63/0.58  fof(f408,plain,(
% 1.63/0.58    spl3_52 | ~spl3_41 | ~spl3_42),
% 1.63/0.58    inference(avatar_split_clause,[],[f388,f322,f316,f405])).
% 1.63/0.58  fof(f322,plain,(
% 1.63/0.58    spl3_42 <=> sK0 = k2_relat_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.63/0.58  fof(f388,plain,(
% 1.63/0.58    k1_xboole_0 = k2_relat_1(sK1) | (~spl3_41 | ~spl3_42)),
% 1.63/0.58    inference(forward_demodulation,[],[f323,f318])).
% 1.63/0.58  fof(f323,plain,(
% 1.63/0.58    sK0 = k2_relat_1(sK1) | ~spl3_42),
% 1.63/0.58    inference(avatar_component_clause,[],[f322])).
% 1.63/0.58  fof(f403,plain,(
% 1.63/0.58    spl3_51 | ~spl3_7 | ~spl3_41),
% 1.63/0.58    inference(avatar_split_clause,[],[f334,f316,f114,f400])).
% 1.63/0.58  fof(f114,plain,(
% 1.63/0.58    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.63/0.58  fof(f334,plain,(
% 1.63/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_7 | ~spl3_41)),
% 1.63/0.58    inference(backward_demodulation,[],[f116,f318])).
% 1.63/0.58  fof(f116,plain,(
% 1.63/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 1.63/0.58    inference(avatar_component_clause,[],[f114])).
% 1.63/0.58  fof(f387,plain,(
% 1.63/0.58    spl3_48 | ~spl3_4 | ~spl3_41),
% 1.63/0.58    inference(avatar_split_clause,[],[f331,f316,f99,f384])).
% 1.63/0.58  fof(f99,plain,(
% 1.63/0.58    spl3_4 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.63/0.58  fof(f331,plain,(
% 1.63/0.58    v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl3_4 | ~spl3_41)),
% 1.63/0.58    inference(backward_demodulation,[],[f101,f318])).
% 1.63/0.58  fof(f101,plain,(
% 1.63/0.58    v3_funct_2(sK1,sK0,sK0) | ~spl3_4),
% 1.63/0.58    inference(avatar_component_clause,[],[f99])).
% 1.63/0.58  fof(f382,plain,(
% 1.63/0.58    spl3_47 | ~spl3_20 | ~spl3_41),
% 1.63/0.58    inference(avatar_split_clause,[],[f344,f316,f197,f379])).
% 1.63/0.58  fof(f197,plain,(
% 1.63/0.58    spl3_20 <=> v2_funct_2(sK2,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.63/0.58  fof(f344,plain,(
% 1.63/0.58    v2_funct_2(sK2,k1_xboole_0) | (~spl3_20 | ~spl3_41)),
% 1.63/0.58    inference(backward_demodulation,[],[f199,f318])).
% 1.63/0.58  fof(f199,plain,(
% 1.63/0.58    v2_funct_2(sK2,sK0) | ~spl3_20),
% 1.63/0.58    inference(avatar_component_clause,[],[f197])).
% 1.63/0.58  fof(f372,plain,(
% 1.63/0.58    spl3_45 | ~spl3_13 | ~spl3_41),
% 1.63/0.58    inference(avatar_split_clause,[],[f339,f316,f162,f369])).
% 1.63/0.58  fof(f162,plain,(
% 1.63/0.58    spl3_13 <=> v5_relat_1(sK2,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.63/0.58  fof(f339,plain,(
% 1.63/0.58    v5_relat_1(sK2,k1_xboole_0) | (~spl3_13 | ~spl3_41)),
% 1.63/0.58    inference(backward_demodulation,[],[f164,f318])).
% 1.63/0.58  fof(f164,plain,(
% 1.63/0.58    v5_relat_1(sK2,sK0) | ~spl3_13),
% 1.63/0.58    inference(avatar_component_clause,[],[f162])).
% 1.63/0.58  fof(f367,plain,(
% 1.63/0.58    spl3_44 | ~spl3_3 | ~spl3_41),
% 1.63/0.58    inference(avatar_split_clause,[],[f330,f316,f94,f364])).
% 1.63/0.58  fof(f94,plain,(
% 1.63/0.58    spl3_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.63/0.58  fof(f330,plain,(
% 1.63/0.58    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_41)),
% 1.63/0.58    inference(backward_demodulation,[],[f96,f318])).
% 1.63/0.58  fof(f96,plain,(
% 1.63/0.58    v1_funct_2(sK1,sK0,sK0) | ~spl3_3),
% 1.63/0.58    inference(avatar_component_clause,[],[f94])).
% 1.63/0.58  fof(f329,plain,(
% 1.63/0.58    sK2 != k2_funct_1(sK1) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.63/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.58  fof(f328,plain,(
% 1.63/0.58    ~spl3_10 | ~spl3_12 | ~spl3_19 | spl3_42),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f326])).
% 1.63/0.58  fof(f326,plain,(
% 1.63/0.58    $false | (~spl3_10 | ~spl3_12 | ~spl3_19 | spl3_42)),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f140,f159,f194,f324,f62])).
% 1.63/0.58  fof(f324,plain,(
% 1.63/0.58    sK0 != k2_relat_1(sK1) | spl3_42),
% 1.63/0.58    inference(avatar_component_clause,[],[f322])).
% 1.63/0.58  fof(f194,plain,(
% 1.63/0.58    v2_funct_2(sK1,sK0) | ~spl3_19),
% 1.63/0.58    inference(avatar_component_clause,[],[f192])).
% 1.63/0.58  fof(f192,plain,(
% 1.63/0.58    spl3_19 <=> v2_funct_2(sK1,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.63/0.58  fof(f159,plain,(
% 1.63/0.58    v5_relat_1(sK1,sK0) | ~spl3_12),
% 1.63/0.58    inference(avatar_component_clause,[],[f157])).
% 1.63/0.58  fof(f157,plain,(
% 1.63/0.58    spl3_12 <=> v5_relat_1(sK1,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.63/0.58  fof(f140,plain,(
% 1.63/0.58    v1_relat_1(sK1) | ~spl3_10),
% 1.63/0.58    inference(avatar_component_clause,[],[f138])).
% 1.63/0.58  fof(f325,plain,(
% 1.63/0.58    ~spl3_7 | ~spl3_42 | spl3_39),
% 1.63/0.58    inference(avatar_split_clause,[],[f320,f308,f322,f114])).
% 1.63/0.58  fof(f308,plain,(
% 1.63/0.58    spl3_39 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.63/0.58  fof(f320,plain,(
% 1.63/0.58    sK0 != k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_39),
% 1.63/0.58    inference(superposition,[],[f310,f70])).
% 1.63/0.58  fof(f70,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f32])).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f7])).
% 1.63/0.58  fof(f7,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.63/0.58  fof(f310,plain,(
% 1.63/0.58    sK0 != k2_relset_1(sK0,sK0,sK1) | spl3_39),
% 1.63/0.58    inference(avatar_component_clause,[],[f308])).
% 1.63/0.58  fof(f319,plain,(
% 1.63/0.58    ~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_2 | ~spl3_5 | ~spl3_8 | ~spl3_39 | spl3_40 | ~spl3_16 | spl3_41 | ~spl3_17),
% 1.63/0.58    inference(avatar_split_clause,[],[f202,f182,f316,f177,f312,f308,f119,f104,f89,f114,f94,f84])).
% 1.63/0.58  fof(f89,plain,(
% 1.63/0.58    spl3_2 <=> v1_funct_1(sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.63/0.58  fof(f104,plain,(
% 1.63/0.58    spl3_5 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.63/0.58  fof(f119,plain,(
% 1.63/0.58    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.63/0.58  fof(f177,plain,(
% 1.63/0.58    spl3_16 <=> v2_funct_1(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.63/0.58  fof(f182,plain,(
% 1.63/0.58    spl3_17 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.63/0.58  fof(f202,plain,(
% 1.63/0.58    k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_17),
% 1.63/0.58    inference(duplicate_literal_removal,[],[f201])).
% 1.63/0.58  fof(f201,plain,(
% 1.63/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_17),
% 1.63/0.58    inference(resolution,[],[f184,f75])).
% 1.63/0.58  fof(f75,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f37])).
% 1.63/0.58  fof(f37,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.63/0.58    inference(flattening,[],[f36])).
% 1.63/0.58  fof(f36,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.63/0.58    inference(ennf_transformation,[],[f15])).
% 1.63/0.58  fof(f15,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.63/0.58  fof(f184,plain,(
% 1.63/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl3_17),
% 1.63/0.58    inference(avatar_component_clause,[],[f182])).
% 1.63/0.58  fof(f296,plain,(
% 1.63/0.58    ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_7 | spl3_36 | ~spl3_30),
% 1.63/0.58    inference(avatar_split_clause,[],[f261,f254,f293,f114,f99,f94,f84])).
% 1.63/0.58  fof(f261,plain,(
% 1.63/0.58    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_30),
% 1.63/0.58    inference(superposition,[],[f67,f256])).
% 1.63/0.58  fof(f67,plain,(
% 1.63/0.58    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f30])).
% 1.63/0.58  fof(f267,plain,(
% 1.63/0.58    spl3_31 | ~spl3_21 | ~spl3_30),
% 1.63/0.58    inference(avatar_split_clause,[],[f258,f254,f204,f264])).
% 1.63/0.58  fof(f204,plain,(
% 1.63/0.58    spl3_21 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.63/0.58  fof(f258,plain,(
% 1.63/0.58    v1_funct_1(k2_funct_1(sK1)) | (~spl3_21 | ~spl3_30)),
% 1.63/0.58    inference(backward_demodulation,[],[f206,f256])).
% 1.63/0.58  fof(f206,plain,(
% 1.63/0.58    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl3_21),
% 1.63/0.58    inference(avatar_component_clause,[],[f204])).
% 1.63/0.58  fof(f257,plain,(
% 1.63/0.58    ~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_30 | ~spl3_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f129,f114,f254,f99,f94,f84])).
% 1.63/0.58  fof(f129,plain,(
% 1.63/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_7),
% 1.63/0.58    inference(resolution,[],[f116,f64])).
% 1.63/0.58  fof(f64,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f28])).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.63/0.58    inference(flattening,[],[f27])).
% 1.63/0.58  fof(f27,plain,(
% 1.63/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f13])).
% 1.63/0.58  fof(f13,axiom,(
% 1.63/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.63/0.58  fof(f207,plain,(
% 1.63/0.58    ~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_21 | ~spl3_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f128,f114,f204,f99,f94,f84])).
% 1.63/0.58  fof(f128,plain,(
% 1.63/0.58    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_7),
% 1.63/0.58    inference(resolution,[],[f116,f65])).
% 1.63/0.58  fof(f65,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f30])).
% 1.63/0.58  fof(f200,plain,(
% 1.63/0.58    spl3_20 | ~spl3_2 | ~spl3_6 | ~spl3_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f147,f119,f109,f89,f197])).
% 1.63/0.58  fof(f109,plain,(
% 1.63/0.58    spl3_6 <=> v3_funct_2(sK2,sK0,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.63/0.58  fof(f147,plain,(
% 1.63/0.58    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0) | ~spl3_8),
% 1.63/0.58    inference(resolution,[],[f121,f74])).
% 1.63/0.58  fof(f121,plain,(
% 1.63/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_8),
% 1.63/0.58    inference(avatar_component_clause,[],[f119])).
% 1.63/0.58  fof(f195,plain,(
% 1.63/0.58    spl3_19 | ~spl3_1 | ~spl3_4 | ~spl3_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f133,f114,f99,f84,f192])).
% 1.63/0.58  fof(f133,plain,(
% 1.63/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | ~spl3_7),
% 1.63/0.58    inference(resolution,[],[f116,f74])).
% 1.63/0.58  fof(f185,plain,(
% 1.63/0.58    spl3_17),
% 1.63/0.58    inference(avatar_split_clause,[],[f53,f182])).
% 1.63/0.58  fof(f53,plain,(
% 1.63/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f42,plain,(
% 1.63/0.58    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f41,f40])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.63/0.58    inference(flattening,[],[f20])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f17])).
% 1.63/0.58  fof(f17,negated_conjecture,(
% 1.63/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.63/0.58    inference(negated_conjecture,[],[f16])).
% 1.63/0.58  fof(f16,conjecture,(
% 1.63/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.63/0.58  fof(f180,plain,(
% 1.63/0.58    spl3_16 | ~spl3_1 | ~spl3_4 | ~spl3_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f132,f114,f99,f84,f177])).
% 1.63/0.58  fof(f132,plain,(
% 1.63/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1) | ~spl3_7),
% 1.63/0.58    inference(resolution,[],[f116,f73])).
% 1.63/0.58  fof(f73,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f35])).
% 1.63/0.58  fof(f175,plain,(
% 1.63/0.58    spl3_15 | ~spl3_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f145,f119,f172])).
% 1.63/0.58  fof(f172,plain,(
% 1.63/0.58    spl3_15 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.63/0.58  fof(f145,plain,(
% 1.63/0.58    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_8),
% 1.63/0.58    inference(resolution,[],[f121,f82])).
% 1.63/0.58  fof(f82,plain,(
% 1.63/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.63/0.58    inference(duplicate_literal_removal,[],[f81])).
% 1.63/0.58  fof(f81,plain,(
% 1.63/0.58    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.58    inference(equality_resolution,[],[f77])).
% 1.63/0.58  fof(f77,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f44])).
% 1.63/0.58  fof(f44,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(nnf_transformation,[],[f39])).
% 1.63/0.58  fof(f39,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(flattening,[],[f38])).
% 1.63/0.58  fof(f38,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.63/0.58    inference(ennf_transformation,[],[f8])).
% 1.63/0.58  fof(f8,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.63/0.58  fof(f165,plain,(
% 1.63/0.58    spl3_13 | ~spl3_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f148,f119,f162])).
% 1.63/0.58  fof(f148,plain,(
% 1.63/0.58    v5_relat_1(sK2,sK0) | ~spl3_8),
% 1.63/0.58    inference(resolution,[],[f121,f71])).
% 1.63/0.58  fof(f160,plain,(
% 1.63/0.58    spl3_12 | ~spl3_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f134,f114,f157])).
% 1.63/0.58  fof(f134,plain,(
% 1.63/0.58    v5_relat_1(sK1,sK0) | ~spl3_7),
% 1.63/0.58    inference(resolution,[],[f116,f71])).
% 1.63/0.58  fof(f155,plain,(
% 1.63/0.58    spl3_11 | ~spl3_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f149,f119,f152])).
% 1.63/0.58  fof(f149,plain,(
% 1.63/0.58    v1_relat_1(sK2) | ~spl3_8),
% 1.63/0.58    inference(resolution,[],[f121,f69])).
% 1.63/0.58  fof(f141,plain,(
% 1.63/0.58    spl3_10 | ~spl3_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f135,f114,f138])).
% 1.63/0.58  fof(f135,plain,(
% 1.63/0.58    v1_relat_1(sK1) | ~spl3_7),
% 1.63/0.58    inference(resolution,[],[f116,f69])).
% 1.63/0.58  fof(f127,plain,(
% 1.63/0.58    ~spl3_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f54,f124])).
% 1.63/0.58  fof(f124,plain,(
% 1.63/0.58    spl3_9 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.63/0.58  fof(f54,plain,(
% 1.63/0.58    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f122,plain,(
% 1.63/0.58    spl3_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f52,f119])).
% 1.63/0.58  fof(f52,plain,(
% 1.63/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f117,plain,(
% 1.63/0.58    spl3_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f48,f114])).
% 1.63/0.58  fof(f48,plain,(
% 1.63/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f112,plain,(
% 1.63/0.58    spl3_6),
% 1.63/0.58    inference(avatar_split_clause,[],[f51,f109])).
% 1.63/0.58  fof(f51,plain,(
% 1.63/0.58    v3_funct_2(sK2,sK0,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f107,plain,(
% 1.63/0.58    spl3_5),
% 1.63/0.58    inference(avatar_split_clause,[],[f50,f104])).
% 1.63/0.58  fof(f50,plain,(
% 1.63/0.58    v1_funct_2(sK2,sK0,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f102,plain,(
% 1.63/0.58    spl3_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f47,f99])).
% 1.63/0.58  fof(f47,plain,(
% 1.63/0.58    v3_funct_2(sK1,sK0,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f97,plain,(
% 1.63/0.58    spl3_3),
% 1.63/0.58    inference(avatar_split_clause,[],[f46,f94])).
% 1.63/0.58  fof(f46,plain,(
% 1.63/0.58    v1_funct_2(sK1,sK0,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f92,plain,(
% 1.63/0.58    spl3_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f49,f89])).
% 1.63/0.58  fof(f49,plain,(
% 1.63/0.58    v1_funct_1(sK2)),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  fof(f87,plain,(
% 1.63/0.58    spl3_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f45,f84])).
% 1.63/0.58  fof(f45,plain,(
% 1.63/0.58    v1_funct_1(sK1)),
% 1.63/0.58    inference(cnf_transformation,[],[f42])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (20224)------------------------------
% 1.63/0.58  % (20224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (20224)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (20224)Memory used [KB]: 11257
% 1.63/0.58  % (20224)Time elapsed: 0.144 s
% 1.63/0.58  % (20224)------------------------------
% 1.63/0.58  % (20224)------------------------------
% 1.63/0.58  % (20212)Success in time 0.214 s
%------------------------------------------------------------------------------
