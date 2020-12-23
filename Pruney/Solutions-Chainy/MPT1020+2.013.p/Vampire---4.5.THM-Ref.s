%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:41 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 374 expanded)
%              Number of leaves         :   57 ( 170 expanded)
%              Depth                    :    8
%              Number of atoms          :  611 (1299 expanded)
%              Number of equality atoms :   89 ( 135 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f982,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f199,f216,f236,f241,f248,f251,f281,f287,f298,f316,f340,f356,f367,f408,f413,f474,f564,f565,f566,f567,f580,f602,f723,f842,f852,f919,f960,f971])).

fof(f971,plain,
    ( spl4_101
    | ~ spl4_24
    | ~ spl4_110 ),
    inference(avatar_split_clause,[],[f963,f957,f246,f848])).

fof(f848,plain,
    ( spl4_101
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f246,plain,
    ( spl4_24
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f957,plain,
    ( spl4_110
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f963,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl4_24
    | ~ spl4_110 ),
    inference(resolution,[],[f959,f247])).

fof(f247,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X1) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f246])).

fof(f959,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_110 ),
    inference(avatar_component_clause,[],[f957])).

fof(f960,plain,
    ( spl4_110
    | ~ spl4_50
    | ~ spl4_61
    | ~ spl4_64
    | ~ spl4_107 ),
    inference(avatar_split_clause,[],[f955,f914,f577,f557,f471,f957])).

fof(f471,plain,
    ( spl4_50
  <=> m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f557,plain,
    ( spl4_61
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f577,plain,
    ( spl4_64
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f914,plain,
    ( spl4_107
  <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f955,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_50
    | ~ spl4_61
    | ~ spl4_64
    | ~ spl4_107 ),
    inference(forward_demodulation,[],[f954,f916])).

fof(f916,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ spl4_107 ),
    inference(avatar_component_clause,[],[f914])).

fof(f954,plain,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_50
    | ~ spl4_61
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f953,f579])).

fof(f579,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f577])).

fof(f953,plain,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_50
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f952,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f952,plain,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_50
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f473,f559])).

fof(f559,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f557])).

fof(f473,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f471])).

fof(f919,plain,
    ( spl4_107
    | ~ spl4_67
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f918,f720,f599,f914])).

fof(f599,plain,
    ( spl4_67
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f720,plain,
    ( spl4_86
  <=> k2_funct_1(sK2) = k2_funct_2(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f918,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ spl4_67
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f722,f601])).

fof(f601,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f599])).

fof(f722,plain,
    ( k2_funct_1(sK2) = k2_funct_2(k1_xboole_0,sK2)
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f720])).

fof(f852,plain,
    ( ~ spl4_11
    | ~ spl4_101
    | spl4_100 ),
    inference(avatar_split_clause,[],[f846,f839,f848,f146])).

fof(f146,plain,
    ( spl4_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f839,plain,
    ( spl4_100
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f846,plain,
    ( ~ v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | spl4_100 ),
    inference(extensionality_resolution,[],[f76,f841])).

fof(f841,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | spl4_100 ),
    inference(avatar_component_clause,[],[f839])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f842,plain,
    ( ~ spl4_100
    | spl4_60
    | ~ spl4_64
    | ~ spl4_67 ),
    inference(avatar_split_clause,[],[f837,f599,f577,f553,f839])).

fof(f553,plain,
    ( spl4_60
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f837,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | spl4_60
    | ~ spl4_64
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f836,f601])).

fof(f836,plain,
    ( sK2 != k2_funct_1(k1_xboole_0)
    | spl4_60
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f554,f579])).

fof(f554,plain,
    ( sK2 != k2_funct_1(sK1)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f553])).

fof(f723,plain,
    ( spl4_86
    | ~ spl4_44
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f622,f557,f410,f720])).

fof(f410,plain,
    ( spl4_44
  <=> k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f622,plain,
    ( k2_funct_1(sK2) = k2_funct_2(k1_xboole_0,sK2)
    | ~ spl4_44
    | ~ spl4_61 ),
    inference(backward_demodulation,[],[f412,f559])).

fof(f412,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f410])).

fof(f602,plain,
    ( spl4_67
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f591,f238,f146,f599])).

fof(f238,plain,
    ( spl4_22
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f591,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(resolution,[],[f240,f164])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_11 ),
    inference(resolution,[],[f76,f148])).

fof(f148,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f240,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f238])).

fof(f580,plain,
    ( spl4_64
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f569,f229,f146,f577])).

fof(f229,plain,
    ( spl4_20
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f569,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(resolution,[],[f231,f164])).

fof(f231,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f229])).

fof(f567,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f566,plain,
    ( sK2 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f565,plain,
    ( sK0 != k2_relat_1(sK1)
    | k2_relset_1(sK0,sK0,sK1) != k2_relat_1(sK1)
    | sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f564,plain,
    ( spl4_60
    | spl4_61
    | ~ spl4_35
    | ~ spl4_4
    | ~ spl4_62
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f551,f121,f106,f96,f141,f136,f126,f561,f111,f337,f557,f553])).

fof(f337,plain,
    ( spl4_35
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f111,plain,
    ( spl4_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f561,plain,
    ( spl4_62
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f126,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f136,plain,
    ( spl4_9
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f141,plain,
    ( spl4_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f96,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( spl4_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f121,plain,
    ( spl4_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f551,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f549])).

fof(f549,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f84,f123])).

fof(f123,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k2_funct_1(X2) = X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f474,plain,
    ( spl4_50
    | ~ spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f464,f96,f106,f101,f111,f471])).

fof(f101,plain,
    ( spl4_2
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f464,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f67,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f413,plain,
    ( spl4_44
    | ~ spl4_10
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f399,f126,f136,f131,f141,f410])).

fof(f131,plain,
    ( spl4_8
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f399,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f63,f128])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f408,plain,
    ( spl4_43
    | ~ spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f398,f96,f106,f101,f111,f405])).

fof(f405,plain,
    ( spl4_43
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f398,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f63,f98])).

fof(f367,plain,
    ( ~ spl4_16
    | spl4_39
    | ~ spl4_18
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f362,f353,f213,f364,f196])).

fof(f196,plain,
    ( spl4_16
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f364,plain,
    ( spl4_39
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f213,plain,
    ( spl4_18
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f353,plain,
    ( spl4_37
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f362,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_37 ),
    inference(resolution,[],[f355,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f355,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f353])).

fof(f356,plain,
    ( spl4_37
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f346,f96,f111,f101,f353])).

fof(f346,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f81,f98])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f340,plain,
    ( spl4_35
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f330,f96,f111,f101,f337])).

fof(f330,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_1(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f80,f98])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f316,plain,
    ( spl4_32
    | ~ spl4_11
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f305,f284,f146,f313])).

fof(f313,plain,
    ( spl4_32
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f284,plain,
    ( spl4_28
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f305,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_28 ),
    inference(resolution,[],[f286,f164])).

fof(f286,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f284])).

fof(f298,plain,
    ( spl4_29
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f288,f96,f295])).

fof(f295,plain,
    ( spl4_29
  <=> k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f288,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f78,f98])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f287,plain,
    ( spl4_28
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f282,f146,f284])).

fof(f282,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_11 ),
    inference(resolution,[],[f224,f148])).

fof(f224,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f60,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f281,plain,
    ( spl4_27
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f267,f126,f278])).

fof(f278,plain,
    ( spl4_27
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f267,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f94,f128])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f251,plain,
    ( ~ spl4_11
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_23 ),
    inference(resolution,[],[f244,f148])).

fof(f244,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl4_23
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f248,plain,
    ( spl4_23
    | spl4_24 ),
    inference(avatar_split_clause,[],[f226,f246,f243])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f60,f91])).

fof(f241,plain,
    ( spl4_22
    | ~ spl4_21
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f223,f126,f233,f238])).

fof(f233,plain,
    ( spl4_21
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f223,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f60,f128])).

fof(f236,plain,
    ( spl4_20
    | ~ spl4_21
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f222,f96,f233,f229])).

fof(f222,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f60,f98])).

fof(f216,plain,
    ( spl4_18
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f206,f96,f213])).

fof(f206,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f79,f98])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f199,plain,
    ( spl4_16
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f189,f96,f196])).

fof(f189,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f77,f98])).

fof(f77,plain,(
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

fof(f149,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f57,f146])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f144,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f47,f141])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f139,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f48,f136])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f134,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f49,f131])).

fof(f49,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f129,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f50,f126])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f124,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f51,f121])).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f52,f116])).

fof(f116,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f52,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f114,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f53,f111])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f54,f106])).

fof(f54,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f55,f101])).

fof(f55,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f56,f96])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (17373)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (17383)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (17375)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (17374)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (17395)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (17376)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (17389)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (17380)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (17387)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (17399)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (17393)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.54  % (17371)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.54  % (17378)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  % (17385)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (17398)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (17391)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (17397)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (17400)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.55  % (17381)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (17379)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (17390)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (17377)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.56  % (17392)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.56  % (17394)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.56  % (17372)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.56  % (17382)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.56  % (17388)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.56  % (17373)Refutation not found, incomplete strategy% (17373)------------------------------
% 1.35/0.56  % (17373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (17373)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (17373)Memory used [KB]: 11001
% 1.35/0.56  % (17373)Time elapsed: 0.120 s
% 1.35/0.56  % (17373)------------------------------
% 1.35/0.56  % (17373)------------------------------
% 1.35/0.56  % (17384)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.57  % (17386)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.57  % (17396)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.59  % (17393)Refutation not found, incomplete strategy% (17393)------------------------------
% 1.52/0.59  % (17393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (17393)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.59  
% 1.52/0.59  % (17393)Memory used [KB]: 11385
% 1.52/0.59  % (17393)Time elapsed: 0.129 s
% 1.52/0.59  % (17393)------------------------------
% 1.52/0.59  % (17393)------------------------------
% 1.52/0.61  % (17387)Refutation found. Thanks to Tanya!
% 1.52/0.61  % SZS status Theorem for theBenchmark
% 1.52/0.61  % SZS output start Proof for theBenchmark
% 1.52/0.61  fof(f982,plain,(
% 1.52/0.61    $false),
% 1.52/0.61    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f199,f216,f236,f241,f248,f251,f281,f287,f298,f316,f340,f356,f367,f408,f413,f474,f564,f565,f566,f567,f580,f602,f723,f842,f852,f919,f960,f971])).
% 1.52/0.61  fof(f971,plain,(
% 1.52/0.61    spl4_101 | ~spl4_24 | ~spl4_110),
% 1.52/0.61    inference(avatar_split_clause,[],[f963,f957,f246,f848])).
% 1.52/0.61  fof(f848,plain,(
% 1.52/0.61    spl4_101 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).
% 1.52/0.61  fof(f246,plain,(
% 1.52/0.61    spl4_24 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.52/0.61  fof(f957,plain,(
% 1.52/0.61    spl4_110 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).
% 1.52/0.61  fof(f963,plain,(
% 1.52/0.61    v1_xboole_0(k2_funct_1(k1_xboole_0)) | (~spl4_24 | ~spl4_110)),
% 1.52/0.61    inference(resolution,[],[f959,f247])).
% 1.52/0.61  fof(f247,plain,(
% 1.52/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1)) ) | ~spl4_24),
% 1.52/0.61    inference(avatar_component_clause,[],[f246])).
% 1.52/0.61  fof(f959,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_110),
% 1.52/0.61    inference(avatar_component_clause,[],[f957])).
% 1.52/0.61  fof(f960,plain,(
% 1.52/0.61    spl4_110 | ~spl4_50 | ~spl4_61 | ~spl4_64 | ~spl4_107),
% 1.52/0.61    inference(avatar_split_clause,[],[f955,f914,f577,f557,f471,f957])).
% 1.52/0.61  fof(f471,plain,(
% 1.52/0.61    spl4_50 <=> m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.52/0.61  fof(f557,plain,(
% 1.52/0.61    spl4_61 <=> k1_xboole_0 = sK0),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 1.52/0.61  fof(f577,plain,(
% 1.52/0.61    spl4_64 <=> k1_xboole_0 = sK1),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 1.52/0.61  fof(f914,plain,(
% 1.52/0.61    spl4_107 <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 1.52/0.61  fof(f955,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_50 | ~spl4_61 | ~spl4_64 | ~spl4_107)),
% 1.52/0.61    inference(forward_demodulation,[],[f954,f916])).
% 1.52/0.61  fof(f916,plain,(
% 1.52/0.61    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | ~spl4_107),
% 1.52/0.61    inference(avatar_component_clause,[],[f914])).
% 1.52/0.61  fof(f954,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_50 | ~spl4_61 | ~spl4_64)),
% 1.52/0.61    inference(forward_demodulation,[],[f953,f579])).
% 1.52/0.61  fof(f579,plain,(
% 1.52/0.61    k1_xboole_0 = sK1 | ~spl4_64),
% 1.52/0.61    inference(avatar_component_clause,[],[f577])).
% 1.52/0.61  fof(f953,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_2(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl4_50 | ~spl4_61)),
% 1.52/0.61    inference(forward_demodulation,[],[f952,f91])).
% 1.52/0.61  fof(f91,plain,(
% 1.52/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.52/0.61    inference(equality_resolution,[],[f75])).
% 1.52/0.61  fof(f75,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f4])).
% 1.52/0.61  fof(f4,axiom,(
% 1.52/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.52/0.61  fof(f952,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_2(k1_xboole_0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_50 | ~spl4_61)),
% 1.52/0.61    inference(forward_demodulation,[],[f473,f559])).
% 1.52/0.61  fof(f559,plain,(
% 1.52/0.61    k1_xboole_0 = sK0 | ~spl4_61),
% 1.52/0.61    inference(avatar_component_clause,[],[f557])).
% 1.52/0.61  fof(f473,plain,(
% 1.52/0.61    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_50),
% 1.52/0.61    inference(avatar_component_clause,[],[f471])).
% 1.52/0.61  fof(f919,plain,(
% 1.52/0.61    spl4_107 | ~spl4_67 | ~spl4_86),
% 1.52/0.61    inference(avatar_split_clause,[],[f918,f720,f599,f914])).
% 1.52/0.61  fof(f599,plain,(
% 1.52/0.61    spl4_67 <=> k1_xboole_0 = sK2),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.52/0.61  fof(f720,plain,(
% 1.52/0.61    spl4_86 <=> k2_funct_1(sK2) = k2_funct_2(k1_xboole_0,sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 1.52/0.61  fof(f918,plain,(
% 1.52/0.61    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | (~spl4_67 | ~spl4_86)),
% 1.52/0.61    inference(forward_demodulation,[],[f722,f601])).
% 1.52/0.61  fof(f601,plain,(
% 1.52/0.61    k1_xboole_0 = sK2 | ~spl4_67),
% 1.52/0.61    inference(avatar_component_clause,[],[f599])).
% 1.52/0.61  fof(f722,plain,(
% 1.52/0.61    k2_funct_1(sK2) = k2_funct_2(k1_xboole_0,sK2) | ~spl4_86),
% 1.52/0.61    inference(avatar_component_clause,[],[f720])).
% 1.52/0.61  fof(f852,plain,(
% 1.52/0.61    ~spl4_11 | ~spl4_101 | spl4_100),
% 1.52/0.61    inference(avatar_split_clause,[],[f846,f839,f848,f146])).
% 1.52/0.61  fof(f146,plain,(
% 1.52/0.61    spl4_11 <=> v1_xboole_0(k1_xboole_0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.52/0.61  fof(f839,plain,(
% 1.52/0.61    spl4_100 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).
% 1.52/0.61  fof(f846,plain,(
% 1.52/0.61    ~v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | spl4_100),
% 1.52/0.61    inference(extensionality_resolution,[],[f76,f841])).
% 1.52/0.61  fof(f841,plain,(
% 1.52/0.61    k1_xboole_0 != k2_funct_1(k1_xboole_0) | spl4_100),
% 1.52/0.61    inference(avatar_component_clause,[],[f839])).
% 1.52/0.61  fof(f76,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f33])).
% 1.52/0.61  fof(f33,plain,(
% 1.52/0.61    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.52/0.61    inference(ennf_transformation,[],[f3])).
% 1.52/0.61  fof(f3,axiom,(
% 1.52/0.61    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.52/0.61  fof(f842,plain,(
% 1.52/0.61    ~spl4_100 | spl4_60 | ~spl4_64 | ~spl4_67),
% 1.52/0.61    inference(avatar_split_clause,[],[f837,f599,f577,f553,f839])).
% 1.52/0.61  fof(f553,plain,(
% 1.52/0.61    spl4_60 <=> sK2 = k2_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.52/0.61  fof(f837,plain,(
% 1.52/0.61    k1_xboole_0 != k2_funct_1(k1_xboole_0) | (spl4_60 | ~spl4_64 | ~spl4_67)),
% 1.52/0.61    inference(forward_demodulation,[],[f836,f601])).
% 1.52/0.61  fof(f836,plain,(
% 1.52/0.61    sK2 != k2_funct_1(k1_xboole_0) | (spl4_60 | ~spl4_64)),
% 1.52/0.61    inference(forward_demodulation,[],[f554,f579])).
% 1.52/0.61  fof(f554,plain,(
% 1.52/0.61    sK2 != k2_funct_1(sK1) | spl4_60),
% 1.52/0.61    inference(avatar_component_clause,[],[f553])).
% 1.52/0.61  fof(f723,plain,(
% 1.52/0.61    spl4_86 | ~spl4_44 | ~spl4_61),
% 1.52/0.61    inference(avatar_split_clause,[],[f622,f557,f410,f720])).
% 1.52/0.61  fof(f410,plain,(
% 1.52/0.61    spl4_44 <=> k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.52/0.61  fof(f622,plain,(
% 1.52/0.61    k2_funct_1(sK2) = k2_funct_2(k1_xboole_0,sK2) | (~spl4_44 | ~spl4_61)),
% 1.52/0.61    inference(backward_demodulation,[],[f412,f559])).
% 1.52/0.61  fof(f412,plain,(
% 1.52/0.61    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~spl4_44),
% 1.52/0.61    inference(avatar_component_clause,[],[f410])).
% 1.52/0.61  fof(f602,plain,(
% 1.52/0.61    spl4_67 | ~spl4_11 | ~spl4_22),
% 1.52/0.61    inference(avatar_split_clause,[],[f591,f238,f146,f599])).
% 1.52/0.61  fof(f238,plain,(
% 1.52/0.61    spl4_22 <=> v1_xboole_0(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.52/0.61  fof(f591,plain,(
% 1.52/0.61    k1_xboole_0 = sK2 | (~spl4_11 | ~spl4_22)),
% 1.52/0.61    inference(resolution,[],[f240,f164])).
% 1.52/0.61  fof(f164,plain,(
% 1.52/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_11),
% 1.52/0.61    inference(resolution,[],[f76,f148])).
% 1.52/0.61  fof(f148,plain,(
% 1.52/0.61    v1_xboole_0(k1_xboole_0) | ~spl4_11),
% 1.52/0.61    inference(avatar_component_clause,[],[f146])).
% 1.52/0.61  fof(f240,plain,(
% 1.52/0.61    v1_xboole_0(sK2) | ~spl4_22),
% 1.52/0.61    inference(avatar_component_clause,[],[f238])).
% 1.52/0.61  fof(f580,plain,(
% 1.52/0.61    spl4_64 | ~spl4_11 | ~spl4_20),
% 1.52/0.61    inference(avatar_split_clause,[],[f569,f229,f146,f577])).
% 1.52/0.61  fof(f229,plain,(
% 1.52/0.61    spl4_20 <=> v1_xboole_0(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.52/0.61  fof(f569,plain,(
% 1.52/0.61    k1_xboole_0 = sK1 | (~spl4_11 | ~spl4_20)),
% 1.52/0.61    inference(resolution,[],[f231,f164])).
% 1.52/0.61  fof(f231,plain,(
% 1.52/0.61    v1_xboole_0(sK1) | ~spl4_20),
% 1.52/0.61    inference(avatar_component_clause,[],[f229])).
% 1.52/0.61  fof(f567,plain,(
% 1.52/0.61    k1_xboole_0 != k6_partfun1(k1_xboole_0) | k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.52/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.52/0.61  fof(f566,plain,(
% 1.52/0.61    sK2 != k2_funct_1(sK1) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.52/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.52/0.61  fof(f565,plain,(
% 1.52/0.61    sK0 != k2_relat_1(sK1) | k2_relset_1(sK0,sK0,sK1) != k2_relat_1(sK1) | sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.52/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.52/0.61  fof(f564,plain,(
% 1.52/0.61    spl4_60 | spl4_61 | ~spl4_35 | ~spl4_4 | ~spl4_62 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_1 | ~spl4_3 | ~spl4_6),
% 1.52/0.61    inference(avatar_split_clause,[],[f551,f121,f106,f96,f141,f136,f126,f561,f111,f337,f557,f553])).
% 1.52/0.61  fof(f337,plain,(
% 1.52/0.61    spl4_35 <=> v2_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.52/0.61  fof(f111,plain,(
% 1.52/0.61    spl4_4 <=> v1_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.52/0.61  fof(f561,plain,(
% 1.52/0.61    spl4_62 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 1.52/0.61  fof(f126,plain,(
% 1.52/0.61    spl4_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.52/0.61  fof(f136,plain,(
% 1.52/0.61    spl4_9 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.52/0.61  fof(f141,plain,(
% 1.52/0.61    spl4_10 <=> v1_funct_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.52/0.61  fof(f96,plain,(
% 1.52/0.61    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.52/0.61  fof(f106,plain,(
% 1.52/0.61    spl4_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.52/0.61  fof(f121,plain,(
% 1.52/0.61    spl4_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.52/0.61  fof(f551,plain,(
% 1.52/0.61    ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~spl4_6),
% 1.52/0.61    inference(duplicate_literal_removal,[],[f549])).
% 1.52/0.61  fof(f549,plain,(
% 1.52/0.61    ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~spl4_6),
% 1.52/0.61    inference(resolution,[],[f84,f123])).
% 1.52/0.61  fof(f123,plain,(
% 1.52/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl4_6),
% 1.52/0.61    inference(avatar_component_clause,[],[f121])).
% 1.52/0.61  fof(f84,plain,(
% 1.52/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) )),
% 1.52/0.61    inference(cnf_transformation,[],[f42])).
% 1.52/0.61  fof(f42,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.52/0.61    inference(flattening,[],[f41])).
% 1.52/0.61  fof(f41,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.52/0.61    inference(ennf_transformation,[],[f19])).
% 1.52/0.61  fof(f19,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.52/0.61  fof(f474,plain,(
% 1.52/0.61    spl4_50 | ~spl4_4 | ~spl4_2 | ~spl4_3 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f464,f96,f106,f101,f111,f471])).
% 1.52/0.61  fof(f101,plain,(
% 1.52/0.61    spl4_2 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.52/0.61  fof(f464,plain,(
% 1.52/0.61    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f67,f98])).
% 1.52/0.61  fof(f98,plain,(
% 1.52/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_1),
% 1.52/0.61    inference(avatar_component_clause,[],[f96])).
% 1.52/0.61  fof(f67,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.52/0.61    inference(cnf_transformation,[],[f31])).
% 1.52/0.61  fof(f31,plain,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.52/0.61    inference(flattening,[],[f30])).
% 1.52/0.61  fof(f30,plain,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f15])).
% 1.52/0.61  fof(f15,axiom,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.52/0.61  fof(f413,plain,(
% 1.52/0.61    spl4_44 | ~spl4_10 | ~spl4_8 | ~spl4_9 | ~spl4_7),
% 1.52/0.61    inference(avatar_split_clause,[],[f399,f126,f136,f131,f141,f410])).
% 1.52/0.61  fof(f131,plain,(
% 1.52/0.61    spl4_8 <=> v3_funct_2(sK2,sK0,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.52/0.61  fof(f399,plain,(
% 1.52/0.61    ~v1_funct_2(sK2,sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~spl4_7),
% 1.52/0.61    inference(resolution,[],[f63,f128])).
% 1.52/0.61  fof(f128,plain,(
% 1.52/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_7),
% 1.52/0.61    inference(avatar_component_clause,[],[f126])).
% 1.52/0.61  fof(f63,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f29])).
% 1.52/0.61  fof(f29,plain,(
% 1.52/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.52/0.61    inference(flattening,[],[f28])).
% 1.52/0.61  fof(f28,plain,(
% 1.52/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f16])).
% 1.52/0.61  fof(f16,axiom,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.52/0.61  fof(f408,plain,(
% 1.52/0.61    spl4_43 | ~spl4_4 | ~spl4_2 | ~spl4_3 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f398,f96,f106,f101,f111,f405])).
% 1.52/0.61  fof(f405,plain,(
% 1.52/0.61    spl4_43 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.52/0.61  fof(f398,plain,(
% 1.52/0.61    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f63,f98])).
% 1.52/0.61  fof(f367,plain,(
% 1.52/0.61    ~spl4_16 | spl4_39 | ~spl4_18 | ~spl4_37),
% 1.52/0.61    inference(avatar_split_clause,[],[f362,f353,f213,f364,f196])).
% 1.52/0.61  fof(f196,plain,(
% 1.52/0.61    spl4_16 <=> v1_relat_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.52/0.61  fof(f364,plain,(
% 1.52/0.61    spl4_39 <=> sK0 = k2_relat_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.52/0.61  fof(f213,plain,(
% 1.52/0.61    spl4_18 <=> v5_relat_1(sK1,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.52/0.61  fof(f353,plain,(
% 1.52/0.61    spl4_37 <=> v2_funct_2(sK1,sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.52/0.61  fof(f362,plain,(
% 1.52/0.61    ~v5_relat_1(sK1,sK0) | sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl4_37),
% 1.52/0.61    inference(resolution,[],[f355,f62])).
% 1.52/0.61  fof(f62,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f27])).
% 1.52/0.61  fof(f27,plain,(
% 1.52/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.52/0.61    inference(flattening,[],[f26])).
% 1.52/0.61  fof(f26,plain,(
% 1.52/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f13])).
% 1.52/0.61  fof(f13,axiom,(
% 1.52/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.52/0.61  fof(f355,plain,(
% 1.52/0.61    v2_funct_2(sK1,sK0) | ~spl4_37),
% 1.52/0.61    inference(avatar_component_clause,[],[f353])).
% 1.52/0.61  fof(f356,plain,(
% 1.52/0.61    spl4_37 | ~spl4_2 | ~spl4_4 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f346,f96,f111,f101,f353])).
% 1.52/0.61  fof(f346,plain,(
% 1.52/0.61    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_2(sK1,sK0) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f81,f98])).
% 1.52/0.61  fof(f81,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f38])).
% 1.52/0.61  fof(f38,plain,(
% 1.52/0.61    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(flattening,[],[f37])).
% 1.52/0.61  fof(f37,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(ennf_transformation,[],[f12])).
% 1.52/0.61  fof(f12,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.52/0.61  fof(f340,plain,(
% 1.52/0.61    spl4_35 | ~spl4_2 | ~spl4_4 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f330,f96,f111,f101,f337])).
% 1.52/0.61  fof(f330,plain,(
% 1.52/0.61    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_1(sK1) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f80,f98])).
% 1.52/0.61  fof(f80,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f38])).
% 1.52/0.61  fof(f316,plain,(
% 1.52/0.61    spl4_32 | ~spl4_11 | ~spl4_28),
% 1.52/0.61    inference(avatar_split_clause,[],[f305,f284,f146,f313])).
% 1.52/0.61  fof(f313,plain,(
% 1.52/0.61    spl4_32 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.52/0.61  fof(f284,plain,(
% 1.52/0.61    spl4_28 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.52/0.61  fof(f305,plain,(
% 1.52/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl4_11 | ~spl4_28)),
% 1.52/0.61    inference(resolution,[],[f286,f164])).
% 1.52/0.61  fof(f286,plain,(
% 1.52/0.61    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl4_28),
% 1.52/0.61    inference(avatar_component_clause,[],[f284])).
% 1.52/0.61  fof(f298,plain,(
% 1.52/0.61    spl4_29 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f288,f96,f295])).
% 1.52/0.61  fof(f295,plain,(
% 1.52/0.61    spl4_29 <=> k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.52/0.61  fof(f288,plain,(
% 1.52/0.61    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f78,f98])).
% 1.52/0.61  fof(f78,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f35])).
% 1.52/0.61  fof(f35,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(ennf_transformation,[],[f9])).
% 1.52/0.61  fof(f9,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.52/0.61  fof(f287,plain,(
% 1.52/0.61    spl4_28 | ~spl4_11),
% 1.52/0.61    inference(avatar_split_clause,[],[f282,f146,f284])).
% 1.52/0.61  fof(f282,plain,(
% 1.52/0.61    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl4_11),
% 1.52/0.61    inference(resolution,[],[f224,f148])).
% 1.52/0.61  fof(f224,plain,(
% 1.52/0.61    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k6_partfun1(X0))) )),
% 1.52/0.61    inference(resolution,[],[f60,f89])).
% 1.52/0.61  fof(f89,plain,(
% 1.52/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.52/0.61    inference(definition_unfolding,[],[f59,f58])).
% 1.52/0.61  fof(f58,plain,(
% 1.52/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f17])).
% 1.52/0.61  fof(f17,axiom,(
% 1.52/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.52/0.61  fof(f59,plain,(
% 1.52/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.52/0.61    inference(cnf_transformation,[],[f11])).
% 1.52/0.61  fof(f11,axiom,(
% 1.52/0.61    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.52/0.61  fof(f60,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f25])).
% 1.52/0.61  fof(f25,plain,(
% 1.52/0.61    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.52/0.61    inference(ennf_transformation,[],[f8])).
% 1.52/0.61  fof(f8,axiom,(
% 1.52/0.61    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.52/0.61  fof(f281,plain,(
% 1.52/0.61    spl4_27 | ~spl4_7),
% 1.52/0.61    inference(avatar_split_clause,[],[f267,f126,f278])).
% 1.52/0.61  fof(f278,plain,(
% 1.52/0.61    spl4_27 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.52/0.61  fof(f267,plain,(
% 1.52/0.61    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl4_7),
% 1.52/0.61    inference(resolution,[],[f94,f128])).
% 1.52/0.61  fof(f94,plain,(
% 1.52/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.52/0.61    inference(duplicate_literal_removal,[],[f93])).
% 1.52/0.61  fof(f93,plain,(
% 1.52/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.52/0.61    inference(equality_resolution,[],[f85])).
% 1.52/0.61  fof(f85,plain,(
% 1.52/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f44])).
% 1.52/0.61  fof(f44,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(flattening,[],[f43])).
% 1.52/0.61  fof(f43,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.52/0.61    inference(ennf_transformation,[],[f10])).
% 1.52/0.61  fof(f10,axiom,(
% 1.52/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.52/0.61  fof(f251,plain,(
% 1.52/0.61    ~spl4_11 | ~spl4_23),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f250])).
% 1.52/0.61  fof(f250,plain,(
% 1.52/0.61    $false | (~spl4_11 | ~spl4_23)),
% 1.52/0.61    inference(resolution,[],[f244,f148])).
% 1.52/0.61  fof(f244,plain,(
% 1.52/0.61    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl4_23),
% 1.52/0.61    inference(avatar_component_clause,[],[f243])).
% 1.52/0.61  fof(f243,plain,(
% 1.52/0.61    spl4_23 <=> ! [X0] : ~v1_xboole_0(X0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.52/0.61  fof(f248,plain,(
% 1.52/0.61    spl4_23 | spl4_24),
% 1.52/0.61    inference(avatar_split_clause,[],[f226,f246,f243])).
% 1.52/0.61  fof(f226,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.52/0.61    inference(superposition,[],[f60,f91])).
% 1.52/0.61  fof(f241,plain,(
% 1.52/0.61    spl4_22 | ~spl4_21 | ~spl4_7),
% 1.52/0.61    inference(avatar_split_clause,[],[f223,f126,f233,f238])).
% 1.52/0.61  fof(f233,plain,(
% 1.52/0.61    spl4_21 <=> v1_xboole_0(sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.52/0.61  fof(f223,plain,(
% 1.52/0.61    ~v1_xboole_0(sK0) | v1_xboole_0(sK2) | ~spl4_7),
% 1.52/0.61    inference(resolution,[],[f60,f128])).
% 1.52/0.61  fof(f236,plain,(
% 1.52/0.61    spl4_20 | ~spl4_21 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f222,f96,f233,f229])).
% 1.52/0.61  fof(f222,plain,(
% 1.52/0.61    ~v1_xboole_0(sK0) | v1_xboole_0(sK1) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f60,f98])).
% 1.52/0.61  fof(f216,plain,(
% 1.52/0.61    spl4_18 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f206,f96,f213])).
% 1.52/0.61  fof(f206,plain,(
% 1.52/0.61    v5_relat_1(sK1,sK0) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f79,f98])).
% 1.52/0.61  fof(f79,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f36])).
% 1.52/0.61  fof(f36,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(ennf_transformation,[],[f22])).
% 1.52/0.61  fof(f22,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.52/0.61    inference(pure_predicate_removal,[],[f7])).
% 1.52/0.61  fof(f7,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.52/0.61  fof(f199,plain,(
% 1.52/0.61    spl4_16 | ~spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f189,f96,f196])).
% 1.52/0.61  fof(f189,plain,(
% 1.52/0.61    v1_relat_1(sK1) | ~spl4_1),
% 1.52/0.61    inference(resolution,[],[f77,f98])).
% 1.52/0.61  fof(f77,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f34])).
% 1.52/0.61  fof(f34,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.61    inference(ennf_transformation,[],[f6])).
% 1.52/0.61  fof(f6,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.52/0.61  fof(f149,plain,(
% 1.52/0.61    spl4_11),
% 1.52/0.61    inference(avatar_split_clause,[],[f57,f146])).
% 1.52/0.61  fof(f57,plain,(
% 1.52/0.61    v1_xboole_0(k1_xboole_0)),
% 1.52/0.61    inference(cnf_transformation,[],[f2])).
% 1.52/0.61  fof(f2,axiom,(
% 1.52/0.61    v1_xboole_0(k1_xboole_0)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.52/0.61  fof(f144,plain,(
% 1.52/0.61    spl4_10),
% 1.52/0.61    inference(avatar_split_clause,[],[f47,f141])).
% 1.52/0.61  fof(f47,plain,(
% 1.52/0.61    v1_funct_1(sK2)),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f24,plain,(
% 1.52/0.61    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.52/0.61    inference(flattening,[],[f23])).
% 1.52/0.61  fof(f23,plain,(
% 1.52/0.61    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f21])).
% 1.52/0.61  fof(f21,negated_conjecture,(
% 1.52/0.61    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.52/0.61    inference(negated_conjecture,[],[f20])).
% 1.52/0.61  fof(f20,conjecture,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.52/0.61  fof(f139,plain,(
% 1.52/0.61    spl4_9),
% 1.52/0.61    inference(avatar_split_clause,[],[f48,f136])).
% 1.52/0.61  fof(f48,plain,(
% 1.52/0.61    v1_funct_2(sK2,sK0,sK0)),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f134,plain,(
% 1.52/0.61    spl4_8),
% 1.52/0.61    inference(avatar_split_clause,[],[f49,f131])).
% 1.52/0.61  fof(f49,plain,(
% 1.52/0.61    v3_funct_2(sK2,sK0,sK0)),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f129,plain,(
% 1.52/0.61    spl4_7),
% 1.52/0.61    inference(avatar_split_clause,[],[f50,f126])).
% 1.52/0.61  fof(f50,plain,(
% 1.52/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f124,plain,(
% 1.52/0.61    spl4_6),
% 1.52/0.61    inference(avatar_split_clause,[],[f51,f121])).
% 1.52/0.61  fof(f51,plain,(
% 1.52/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f119,plain,(
% 1.52/0.61    ~spl4_5),
% 1.52/0.61    inference(avatar_split_clause,[],[f52,f116])).
% 1.52/0.61  fof(f116,plain,(
% 1.52/0.61    spl4_5 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.52/0.61  fof(f52,plain,(
% 1.52/0.61    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f114,plain,(
% 1.52/0.61    spl4_4),
% 1.52/0.61    inference(avatar_split_clause,[],[f53,f111])).
% 1.52/0.61  fof(f53,plain,(
% 1.52/0.61    v1_funct_1(sK1)),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f109,plain,(
% 1.52/0.61    spl4_3),
% 1.52/0.61    inference(avatar_split_clause,[],[f54,f106])).
% 1.52/0.61  fof(f54,plain,(
% 1.52/0.61    v1_funct_2(sK1,sK0,sK0)),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f104,plain,(
% 1.52/0.61    spl4_2),
% 1.52/0.61    inference(avatar_split_clause,[],[f55,f101])).
% 1.52/0.61  fof(f55,plain,(
% 1.52/0.61    v3_funct_2(sK1,sK0,sK0)),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  fof(f99,plain,(
% 1.52/0.61    spl4_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f56,f96])).
% 1.52/0.61  fof(f56,plain,(
% 1.52/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.52/0.61    inference(cnf_transformation,[],[f24])).
% 1.52/0.61  % SZS output end Proof for theBenchmark
% 1.52/0.61  % (17387)------------------------------
% 1.52/0.61  % (17387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.61  % (17387)Termination reason: Refutation
% 1.52/0.61  
% 1.52/0.61  % (17387)Memory used [KB]: 11385
% 1.52/0.61  % (17387)Time elapsed: 0.173 s
% 1.52/0.61  % (17387)------------------------------
% 1.52/0.61  % (17387)------------------------------
% 1.52/0.61  % (17370)Success in time 0.244 s
%------------------------------------------------------------------------------
