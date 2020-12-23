%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t152_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:32 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  406 (1257 expanded)
%              Number of leaves         :  106 ( 522 expanded)
%              Depth                    :   15
%              Number of atoms          : 1323 (3999 expanded)
%              Number of equality atoms :   45 ( 155 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1086,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f95,f102,f109,f116,f123,f130,f137,f144,f151,f158,f165,f181,f188,f195,f215,f225,f230,f232,f234,f250,f252,f263,f275,f307,f320,f333,f354,f372,f377,f395,f400,f418,f431,f443,f457,f477,f495,f508,f526,f541,f545,f556,f564,f586,f603,f609,f629,f658,f660,f674,f682,f690,f693,f710,f711,f747,f765,f785,f804,f824,f834,f849,f868,f871,f889,f960,f986,f994,f1001,f1008,f1014,f1037,f1045,f1051,f1073,f1081,f1085])).

fof(f1085,plain,
    ( ~ spl5_30
    | ~ spl5_34
    | ~ spl5_78
    | spl5_161 ),
    inference(avatar_contradiction_clause,[],[f1084])).

fof(f1084,plain,
    ( $false
    | ~ spl5_30
    | ~ spl5_34
    | ~ spl5_78
    | ~ spl5_161 ),
    inference(subsumption_resolution,[],[f1083,f476])).

fof(f476,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl5_78
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1083,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ spl5_30
    | ~ spl5_34
    | ~ spl5_161 ),
    inference(subsumption_resolution,[],[f1082,f214])).

fof(f214,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl5_30
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1082,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl5_34
    | ~ spl5_161 ),
    inference(resolution,[],[f1080,f224])).

fof(f224,plain,
    ( ! [X0] :
        ( r1_partfun1(X0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl5_34
  <=> ! [X0] :
        ( r1_partfun1(X0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1080,plain,
    ( ~ r1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_161 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f1079,plain,
    ( spl5_161
  <=> ~ r1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f1081,plain,
    ( ~ spl5_161
    | spl5_13
    | ~ spl5_60
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1065,f393,f370,f128,f1079])).

fof(f128,plain,
    ( spl5_13
  <=> ~ r1_partfun1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f370,plain,
    ( spl5_60
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f393,plain,
    ( spl5_64
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1065,plain,
    ( ~ r1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_60
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f1054,f371])).

fof(f371,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1054,plain,
    ( ~ r1_partfun1(sK1,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_64 ),
    inference(superposition,[],[f129,f394])).

fof(f394,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f393])).

fof(f129,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f1073,plain,
    ( spl5_52
    | ~ spl5_6
    | ~ spl5_158 ),
    inference(avatar_split_clause,[],[f1046,f1043,f107,f318])).

fof(f318,plain,
    ( spl5_52
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f107,plain,
    ( spl5_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1043,plain,
    ( spl5_158
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f1046,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_6
    | ~ spl5_158 ),
    inference(resolution,[],[f1044,f200])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f69,f108])).

fof(f108,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',cc4_relset_1)).

fof(f1044,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_158 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1051,plain,
    ( ~ spl5_6
    | spl5_53
    | ~ spl5_158 ),
    inference(avatar_contradiction_clause,[],[f1050])).

fof(f1050,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_53
    | ~ spl5_158 ),
    inference(subsumption_resolution,[],[f1046,f316])).

fof(f316,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl5_53
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f1045,plain,
    ( spl5_158
    | ~ spl5_20
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f964,f524,f156,f1043])).

fof(f156,plain,
    ( spl5_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f524,plain,
    ( spl5_86
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f964,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_20
    | ~ spl5_86 ),
    inference(superposition,[],[f157,f525])).

fof(f525,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f524])).

fof(f157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f1037,plain,
    ( spl5_48
    | ~ spl5_6
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1009,f1006,f107,f305])).

fof(f305,plain,
    ( spl5_48
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1006,plain,
    ( spl5_156
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f1009,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_6
    | ~ spl5_156 ),
    inference(resolution,[],[f1007,f200])).

fof(f1007,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_156 ),
    inference(avatar_component_clause,[],[f1006])).

fof(f1014,plain,
    ( ~ spl5_6
    | spl5_49
    | ~ spl5_156 ),
    inference(avatar_contradiction_clause,[],[f1013])).

fof(f1013,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_49
    | ~ spl5_156 ),
    inference(subsumption_resolution,[],[f1009,f303])).

fof(f303,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl5_49
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1008,plain,
    ( spl5_156
    | ~ spl5_18
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f963,f524,f149,f1006])).

fof(f149,plain,
    ( spl5_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f963,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_18
    | ~ spl5_86 ),
    inference(superposition,[],[f150,f525])).

fof(f150,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1001,plain,
    ( ~ spl5_155
    | spl5_81
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f973,f524,f490,f999])).

fof(f999,plain,
    ( spl5_155
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f490,plain,
    ( spl5_81
  <=> k2_zfmisc_1(sK0,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f973,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | ~ spl5_81
    | ~ spl5_86 ),
    inference(superposition,[],[f491,f525])).

fof(f491,plain,
    ( k2_zfmisc_1(sK0,sK0) != k1_xboole_0
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f490])).

fof(f994,plain,
    ( ~ spl5_153
    | spl5_75
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f972,f524,f449,f992])).

fof(f992,plain,
    ( spl5_153
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f449,plain,
    ( spl5_75
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f972,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_75
    | ~ spl5_86 ),
    inference(superposition,[],[f450,f525])).

fof(f450,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f449])).

fof(f986,plain,
    ( spl5_150
    | ~ spl5_16
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f962,f524,f142,f984])).

fof(f984,plain,
    ( spl5_150
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f142,plain,
    ( spl5_16
  <=> v1_funct_2(sK3,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f962,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_16
    | ~ spl5_86 ),
    inference(superposition,[],[f143,f525])).

fof(f143,plain,
    ( v1_funct_2(sK3,sK0,sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f960,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_10
    | spl5_13
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f958,f122])).

fof(f122,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_10
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f958,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f957,f129])).

fof(f957,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f953,f157])).

fof(f953,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r1_partfun1(sK1,sK2)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(resolution,[],[f948,f94])).

fof(f94,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f948,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r1_partfun1(sK1,X0)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f947,f150])).

fof(f947,plain,
    ( ! [X0] :
        ( r1_partfun1(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f944,f115])).

fof(f115,plain,
    ( r1_partfun1(sK1,sK3)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_8
  <=> r1_partfun1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f944,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK1,sK3)
        | r1_partfun1(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(resolution,[],[f805,f87])).

fof(f87,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_0
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f805,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK3)
        | r1_partfun1(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl5_4
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(resolution,[],[f588,f164])).

fof(f164,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f588,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ r1_partfun1(X1,sK3)
        | ~ r1_partfun1(X0,sK3)
        | r1_partfun1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_4
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f587,f101])).

fof(f101,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f587,plain,
    ( ! [X2,X0,X1] :
        ( r1_partfun1(X0,X1)
        | ~ r1_partfun1(X1,sK3)
        | ~ r1_partfun1(X0,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_84 ),
    inference(resolution,[],[f78,f507])).

fof(f507,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl5_84
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_partfun1(X4,X0)
      | r1_partfun1(X2,X3)
      | ~ r1_partfun1(X3,X4)
      | ~ r1_partfun1(X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X4) )
             => ( ( v1_partfun1(X4,X0)
                  & r1_partfun1(X3,X4)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',t158_partfun1)).

fof(f889,plain,
    ( ~ spl5_149
    | ~ spl5_120
    | spl5_143 ),
    inference(avatar_split_clause,[],[f875,f829,f763,f887])).

fof(f887,plain,
    ( spl5_149
  <=> ~ v1_xboole_0(sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f763,plain,
    ( spl5_120
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f829,plain,
    ( spl5_143
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f875,plain,
    ( ~ v1_xboole_0(sK4(k1_xboole_0))
    | ~ spl5_120
    | ~ spl5_143 ),
    inference(superposition,[],[f830,f764])).

fof(f764,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f763])).

fof(f830,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_143 ),
    inference(avatar_component_clause,[],[f829])).

fof(f871,plain,(
    ~ spl5_140 ),
    inference(avatar_contradiction_clause,[],[f869])).

fof(f869,plain,
    ( $false
    | ~ spl5_140 ),
    inference(resolution,[],[f827,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',existence_m1_subset_1)).

fof(f827,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_140 ),
    inference(avatar_component_clause,[],[f826])).

fof(f826,plain,
    ( spl5_140
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f868,plain,
    ( spl5_146
    | ~ spl5_6
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f856,f832,f107,f866])).

fof(f866,plain,
    ( spl5_146
  <=> k1_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f832,plain,
    ( spl5_142
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f856,plain,
    ( k1_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_6
    | ~ spl5_142 ),
    inference(forward_demodulation,[],[f850,f205])).

fof(f205,plain,
    ( ! [X8] : k1_xboole_0 = sK4(k1_zfmisc_1(k2_zfmisc_1(X8,k1_xboole_0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f201,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',t6_boole)).

fof(f201,plain,
    ( ! [X0] : v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))))
    | ~ spl5_6 ),
    inference(resolution,[],[f200,f66])).

fof(f850,plain,
    ( ! [X0] : sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_142 ),
    inference(resolution,[],[f833,f204])).

fof(f204,plain,
    ( ! [X6,X7] :
        ( ~ v1_xboole_0(X7)
        | sK4(k1_zfmisc_1(k2_zfmisc_1(X6,k1_xboole_0))) = X7 )
    | ~ spl5_6 ),
    inference(resolution,[],[f201,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',t8_boole)).

fof(f833,plain,
    ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f832])).

fof(f849,plain,
    ( spl5_144
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f839,f763,f847])).

fof(f847,plain,
    ( spl5_144
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f839,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_120 ),
    inference(superposition,[],[f66,f764])).

fof(f834,plain,
    ( spl5_140
    | spl5_142
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f766,f739,f832,f826])).

fof(f739,plain,
    ( spl5_116
  <=> ! [X6] : ~ r2_hidden(X6,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f766,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
        | ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl5_116 ),
    inference(resolution,[],[f740,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',t2_subset)).

fof(f740,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_116 ),
    inference(avatar_component_clause,[],[f739])).

fof(f824,plain,
    ( spl5_134
    | ~ spl5_137
    | spl5_138
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f724,f607,f822,f816,f810])).

fof(f810,plain,
    ( spl5_134
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f816,plain,
    ( spl5_137
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK4(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f822,plain,
    ( spl5_138
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f607,plain,
    ( spl5_102
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f724,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK3)))
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK4(k1_zfmisc_1(sK3))))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK3))))
    | ~ spl5_102 ),
    inference(resolution,[],[f712,f608])).

fof(f608,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f607])).

fof(f712,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK4(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f344,f66])).

fof(f344,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,sK4(k1_zfmisc_1(X7)))
      | v1_xboole_0(sK4(k1_zfmisc_1(X7)))
      | m1_subset_1(X6,X7) ) ),
    inference(resolution,[],[f218,f66])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f79,f72])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',t4_subset)).

fof(f804,plain,
    ( spl5_128
    | ~ spl5_131
    | spl5_132
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f723,f543,f802,f796,f790])).

fof(f790,plain,
    ( spl5_128
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f796,plain,
    ( spl5_131
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK4(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f802,plain,
    ( spl5_132
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f543,plain,
    ( spl5_92
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f723,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK4(k1_zfmisc_1(sK2))))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK2))))
    | ~ spl5_92 ),
    inference(resolution,[],[f712,f544])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f543])).

fof(f785,plain,
    ( spl5_122
    | ~ spl5_125
    | spl5_126
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f722,f455,f783,f777,f771])).

fof(f771,plain,
    ( spl5_122
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f777,plain,
    ( spl5_125
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK4(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f783,plain,
    ( spl5_126
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f455,plain,
    ( spl5_76
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f722,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK4(k1_zfmisc_1(sK1))))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK1))))
    | ~ spl5_76 ),
    inference(resolution,[],[f712,f456])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f455])).

fof(f765,plain,
    ( spl5_120
    | ~ spl5_6
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f754,f745,f107,f763])).

fof(f745,plain,
    ( spl5_118
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f754,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f748,f205])).

fof(f748,plain,
    ( ! [X0] : sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_118 ),
    inference(resolution,[],[f746,f204])).

fof(f746,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f745])).

fof(f747,plain,
    ( spl5_116
    | spl5_118
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f720,f107,f745,f739])).

fof(f720,plain,
    ( ! [X6] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X6,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f712,f197])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f80,f108])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',t5_subset)).

fof(f711,plain,
    ( spl5_74
    | spl5_92
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f589,f375,f543,f452])).

fof(f452,plain,
    ( spl5_74
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f375,plain,
    ( spl5_62
  <=> ! [X4] :
        ( m1_subset_1(X4,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f589,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0) )
    | ~ spl5_62 ),
    inference(resolution,[],[f376,f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f169,f72])).

fof(f169,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f72,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',antisymmetry_r2_hidden)).

fof(f376,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X4,sK2) )
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f375])).

fof(f710,plain,
    ( spl5_112
    | ~ spl5_115
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f697,f607,f708,f702])).

fof(f702,plain,
    ( spl5_112
  <=> v1_xboole_0(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f708,plain,
    ( spl5_115
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f697,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK3))
    | v1_xboole_0(sK4(sK3))
    | ~ spl5_102 ),
    inference(resolution,[],[f608,f66])).

fof(f693,plain,
    ( spl5_110
    | ~ spl5_4
    | ~ spl5_28
    | ~ spl5_30
    | ~ spl5_78
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f692,f562,f475,f213,f193,f100,f688])).

fof(f688,plain,
    ( spl5_110
  <=> r1_partfun1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f193,plain,
    ( spl5_28
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f562,plain,
    ( spl5_94
  <=> r1_partfun1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f692,plain,
    ( r1_partfun1(sK3,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_28
    | ~ spl5_30
    | ~ spl5_78
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f691,f194])).

fof(f194,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f193])).

fof(f691,plain,
    ( ~ v1_relat_1(sK3)
    | r1_partfun1(sK3,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_30
    | ~ spl5_78
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f675,f101])).

fof(f675,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r1_partfun1(sK3,k1_xboole_0)
    | ~ spl5_30
    | ~ spl5_78
    | ~ spl5_94 ),
    inference(resolution,[],[f563,f565])).

fof(f565,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(k1_xboole_0,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r1_partfun1(X0,k1_xboole_0) )
    | ~ spl5_30
    | ~ spl5_78 ),
    inference(subsumption_resolution,[],[f557,f214])).

fof(f557,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(k1_xboole_0,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r1_partfun1(X0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_78 ),
    inference(resolution,[],[f476,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_partfun1(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( r1_partfun1(X0,X1)
       => r1_partfun1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',symmetry_r1_partfun1)).

fof(f563,plain,
    ( r1_partfun1(k1_xboole_0,sK3)
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f562])).

fof(f690,plain,
    ( spl5_110
    | ~ spl5_60
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f669,f429,f370,f688])).

fof(f429,plain,
    ( spl5_70
  <=> r1_partfun1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f669,plain,
    ( r1_partfun1(sK3,k1_xboole_0)
    | ~ spl5_60
    | ~ spl5_70 ),
    inference(superposition,[],[f430,f371])).

fof(f430,plain,
    ( r1_partfun1(sK3,sK1)
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f429])).

fof(f682,plain,
    ( ~ spl5_109
    | spl5_13
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f664,f370,f128,f680])).

fof(f680,plain,
    ( spl5_109
  <=> ~ r1_partfun1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f664,plain,
    ( ~ r1_partfun1(k1_xboole_0,sK2)
    | ~ spl5_13
    | ~ spl5_60 ),
    inference(superposition,[],[f129,f371])).

fof(f674,plain,
    ( spl5_94
    | ~ spl5_8
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f663,f370,f114,f562])).

fof(f663,plain,
    ( r1_partfun1(k1_xboole_0,sK3)
    | ~ spl5_8
    | ~ spl5_60 ),
    inference(superposition,[],[f115,f371])).

fof(f660,plain,
    ( ~ spl5_38
    | ~ spl5_40
    | spl5_49
    | ~ spl5_96 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | ~ spl5_38
    | ~ spl5_40
    | ~ spl5_49
    | ~ spl5_96 ),
    inference(resolution,[],[f637,f66])).

fof(f637,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK1)
    | ~ spl5_38
    | ~ spl5_40
    | ~ spl5_49
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f633,f303])).

fof(f633,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl5_38
    | ~ spl5_40
    | ~ spl5_96 ),
    inference(resolution,[],[f585,f288])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f287,f262])).

fof(f262,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl5_40
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0))))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_38 ),
    inference(resolution,[],[f254,f72])).

fof(f254,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl5_38 ),
    inference(resolution,[],[f249,f80])).

fof(f249,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_38
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f585,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl5_96
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f658,plain,
    ( spl5_106
    | ~ spl5_20
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f569,f493,f156,f656])).

fof(f656,plain,
    ( spl5_106
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f493,plain,
    ( spl5_80
  <=> k2_zfmisc_1(sK0,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f569,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_80 ),
    inference(superposition,[],[f157,f494])).

fof(f494,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_xboole_0
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f493])).

fof(f629,plain,
    ( spl5_104
    | ~ spl5_8
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f612,f416,f114,f627])).

fof(f627,plain,
    ( spl5_104
  <=> r1_partfun1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f416,plain,
    ( spl5_68
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f612,plain,
    ( r1_partfun1(sK1,k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_68 ),
    inference(superposition,[],[f115,f417])).

fof(f417,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f416])).

fof(f609,plain,
    ( spl5_74
    | spl5_102
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f419,f398,f607,f452])).

fof(f398,plain,
    ( spl5_66
  <=> ! [X5] :
        ( m1_subset_1(X5,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X5,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f419,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0) )
    | ~ spl5_66 ),
    inference(resolution,[],[f399,f196])).

fof(f399,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X5,sK3) )
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f398])).

fof(f603,plain,
    ( spl5_98
    | ~ spl5_101
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f590,f543,f601,f595])).

fof(f595,plain,
    ( spl5_98
  <=> v1_xboole_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f601,plain,
    ( spl5_101
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f590,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK2))
    | v1_xboole_0(sK4(sK2))
    | ~ spl5_92 ),
    inference(resolution,[],[f544,f66])).

fof(f586,plain,
    ( spl5_96
    | ~ spl5_18
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f568,f493,f149,f584])).

fof(f568,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_80 ),
    inference(superposition,[],[f150,f494])).

fof(f564,plain,
    ( spl5_94
    | ~ spl5_10
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f548,f393,f121,f562])).

fof(f548,plain,
    ( r1_partfun1(k1_xboole_0,sK3)
    | ~ spl5_10
    | ~ spl5_64 ),
    inference(superposition,[],[f122,f394])).

fof(f556,plain,
    ( spl5_78
    | ~ spl5_2
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f547,f393,f93,f475])).

fof(f547,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_64 ),
    inference(superposition,[],[f94,f394])).

fof(f545,plain,
    ( spl5_74
    | spl5_92
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f396,f375,f543,f452])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0) )
    | ~ spl5_62 ),
    inference(resolution,[],[f376,f196])).

fof(f541,plain,
    ( spl5_88
    | ~ spl5_91
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f528,f455,f539,f533])).

fof(f533,plain,
    ( spl5_88
  <=> v1_xboole_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f539,plain,
    ( spl5_91
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f528,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(sK1))
    | v1_xboole_0(sK4(sK1))
    | ~ spl5_76 ),
    inference(resolution,[],[f456,f66])).

fof(f526,plain,
    ( spl5_86
    | ~ spl5_6
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f515,f500,f107,f524])).

fof(f500,plain,
    ( spl5_82
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f515,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_6
    | ~ spl5_82 ),
    inference(forward_demodulation,[],[f509,f205])).

fof(f509,plain,
    ( ! [X0] : sK0 = sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_82 ),
    inference(resolution,[],[f501,f204])).

fof(f501,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f500])).

fof(f508,plain,
    ( spl5_82
    | spl5_84
    | ~ spl5_4
    | ~ spl5_16
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f470,f163,f142,f100,f506,f500])).

fof(f470,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK0)
    | ~ spl5_4
    | ~ spl5_16
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f469,f164])).

fof(f469,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f468,f101])).

fof(f468,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f68,f143])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',cc5_funct_2)).

fof(f495,plain,
    ( spl5_80
    | ~ spl5_6
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f484,f452,f107,f493])).

fof(f484,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_xboole_0
    | ~ spl5_6
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f478,f205])).

fof(f478,plain,
    ( ! [X0] : k2_zfmisc_1(sK0,sK0) = sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_74 ),
    inference(resolution,[],[f453,f204])).

fof(f453,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f452])).

fof(f477,plain,
    ( spl5_78
    | ~ spl5_0
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f459,f370,f86,f475])).

fof(f459,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_0
    | ~ spl5_60 ),
    inference(superposition,[],[f87,f371])).

fof(f457,plain,
    ( spl5_74
    | spl5_76
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f373,f352,f455,f452])).

fof(f352,plain,
    ( spl5_58
  <=> ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f373,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0) )
    | ~ spl5_58 ),
    inference(resolution,[],[f353,f196])).

fof(f353,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f352])).

fof(f443,plain,
    ( spl5_72
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f436,f193,f186,f121,f100,f93,f441])).

fof(f441,plain,
    ( spl5_72
  <=> r1_partfun1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f186,plain,
    ( spl5_26
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f436,plain,
    ( r1_partfun1(sK3,sK2)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f435,f194])).

fof(f435,plain,
    ( ~ v1_relat_1(sK3)
    | r1_partfun1(sK3,sK2)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f432,f101])).

fof(f432,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r1_partfun1(sK3,sK2)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(resolution,[],[f349,f122])).

fof(f349,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(sK2,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK2) )
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f346,f187])).

fof(f187,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f186])).

fof(f346,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(sK2,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | r1_partfun1(X1,sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f94])).

fof(f431,plain,
    ( spl5_70
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f424,f193,f179,f114,f100,f86,f429])).

fof(f179,plain,
    ( spl5_24
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f424,plain,
    ( r1_partfun1(sK3,sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f423,f194])).

fof(f423,plain,
    ( ~ v1_relat_1(sK3)
    | r1_partfun1(sK3,sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f420,f101])).

fof(f420,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r1_partfun1(sK3,sK1)
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(resolution,[],[f348,f115])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r1_partfun1(X0,sK1) )
    | ~ spl5_0
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f345,f180])).

fof(f180,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f179])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r1_partfun1(X0,sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_0 ),
    inference(resolution,[],[f74,f87])).

fof(f418,plain,
    ( spl5_68
    | ~ spl5_6
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f407,f331,f107,f416])).

fof(f331,plain,
    ( spl5_56
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f407,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_6
    | ~ spl5_56 ),
    inference(forward_demodulation,[],[f401,f205])).

fof(f401,plain,
    ( ! [X0] : sK3 = sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_56 ),
    inference(resolution,[],[f332,f204])).

fof(f332,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f331])).

fof(f400,plain,
    ( spl5_56
    | spl5_66
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f343,f163,f398,f331])).

fof(f343,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,k2_zfmisc_1(sK0,sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X5,sK3) )
    | ~ spl5_22 ),
    inference(resolution,[],[f218,f164])).

fof(f395,plain,
    ( spl5_64
    | ~ spl5_6
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f384,f318,f107,f393])).

fof(f384,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_6
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f378,f205])).

fof(f378,plain,
    ( ! [X0] : sK2 = sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_52 ),
    inference(resolution,[],[f319,f204])).

fof(f319,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f318])).

fof(f377,plain,
    ( spl5_52
    | spl5_62
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f342,f156,f375,f318])).

fof(f342,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,k2_zfmisc_1(sK0,sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X4,sK2) )
    | ~ spl5_20 ),
    inference(resolution,[],[f218,f157])).

fof(f372,plain,
    ( spl5_60
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f361,f305,f107,f370])).

fof(f361,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f355,f205])).

fof(f355,plain,
    ( ! [X0] : sK1 = sK4(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(resolution,[],[f306,f204])).

fof(f306,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f305])).

fof(f354,plain,
    ( spl5_48
    | spl5_58
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f341,f149,f352,f305])).

fof(f341,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(sK0,sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl5_18 ),
    inference(resolution,[],[f218,f150])).

fof(f333,plain,
    ( ~ spl5_55
    | spl5_46
    | spl5_56
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f238,f163,f331,f299,f325])).

fof(f325,plain,
    ( spl5_55
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f299,plain,
    ( spl5_46
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f238,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK3)
    | ~ spl5_22 ),
    inference(resolution,[],[f196,f164])).

fof(f320,plain,
    ( ~ spl5_51
    | spl5_46
    | spl5_52
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f237,f156,f318,f299,f312])).

fof(f312,plain,
    ( spl5_51
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f237,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2)
    | ~ spl5_20 ),
    inference(resolution,[],[f196,f157])).

fof(f307,plain,
    ( ~ spl5_45
    | spl5_46
    | spl5_48
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f236,f149,f305,f299,f293])).

fof(f293,plain,
    ( spl5_45
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f236,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl5_18 ),
    inference(resolution,[],[f196,f150])).

fof(f275,plain,
    ( spl5_42
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f267,f261,f273])).

fof(f273,plain,
    ( spl5_42
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f267,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_40 ),
    inference(superposition,[],[f66,f262])).

fof(f263,plain,
    ( spl5_40
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f256,f248,f261])).

fof(f256,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38 ),
    inference(resolution,[],[f249,f65])).

fof(f252,plain,(
    ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl5_36 ),
    inference(resolution,[],[f243,f66])).

fof(f243,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl5_36
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f250,plain,
    ( spl5_36
    | spl5_38
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f199,f107,f248,f242])).

fof(f199,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X0,sK4(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f198,f72])).

fof(f198,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f197,f66])).

fof(f234,plain,
    ( ~ spl5_4
    | ~ spl5_28
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_28
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f228,f194])).

fof(f228,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_4
    | ~ spl5_32 ),
    inference(resolution,[],[f221,f101])).

fof(f221,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_32
  <=> ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f232,plain,
    ( ~ spl5_2
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f227,f187])).

fof(f227,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_2
    | ~ spl5_32 ),
    inference(resolution,[],[f221,f94])).

fof(f230,plain,
    ( ~ spl5_0
    | ~ spl5_24
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_24
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f226,f180])).

fof(f226,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl5_0
    | ~ spl5_32 ),
    inference(resolution,[],[f221,f87])).

fof(f225,plain,
    ( spl5_32
    | spl5_34 ),
    inference(avatar_split_clause,[],[f73,f223,f220])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_partfun1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',reflexivity_r1_partfun1)).

fof(f215,plain,
    ( spl5_30
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f207,f107,f213])).

fof(f207,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_6 ),
    inference(superposition,[],[f174,f205])).

fof(f174,plain,(
    ! [X0,X1] : v1_relat_1(sK4(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ),
    inference(resolution,[],[f77,f66])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',cc1_relset_1)).

fof(f195,plain,
    ( spl5_28
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f173,f163,f193])).

fof(f173,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_22 ),
    inference(resolution,[],[f77,f164])).

fof(f188,plain,
    ( spl5_26
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f172,f156,f186])).

fof(f172,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_20 ),
    inference(resolution,[],[f77,f157])).

fof(f181,plain,
    ( spl5_24
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f171,f149,f179])).

fof(f171,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_18 ),
    inference(resolution,[],[f77,f150])).

fof(f165,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f59,f163])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_partfun1(sK1,sK2)
    & r1_partfun1(sK2,sK3)
    & r1_partfun1(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK3,sK0,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_partfun1(X1,X2)
                & r1_partfun1(X2,X3)
                & r1_partfun1(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(sK1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(sK1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
              & v1_funct_2(X3,sK0,sK0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ r1_partfun1(X1,sK2)
            & r1_partfun1(sK2,X3)
            & r1_partfun1(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X3,X0,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_partfun1(X1,X2)
          & r1_partfun1(X2,X3)
          & r1_partfun1(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X3,X0,X0)
          & v1_funct_1(X3) )
     => ( ~ r1_partfun1(X1,X2)
        & r1_partfun1(X2,sK3)
        & r1_partfun1(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                  & v1_funct_2(X3,X0,X0)
                  & v1_funct_1(X3) )
               => ( ( r1_partfun1(X2,X3)
                    & r1_partfun1(X1,X3) )
                 => r1_partfun1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
             => ( ( r1_partfun1(X2,X3)
                  & r1_partfun1(X1,X3) )
               => r1_partfun1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',t152_funct_2)).

fof(f158,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f56,f156])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f151,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f54,f149])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f144,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f58,f142])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f137,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f64,f135])).

fof(f135,plain,
    ( spl5_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f64,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',d2_xboole_0)).

fof(f130,plain,(
    ~ spl5_13 ),
    inference(avatar_split_clause,[],[f62,f128])).

fof(f62,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f123,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f61,f121])).

fof(f61,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f109,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f81,f107])).

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f63,f64])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t152_funct_2.p',dt_o_0_0_xboole_0)).

fof(f102,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f57,f100])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f95,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f55,f93])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f53,f86])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
