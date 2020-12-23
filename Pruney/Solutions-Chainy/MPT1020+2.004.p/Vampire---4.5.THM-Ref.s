%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  295 ( 620 expanded)
%              Number of leaves         :   66 ( 274 expanded)
%              Depth                    :   12
%              Number of atoms          : 1089 (2498 expanded)
%              Number of equality atoms :  124 ( 307 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f149,f160,f199,f204,f240,f275,f282,f288,f293,f314,f387,f406,f419,f444,f468,f477,f497,f543,f557,f671,f735,f784,f821,f851,f861,f892,f909,f914,f1013,f1028,f1038,f1053,f1087,f1092,f1274,f1287,f1297,f1313,f1367])).

fof(f1367,plain,
    ( ~ spl3_23
    | ~ spl3_36
    | spl3_114
    | ~ spl3_133 ),
    inference(avatar_contradiction_clause,[],[f1366])).

fof(f1366,plain,
    ( $false
    | ~ spl3_23
    | ~ spl3_36
    | spl3_114
    | ~ spl3_133 ),
    inference(subsumption_resolution,[],[f1351,f386])).

fof(f386,plain,
    ( ! [X0] : r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl3_36
  <=> ! [X0] : r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f1351,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_23
    | spl3_114
    | ~ spl3_133 ),
    inference(backward_demodulation,[],[f1091,f1317])).

fof(f1317,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_133 ),
    inference(resolution,[],[f1312,f274])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl3_23
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1312,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_133 ),
    inference(avatar_component_clause,[],[f1310])).

fof(f1310,plain,
    ( spl3_133
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).

fof(f1091,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | spl3_114 ),
    inference(avatar_component_clause,[],[f1089])).

fof(f1089,plain,
    ( spl3_114
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f1313,plain,
    ( spl3_133
    | ~ spl3_24
    | ~ spl3_132 ),
    inference(avatar_split_clause,[],[f1305,f1294,f278,f1310])).

fof(f278,plain,
    ( spl3_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1294,plain,
    ( spl3_132
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_132])])).

fof(f1305,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_24
    | ~ spl3_132 ),
    inference(resolution,[],[f1296,f279])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f1296,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_132 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1297,plain,
    ( spl3_132
    | ~ spl3_29
    | ~ spl3_106
    | ~ spl3_108
    | ~ spl3_128
    | ~ spl3_131 ),
    inference(avatar_split_clause,[],[f1292,f1277,f1260,f1035,f1025,f311,f1294])).

fof(f311,plain,
    ( spl3_29
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f1025,plain,
    ( spl3_106
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).

fof(f1035,plain,
    ( spl3_108
  <=> v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).

fof(f1260,plain,
    ( spl3_128
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(k1_xboole_0,X0,X0)
        | ~ v1_funct_2(k1_xboole_0,X0,X0)
        | m1_subset_1(k2_funct_2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).

fof(f1277,plain,
    ( spl3_131
  <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).

fof(f1292,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_29
    | ~ spl3_106
    | ~ spl3_108
    | ~ spl3_128
    | ~ spl3_131 ),
    inference(forward_demodulation,[],[f1285,f1279])).

fof(f1279,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ spl3_131 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1285,plain,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_29
    | ~ spl3_106
    | ~ spl3_108
    | ~ spl3_128 ),
    inference(forward_demodulation,[],[f1284,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f1284,plain,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_29
    | ~ spl3_106
    | ~ spl3_108
    | ~ spl3_128 ),
    inference(subsumption_resolution,[],[f1283,f313])).

fof(f313,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f311])).

fof(f1283,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_106
    | ~ spl3_108
    | ~ spl3_128 ),
    inference(forward_demodulation,[],[f1282,f87])).

fof(f1282,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_106
    | ~ spl3_108
    | ~ spl3_128 ),
    inference(subsumption_resolution,[],[f1281,f1037])).

fof(f1037,plain,
    ( v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_108 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f1281,plain,
    ( ~ v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_106
    | ~ spl3_128 ),
    inference(resolution,[],[f1261,f1027])).

fof(f1027,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_106 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1261,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,X0,X0)
        | ~ v3_funct_2(k1_xboole_0,X0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | m1_subset_1(k2_funct_2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl3_128 ),
    inference(avatar_component_clause,[],[f1260])).

fof(f1287,plain,
    ( spl3_131
    | ~ spl3_59
    | ~ spl3_74
    | ~ spl3_113 ),
    inference(avatar_split_clause,[],[f1258,f1084,f668,f554,f1277])).

fof(f554,plain,
    ( spl3_59
  <=> k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f668,plain,
    ( spl3_74
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f1084,plain,
    ( spl3_113
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).

fof(f1258,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ spl3_59
    | ~ spl3_74
    | ~ spl3_113 ),
    inference(forward_demodulation,[],[f1257,f670])).

fof(f670,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f668])).

fof(f1257,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(sK0,k1_xboole_0)
    | ~ spl3_59
    | ~ spl3_113 ),
    inference(forward_demodulation,[],[f556,f1086])).

fof(f1086,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_113 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f556,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f554])).

fof(f1274,plain,
    ( spl3_128
    | ~ spl3_23
    | ~ spl3_57
    | ~ spl3_90
    | ~ spl3_104 ),
    inference(avatar_split_clause,[],[f1256,f1010,f889,f541,f273,f1260])).

fof(f541,plain,
    ( spl3_57
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(sK1,X0,X0)
        | ~ v1_funct_2(sK1,X0,X0)
        | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f889,plain,
    ( spl3_90
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f1010,plain,
    ( spl3_104
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).

fof(f1256,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(k1_xboole_0,X0,X0)
        | ~ v1_funct_2(k1_xboole_0,X0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl3_23
    | ~ spl3_57
    | ~ spl3_90
    | ~ spl3_104 ),
    inference(forward_demodulation,[],[f1255,f1012])).

fof(f1012,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_104 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f1255,plain,
    ( ! [X0] :
        ( ~ v3_funct_2(k1_xboole_0,X0,X0)
        | ~ v1_funct_2(k1_xboole_0,X0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl3_23
    | ~ spl3_57
    | ~ spl3_90
    | ~ spl3_104 ),
    inference(forward_demodulation,[],[f1254,f1012])).

fof(f1254,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,X0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(sK1,X0,X0)
        | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl3_23
    | ~ spl3_57
    | ~ spl3_90
    | ~ spl3_104 ),
    inference(forward_demodulation,[],[f996,f1012])).

fof(f996,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_2(sK1,X0,X0)
        | ~ v3_funct_2(sK1,X0,X0)
        | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl3_23
    | ~ spl3_57
    | ~ spl3_90 ),
    inference(backward_demodulation,[],[f542,f901])).

fof(f901,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_23
    | ~ spl3_90 ),
    inference(resolution,[],[f891,f274])).

fof(f891,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_90 ),
    inference(avatar_component_clause,[],[f889])).

fof(f542,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,X0,X0)
        | ~ v3_funct_2(sK1,X0,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f541])).

fof(f1092,plain,
    ( ~ spl3_114
    | ~ spl3_23
    | ~ spl3_92
    | spl3_111 ),
    inference(avatar_split_clause,[],[f1082,f1050,f911,f273,f1089])).

fof(f911,plain,
    ( spl3_92
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f1050,plain,
    ( spl3_111
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).

fof(f1082,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl3_23
    | ~ spl3_92
    | spl3_111 ),
    inference(backward_demodulation,[],[f1052,f915])).

fof(f915,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_23
    | ~ spl3_92 ),
    inference(resolution,[],[f913,f274])).

fof(f913,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f911])).

fof(f1052,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))
    | spl3_111 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1087,plain,
    ( spl3_113
    | ~ spl3_23
    | ~ spl3_92 ),
    inference(avatar_split_clause,[],[f915,f911,f273,f1084])).

fof(f1053,plain,
    ( ~ spl3_111
    | ~ spl3_23
    | ~ spl3_90
    | spl3_91 ),
    inference(avatar_split_clause,[],[f1002,f906,f889,f273,f1050])).

fof(f906,plain,
    ( spl3_91
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f1002,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl3_23
    | ~ spl3_90
    | spl3_91 ),
    inference(backward_demodulation,[],[f908,f901])).

fof(f908,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))
    | spl3_91 ),
    inference(avatar_component_clause,[],[f906])).

fof(f1038,plain,
    ( spl3_108
    | ~ spl3_23
    | ~ spl3_80
    | ~ spl3_90 ),
    inference(avatar_split_clause,[],[f999,f889,f818,f273,f1035])).

fof(f818,plain,
    ( spl3_80
  <=> v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f999,plain,
    ( v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_80
    | ~ spl3_90 ),
    inference(backward_demodulation,[],[f820,f901])).

fof(f820,plain,
    ( v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f818])).

fof(f1028,plain,
    ( spl3_106
    | ~ spl3_23
    | ~ spl3_78
    | ~ spl3_90 ),
    inference(avatar_split_clause,[],[f998,f889,f732,f273,f1025])).

fof(f732,plain,
    ( spl3_78
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f998,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_78
    | ~ spl3_90 ),
    inference(backward_demodulation,[],[f734,f901])).

fof(f734,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f732])).

fof(f1013,plain,
    ( spl3_104
    | ~ spl3_23
    | ~ spl3_90 ),
    inference(avatar_split_clause,[],[f901,f889,f273,f1010])).

fof(f914,plain,
    ( spl3_92
    | ~ spl3_24
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f900,f858,f278,f911])).

fof(f858,plain,
    ( spl3_88
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f900,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_24
    | ~ spl3_88 ),
    inference(resolution,[],[f860,f279])).

fof(f860,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_88 ),
    inference(avatar_component_clause,[],[f858])).

fof(f909,plain,
    ( ~ spl3_91
    | spl3_51
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f811,f668,f494,f906])).

fof(f494,plain,
    ( spl3_51
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f811,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))
    | spl3_51
    | ~ spl3_74 ),
    inference(backward_demodulation,[],[f496,f670])).

fof(f496,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | spl3_51 ),
    inference(avatar_component_clause,[],[f494])).

fof(f892,plain,
    ( spl3_90
    | ~ spl3_24
    | ~ spl3_86 ),
    inference(avatar_split_clause,[],[f887,f848,f278,f889])).

fof(f848,plain,
    ( spl3_86
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f887,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_24
    | ~ spl3_86 ),
    inference(resolution,[],[f850,f279])).

fof(f850,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f848])).

fof(f861,plain,
    ( spl3_88
    | ~ spl3_9
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f815,f668,f132,f858])).

fof(f132,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f815,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f800,f87])).

fof(f800,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_9
    | ~ spl3_74 ),
    inference(backward_demodulation,[],[f134,f670])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f851,plain,
    ( spl3_86
    | ~ spl3_8
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f814,f668,f127,f848])).

fof(f127,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f814,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f799,f87])).

fof(f799,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_74 ),
    inference(backward_demodulation,[],[f129,f670])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f821,plain,
    ( spl3_80
    | ~ spl3_5
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f796,f668,f112,f818])).

fof(f112,plain,
    ( spl3_5
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f796,plain,
    ( v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_74 ),
    inference(backward_demodulation,[],[f114,f670])).

fof(f114,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f784,plain,
    ( ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_20
    | spl3_51
    | ~ spl3_73 ),
    inference(avatar_contradiction_clause,[],[f783])).

fof(f783,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_20
    | spl3_51
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f773,f239])).

fof(f239,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl3_20
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f773,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_17
    | spl3_51
    | ~ spl3_73 ),
    inference(backward_demodulation,[],[f496,f680])).

fof(f680,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f679,f134])).

fof(f679,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_17
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f678,f119])).

fof(f119,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f678,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f677,f99])).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f677,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_17
    | ~ spl3_73 ),
    inference(resolution,[],[f666,f203])).

fof(f203,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_17
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f666,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k2_funct_1(sK1) = X0 )
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f665])).

fof(f665,plain,
    ( spl3_73
  <=> ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k2_funct_1(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f735,plain,
    ( spl3_78
    | ~ spl3_4
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f690,f668,f107,f732])).

fof(f107,plain,
    ( spl3_4
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f690,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_74 ),
    inference(backward_demodulation,[],[f109,f670])).

fof(f109,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f671,plain,
    ( spl3_73
    | spl3_74
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f455,f441,f127,f107,f92,f668,f665])).

fof(f92,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f441,plain,
    ( spl3_45
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f455,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f454,f94])).

fof(f94,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f454,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f453,f109])).

fof(f453,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1) )
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f452,f129])).

fof(f452,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1) )
    | ~ spl3_45 ),
    inference(trivial_inequality_removal,[],[f451])).

fof(f451,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | k1_xboole_0 = sK0
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1) )
    | ~ spl3_45 ),
    inference(duplicate_literal_removal,[],[f450])).

fof(f450,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK0
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1) )
    | ~ spl3_45 ),
    inference(superposition,[],[f266,f443])).

fof(f443,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f441])).

fof(f266,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_funct_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f83,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f557,plain,
    ( spl3_59
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f510,f475,f132,f122,f117,f554])).

fof(f122,plain,
    ( spl3_7
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f475,plain,
    ( spl3_49
  <=> ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v3_funct_2(sK2,X1,X1)
        | ~ v1_funct_2(sK2,X1,X1)
        | k2_funct_2(X1,sK2) = k2_funct_1(sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f510,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f509,f134])).

fof(f509,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f508,f124])).

fof(f124,plain,
    ( v3_funct_2(sK2,sK0,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f508,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ spl3_6
    | ~ spl3_49 ),
    inference(resolution,[],[f476,f119])).

fof(f476,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,X1,X1)
        | ~ v3_funct_2(sK2,X1,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | k2_funct_2(X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f475])).

fof(f543,plain,
    ( spl3_57
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f243,f92,f541])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(sK1,X0,X0)
        | ~ v1_funct_2(sK1,X0,X0)
        | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f69,f94])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f497,plain,
    ( ~ spl3_51
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_10
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f487,f466,f137,f127,f112,f107,f494])).

fof(f137,plain,
    ( spl3_10
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f466,plain,
    ( spl3_47
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(sK1,X0,X0)
        | ~ v1_funct_2(sK1,X0,X0)
        | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f487,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_10
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f139,f485])).

fof(f485,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f484,f129])).

fof(f484,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f483,f114])).

fof(f483,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_4
    | ~ spl3_47 ),
    inference(resolution,[],[f467,f109])).

fof(f467,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,X0,X0)
        | ~ v3_funct_2(sK1,X0,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | k2_funct_2(X0,sK1) = k2_funct_1(sK1) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f466])).

fof(f139,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f477,plain,
    ( spl3_49
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f230,f97,f475])).

fof(f230,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v3_funct_2(sK2,X1,X1)
        | ~ v1_funct_2(sK2,X1,X1)
        | k2_funct_2(X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f65,f99])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f468,plain,
    ( spl3_47
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f229,f92,f466])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(sK1,X0,X0)
        | ~ v1_funct_2(sK1,X0,X0)
        | k2_funct_2(X0,sK1) = k2_funct_1(sK1) )
    | ~ spl3_1 ),
    inference(resolution,[],[f65,f94])).

fof(f444,plain,
    ( spl3_45
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_26
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f434,f416,f290,f196,f157,f441])).

fof(f157,plain,
    ( spl3_12
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f196,plain,
    ( spl3_16
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f290,plain,
    ( spl3_26
  <=> k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f416,plain,
    ( spl3_41
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f434,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_26
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f292,f430])).

fof(f430,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f216,f418])).

fof(f418,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f416])).

fof(f216,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | sK0 = k2_relat_1(sK1)
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f215,f159])).

fof(f159,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f215,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_16 ),
    inference(resolution,[],[f198,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f198,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f292,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f290])).

fof(f419,plain,
    ( spl3_41
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f414,f404,f127,f112,f416])).

fof(f404,plain,
    ( spl3_39
  <=> ! [X1,X0] :
        ( ~ v3_funct_2(sK1,X0,X1)
        | v2_funct_2(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f414,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f413,f129])).

fof(f413,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_5
    | ~ spl3_39 ),
    inference(resolution,[],[f405,f114])).

fof(f405,plain,
    ( ! [X0,X1] :
        ( ~ v3_funct_2(sK1,X0,X1)
        | v2_funct_2(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f404])).

fof(f406,plain,
    ( spl3_39
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f221,f92,f404])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ v3_funct_2(sK1,X0,X1)
        | v2_funct_2(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f80,f94])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f387,plain,
    ( spl3_36
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f355,f311,f385])).

fof(f355,plain,
    ( ! [X0] : r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_29 ),
    inference(resolution,[],[f194,f313])).

fof(f194,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | r2_relset_1(k1_xboole_0,X2,X3,X3) ) ),
    inference(superposition,[],[f90,f88])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f314,plain,
    ( spl3_29
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f304,f285,f273,f144,f311])).

fof(f144,plain,
    ( spl3_11
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f285,plain,
    ( spl3_25
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f304,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f146,f294])).

fof(f294,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(resolution,[],[f287,f274])).

fof(f287,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f285])).

fof(f146,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f293,plain,
    ( spl3_26
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f210,f127,f290])).

fof(f210,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f75,f129])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f288,plain,
    ( spl3_25
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f283,f278,f144,f285])).

fof(f283,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(resolution,[],[f279,f146])).

fof(f282,plain,
    ( spl3_24
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f177,f102,f278])).

fof(f102,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f176,f87])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f62,f104])).

fof(f104,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f275,plain,
    ( spl3_23
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f148,f102,f273])).

fof(f148,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f104])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f240,plain,
    ( spl3_20
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f191,f132,f237])).

fof(f191,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f90,f134])).

fof(f204,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f56,f201])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f199,plain,
    ( spl3_16
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f171,f127,f196])).

fof(f171,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f77,f129])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f160,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f151,f127,f157])).

fof(f151,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f74,f129])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f149,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f142,f144])).

fof(f142,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f60,f88])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f140,plain,(
    ~ spl3_10 ),
    inference(avatar_split_clause,[],[f57,f137])).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f135,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f55,f132])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f130,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f51,f127])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f125,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f54,f122])).

fof(f54,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f53,f117])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f112])).

fof(f50,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f49,f107])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f58,f102])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f100,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f52,f97])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:11:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (5818)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.49  % (5815)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (5811)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.49  % (5828)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (5833)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (5813)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (5829)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (5817)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (5812)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (5816)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (5825)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (5835)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (5827)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (5831)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (5836)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (5810)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (5819)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (5820)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (5822)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (5826)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (5832)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (5824)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (5823)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (5830)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (5834)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (5821)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.56  % (5812)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1368,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f149,f160,f199,f204,f240,f275,f282,f288,f293,f314,f387,f406,f419,f444,f468,f477,f497,f543,f557,f671,f735,f784,f821,f851,f861,f892,f909,f914,f1013,f1028,f1038,f1053,f1087,f1092,f1274,f1287,f1297,f1313,f1367])).
% 0.22/0.56  fof(f1367,plain,(
% 0.22/0.56    ~spl3_23 | ~spl3_36 | spl3_114 | ~spl3_133),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1366])).
% 0.22/0.56  fof(f1366,plain,(
% 0.22/0.56    $false | (~spl3_23 | ~spl3_36 | spl3_114 | ~spl3_133)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1351,f386])).
% 0.22/0.56  fof(f386,plain,(
% 0.22/0.56    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)) ) | ~spl3_36),
% 0.22/0.56    inference(avatar_component_clause,[],[f385])).
% 0.22/0.56  fof(f385,plain,(
% 0.22/0.56    spl3_36 <=> ! [X0] : r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.56  fof(f1351,plain,(
% 0.22/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_23 | spl3_114 | ~spl3_133)),
% 0.22/0.56    inference(backward_demodulation,[],[f1091,f1317])).
% 0.22/0.56  fof(f1317,plain,(
% 0.22/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_23 | ~spl3_133)),
% 0.22/0.56    inference(resolution,[],[f1312,f274])).
% 0.22/0.56  fof(f274,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_23),
% 0.22/0.56    inference(avatar_component_clause,[],[f273])).
% 0.22/0.56  fof(f273,plain,(
% 0.22/0.56    spl3_23 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.56  fof(f1312,plain,(
% 0.22/0.56    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl3_133),
% 0.22/0.56    inference(avatar_component_clause,[],[f1310])).
% 0.22/0.56  fof(f1310,plain,(
% 0.22/0.56    spl3_133 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).
% 0.22/0.56  fof(f1091,plain,(
% 0.22/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) | spl3_114),
% 0.22/0.56    inference(avatar_component_clause,[],[f1089])).
% 0.22/0.56  fof(f1089,plain,(
% 0.22/0.56    spl3_114 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 0.22/0.56  fof(f1313,plain,(
% 0.22/0.56    spl3_133 | ~spl3_24 | ~spl3_132),
% 0.22/0.56    inference(avatar_split_clause,[],[f1305,f1294,f278,f1310])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    spl3_24 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.56  fof(f1294,plain,(
% 0.22/0.56    spl3_132 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_132])])).
% 0.22/0.56  fof(f1305,plain,(
% 0.22/0.56    v1_xboole_0(k2_funct_1(k1_xboole_0)) | (~spl3_24 | ~spl3_132)),
% 0.22/0.56    inference(resolution,[],[f1296,f279])).
% 0.22/0.56  fof(f279,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl3_24),
% 0.22/0.56    inference(avatar_component_clause,[],[f278])).
% 0.22/0.56  fof(f1296,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_132),
% 0.22/0.56    inference(avatar_component_clause,[],[f1294])).
% 0.22/0.56  fof(f1297,plain,(
% 0.22/0.56    spl3_132 | ~spl3_29 | ~spl3_106 | ~spl3_108 | ~spl3_128 | ~spl3_131),
% 0.22/0.56    inference(avatar_split_clause,[],[f1292,f1277,f1260,f1035,f1025,f311,f1294])).
% 0.22/0.56  fof(f311,plain,(
% 0.22/0.56    spl3_29 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.56  fof(f1025,plain,(
% 0.22/0.56    spl3_106 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).
% 0.22/0.56  fof(f1035,plain,(
% 0.22/0.56    spl3_108 <=> v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).
% 0.22/0.56  fof(f1260,plain,(
% 0.22/0.56    spl3_128 <=> ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(k1_xboole_0,X0,X0) | ~v1_funct_2(k1_xboole_0,X0,X0) | m1_subset_1(k2_funct_2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).
% 0.22/0.56  fof(f1277,plain,(
% 0.22/0.56    spl3_131 <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).
% 0.22/0.56  fof(f1292,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_29 | ~spl3_106 | ~spl3_108 | ~spl3_128 | ~spl3_131)),
% 0.22/0.56    inference(forward_demodulation,[],[f1285,f1279])).
% 0.22/0.56  fof(f1279,plain,(
% 0.22/0.56    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | ~spl3_131),
% 0.22/0.56    inference(avatar_component_clause,[],[f1277])).
% 0.22/0.56  fof(f1285,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_29 | ~spl3_106 | ~spl3_108 | ~spl3_128)),
% 0.22/0.56    inference(forward_demodulation,[],[f1284,f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f1284,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_29 | ~spl3_106 | ~spl3_108 | ~spl3_128)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1283,f313])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_29),
% 0.22/0.56    inference(avatar_component_clause,[],[f311])).
% 0.22/0.56  fof(f1283,plain,(
% 0.22/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_106 | ~spl3_108 | ~spl3_128)),
% 0.22/0.56    inference(forward_demodulation,[],[f1282,f87])).
% 0.22/0.56  fof(f1282,plain,(
% 0.22/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_106 | ~spl3_108 | ~spl3_128)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1281,f1037])).
% 0.22/0.56  fof(f1037,plain,(
% 0.22/0.56    v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_108),
% 0.22/0.56    inference(avatar_component_clause,[],[f1035])).
% 0.22/0.56  fof(f1281,plain,(
% 0.22/0.56    ~v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_106 | ~spl3_128)),
% 0.22/0.56    inference(resolution,[],[f1261,f1027])).
% 0.22/0.56  fof(f1027,plain,(
% 0.22/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_106),
% 0.22/0.56    inference(avatar_component_clause,[],[f1025])).
% 0.22/0.56  fof(f1261,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_2(k1_xboole_0,X0,X0) | ~v3_funct_2(k1_xboole_0,X0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl3_128),
% 0.22/0.56    inference(avatar_component_clause,[],[f1260])).
% 0.22/0.56  fof(f1287,plain,(
% 0.22/0.56    spl3_131 | ~spl3_59 | ~spl3_74 | ~spl3_113),
% 0.22/0.56    inference(avatar_split_clause,[],[f1258,f1084,f668,f554,f1277])).
% 0.22/0.56  fof(f554,plain,(
% 0.22/0.56    spl3_59 <=> k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.22/0.56  fof(f668,plain,(
% 0.22/0.56    spl3_74 <=> k1_xboole_0 = sK0),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.22/0.56  fof(f1084,plain,(
% 0.22/0.56    spl3_113 <=> k1_xboole_0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).
% 0.22/0.56  fof(f1258,plain,(
% 0.22/0.56    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | (~spl3_59 | ~spl3_74 | ~spl3_113)),
% 0.22/0.56    inference(forward_demodulation,[],[f1257,f670])).
% 0.22/0.56  fof(f670,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | ~spl3_74),
% 0.22/0.56    inference(avatar_component_clause,[],[f668])).
% 0.22/0.56  fof(f1257,plain,(
% 0.22/0.56    k2_funct_1(k1_xboole_0) = k2_funct_2(sK0,k1_xboole_0) | (~spl3_59 | ~spl3_113)),
% 0.22/0.56    inference(forward_demodulation,[],[f556,f1086])).
% 0.22/0.56  fof(f1086,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl3_113),
% 0.22/0.56    inference(avatar_component_clause,[],[f1084])).
% 0.22/0.56  fof(f556,plain,(
% 0.22/0.56    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~spl3_59),
% 0.22/0.56    inference(avatar_component_clause,[],[f554])).
% 0.22/0.56  fof(f1274,plain,(
% 0.22/0.56    spl3_128 | ~spl3_23 | ~spl3_57 | ~spl3_90 | ~spl3_104),
% 0.22/0.56    inference(avatar_split_clause,[],[f1256,f1010,f889,f541,f273,f1260])).
% 0.22/0.56  fof(f541,plain,(
% 0.22/0.56    spl3_57 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK1,X0,X0) | ~v1_funct_2(sK1,X0,X0) | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.56  fof(f889,plain,(
% 0.22/0.56    spl3_90 <=> v1_xboole_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 0.22/0.56  fof(f1010,plain,(
% 0.22/0.56    spl3_104 <=> k1_xboole_0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).
% 0.22/0.56  fof(f1256,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k2_funct_2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(k1_xboole_0,X0,X0) | ~v1_funct_2(k1_xboole_0,X0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | (~spl3_23 | ~spl3_57 | ~spl3_90 | ~spl3_104)),
% 0.22/0.56    inference(forward_demodulation,[],[f1255,f1012])).
% 0.22/0.56  fof(f1012,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | ~spl3_104),
% 0.22/0.56    inference(avatar_component_clause,[],[f1010])).
% 0.22/0.56  fof(f1255,plain,(
% 0.22/0.56    ( ! [X0] : (~v3_funct_2(k1_xboole_0,X0,X0) | ~v1_funct_2(k1_xboole_0,X0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | (~spl3_23 | ~spl3_57 | ~spl3_90 | ~spl3_104)),
% 0.22/0.56    inference(forward_demodulation,[],[f1254,f1012])).
% 0.22/0.56  fof(f1254,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_2(k1_xboole_0,X0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK1,X0,X0) | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | (~spl3_23 | ~spl3_57 | ~spl3_90 | ~spl3_104)),
% 0.22/0.56    inference(forward_demodulation,[],[f996,f1012])).
% 0.22/0.56  fof(f996,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(sK1,X0,X0) | ~v3_funct_2(sK1,X0,X0) | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | (~spl3_23 | ~spl3_57 | ~spl3_90)),
% 0.22/0.56    inference(backward_demodulation,[],[f542,f901])).
% 0.22/0.56  fof(f901,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | (~spl3_23 | ~spl3_90)),
% 0.22/0.56    inference(resolution,[],[f891,f274])).
% 0.22/0.56  fof(f891,plain,(
% 0.22/0.56    v1_xboole_0(sK1) | ~spl3_90),
% 0.22/0.56    inference(avatar_component_clause,[],[f889])).
% 0.22/0.56  fof(f542,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_2(sK1,X0,X0) | ~v3_funct_2(sK1,X0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl3_57),
% 0.22/0.56    inference(avatar_component_clause,[],[f541])).
% 0.22/0.56  fof(f1092,plain,(
% 0.22/0.56    ~spl3_114 | ~spl3_23 | ~spl3_92 | spl3_111),
% 0.22/0.56    inference(avatar_split_clause,[],[f1082,f1050,f911,f273,f1089])).
% 0.22/0.56  fof(f911,plain,(
% 0.22/0.56    spl3_92 <=> v1_xboole_0(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 0.22/0.56  fof(f1050,plain,(
% 0.22/0.56    spl3_111 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).
% 0.22/0.56  fof(f1082,plain,(
% 0.22/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) | (~spl3_23 | ~spl3_92 | spl3_111)),
% 0.22/0.56    inference(backward_demodulation,[],[f1052,f915])).
% 0.22/0.56  fof(f915,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | (~spl3_23 | ~spl3_92)),
% 0.22/0.56    inference(resolution,[],[f913,f274])).
% 0.22/0.56  fof(f913,plain,(
% 0.22/0.56    v1_xboole_0(sK2) | ~spl3_92),
% 0.22/0.56    inference(avatar_component_clause,[],[f911])).
% 0.22/0.56  fof(f1052,plain,(
% 0.22/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) | spl3_111),
% 0.22/0.56    inference(avatar_component_clause,[],[f1050])).
% 0.22/0.56  fof(f1087,plain,(
% 0.22/0.56    spl3_113 | ~spl3_23 | ~spl3_92),
% 0.22/0.56    inference(avatar_split_clause,[],[f915,f911,f273,f1084])).
% 0.22/0.56  fof(f1053,plain,(
% 0.22/0.56    ~spl3_111 | ~spl3_23 | ~spl3_90 | spl3_91),
% 0.22/0.56    inference(avatar_split_clause,[],[f1002,f906,f889,f273,f1050])).
% 0.22/0.56  fof(f906,plain,(
% 0.22/0.56    spl3_91 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 0.22/0.56  fof(f1002,plain,(
% 0.22/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) | (~spl3_23 | ~spl3_90 | spl3_91)),
% 0.22/0.56    inference(backward_demodulation,[],[f908,f901])).
% 0.22/0.56  fof(f908,plain,(
% 0.22/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) | spl3_91),
% 0.22/0.56    inference(avatar_component_clause,[],[f906])).
% 0.22/0.56  fof(f1038,plain,(
% 0.22/0.56    spl3_108 | ~spl3_23 | ~spl3_80 | ~spl3_90),
% 0.22/0.56    inference(avatar_split_clause,[],[f999,f889,f818,f273,f1035])).
% 0.22/0.56  fof(f818,plain,(
% 0.22/0.56    spl3_80 <=> v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 0.22/0.56  fof(f999,plain,(
% 0.22/0.56    v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_23 | ~spl3_80 | ~spl3_90)),
% 0.22/0.56    inference(backward_demodulation,[],[f820,f901])).
% 0.22/0.56  fof(f820,plain,(
% 0.22/0.56    v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl3_80),
% 0.22/0.56    inference(avatar_component_clause,[],[f818])).
% 0.22/0.56  fof(f1028,plain,(
% 0.22/0.56    spl3_106 | ~spl3_23 | ~spl3_78 | ~spl3_90),
% 0.22/0.56    inference(avatar_split_clause,[],[f998,f889,f732,f273,f1025])).
% 0.22/0.56  fof(f732,plain,(
% 0.22/0.56    spl3_78 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.22/0.56  fof(f998,plain,(
% 0.22/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_23 | ~spl3_78 | ~spl3_90)),
% 0.22/0.56    inference(backward_demodulation,[],[f734,f901])).
% 0.22/0.56  fof(f734,plain,(
% 0.22/0.56    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl3_78),
% 0.22/0.56    inference(avatar_component_clause,[],[f732])).
% 0.22/0.56  fof(f1013,plain,(
% 0.22/0.56    spl3_104 | ~spl3_23 | ~spl3_90),
% 0.22/0.56    inference(avatar_split_clause,[],[f901,f889,f273,f1010])).
% 0.22/0.56  fof(f914,plain,(
% 0.22/0.56    spl3_92 | ~spl3_24 | ~spl3_88),
% 0.22/0.56    inference(avatar_split_clause,[],[f900,f858,f278,f911])).
% 0.22/0.56  fof(f858,plain,(
% 0.22/0.56    spl3_88 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 0.22/0.56  fof(f900,plain,(
% 0.22/0.56    v1_xboole_0(sK2) | (~spl3_24 | ~spl3_88)),
% 0.22/0.56    inference(resolution,[],[f860,f279])).
% 0.22/0.56  fof(f860,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_88),
% 0.22/0.56    inference(avatar_component_clause,[],[f858])).
% 0.22/0.56  fof(f909,plain,(
% 0.22/0.56    ~spl3_91 | spl3_51 | ~spl3_74),
% 0.22/0.56    inference(avatar_split_clause,[],[f811,f668,f494,f906])).
% 0.22/0.56  fof(f494,plain,(
% 0.22/0.56    spl3_51 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.22/0.56  fof(f811,plain,(
% 0.22/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) | (spl3_51 | ~spl3_74)),
% 0.22/0.56    inference(backward_demodulation,[],[f496,f670])).
% 0.22/0.56  fof(f496,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | spl3_51),
% 0.22/0.56    inference(avatar_component_clause,[],[f494])).
% 0.22/0.56  fof(f892,plain,(
% 0.22/0.56    spl3_90 | ~spl3_24 | ~spl3_86),
% 0.22/0.56    inference(avatar_split_clause,[],[f887,f848,f278,f889])).
% 0.22/0.56  fof(f848,plain,(
% 0.22/0.56    spl3_86 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 0.22/0.56  fof(f887,plain,(
% 0.22/0.56    v1_xboole_0(sK1) | (~spl3_24 | ~spl3_86)),
% 0.22/0.56    inference(resolution,[],[f850,f279])).
% 0.22/0.56  fof(f850,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl3_86),
% 0.22/0.56    inference(avatar_component_clause,[],[f848])).
% 0.22/0.57  fof(f861,plain,(
% 0.22/0.57    spl3_88 | ~spl3_9 | ~spl3_74),
% 0.22/0.57    inference(avatar_split_clause,[],[f815,f668,f132,f858])).
% 0.22/0.57  fof(f132,plain,(
% 0.22/0.57    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.57  fof(f815,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_9 | ~spl3_74)),
% 0.22/0.57    inference(forward_demodulation,[],[f800,f87])).
% 0.22/0.57  fof(f800,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_9 | ~spl3_74)),
% 0.22/0.57    inference(backward_demodulation,[],[f134,f670])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f132])).
% 0.22/0.57  fof(f851,plain,(
% 0.22/0.57    spl3_86 | ~spl3_8 | ~spl3_74),
% 0.22/0.57    inference(avatar_split_clause,[],[f814,f668,f127,f848])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.57  fof(f814,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl3_8 | ~spl3_74)),
% 0.22/0.57    inference(forward_demodulation,[],[f799,f87])).
% 0.22/0.57  fof(f799,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_8 | ~spl3_74)),
% 0.22/0.57    inference(backward_demodulation,[],[f129,f670])).
% 0.22/0.57  fof(f129,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f127])).
% 0.22/0.57  fof(f821,plain,(
% 0.22/0.57    spl3_80 | ~spl3_5 | ~spl3_74),
% 0.22/0.57    inference(avatar_split_clause,[],[f796,f668,f112,f818])).
% 0.22/0.57  fof(f112,plain,(
% 0.22/0.57    spl3_5 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.57  fof(f796,plain,(
% 0.22/0.57    v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl3_5 | ~spl3_74)),
% 0.22/0.57    inference(backward_demodulation,[],[f114,f670])).
% 0.22/0.57  fof(f114,plain,(
% 0.22/0.57    v3_funct_2(sK1,sK0,sK0) | ~spl3_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f112])).
% 0.22/0.57  fof(f784,plain,(
% 0.22/0.57    ~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_17 | ~spl3_20 | spl3_51 | ~spl3_73),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f783])).
% 0.22/0.57  fof(f783,plain,(
% 0.22/0.57    $false | (~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_17 | ~spl3_20 | spl3_51 | ~spl3_73)),
% 0.22/0.57    inference(subsumption_resolution,[],[f773,f239])).
% 0.22/0.57  fof(f239,plain,(
% 0.22/0.57    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_20),
% 0.22/0.57    inference(avatar_component_clause,[],[f237])).
% 0.22/0.57  fof(f237,plain,(
% 0.22/0.57    spl3_20 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.57  fof(f773,plain,(
% 0.22/0.57    ~r2_relset_1(sK0,sK0,sK2,sK2) | (~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_17 | spl3_51 | ~spl3_73)),
% 0.22/0.57    inference(backward_demodulation,[],[f496,f680])).
% 0.22/0.57  fof(f680,plain,(
% 0.22/0.57    sK2 = k2_funct_1(sK1) | (~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_17 | ~spl3_73)),
% 0.22/0.57    inference(subsumption_resolution,[],[f679,f134])).
% 0.22/0.57  fof(f679,plain,(
% 0.22/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | (~spl3_2 | ~spl3_6 | ~spl3_17 | ~spl3_73)),
% 0.22/0.57    inference(subsumption_resolution,[],[f678,f119])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    v1_funct_2(sK2,sK0,sK0) | ~spl3_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f117])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    spl3_6 <=> v1_funct_2(sK2,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.57  fof(f678,plain,(
% 0.22/0.57    ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | (~spl3_2 | ~spl3_17 | ~spl3_73)),
% 0.22/0.57    inference(subsumption_resolution,[],[f677,f99])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    v1_funct_1(sK2) | ~spl3_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f97])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    spl3_2 <=> v1_funct_1(sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.57  fof(f677,plain,(
% 0.22/0.57    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | (~spl3_17 | ~spl3_73)),
% 0.22/0.57    inference(resolution,[],[f666,f203])).
% 0.22/0.57  fof(f203,plain,(
% 0.22/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl3_17),
% 0.22/0.57    inference(avatar_component_clause,[],[f201])).
% 0.22/0.57  fof(f201,plain,(
% 0.22/0.57    spl3_17 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.57  fof(f666,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_1(sK1) = X0) ) | ~spl3_73),
% 0.22/0.57    inference(avatar_component_clause,[],[f665])).
% 0.22/0.57  fof(f665,plain,(
% 0.22/0.57    spl3_73 <=> ! [X0] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_1(sK1) = X0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.22/0.57  fof(f735,plain,(
% 0.22/0.57    spl3_78 | ~spl3_4 | ~spl3_74),
% 0.22/0.57    inference(avatar_split_clause,[],[f690,f668,f107,f732])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    spl3_4 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.57  fof(f690,plain,(
% 0.22/0.57    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl3_4 | ~spl3_74)),
% 0.22/0.57    inference(backward_demodulation,[],[f109,f670])).
% 0.22/0.57  fof(f109,plain,(
% 0.22/0.57    v1_funct_2(sK1,sK0,sK0) | ~spl3_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f107])).
% 0.22/0.57  fof(f671,plain,(
% 0.22/0.57    spl3_73 | spl3_74 | ~spl3_1 | ~spl3_4 | ~spl3_8 | ~spl3_45),
% 0.22/0.57    inference(avatar_split_clause,[],[f455,f441,f127,f107,f92,f668,f665])).
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    spl3_1 <=> v1_funct_1(sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.57  fof(f441,plain,(
% 0.22/0.57    spl3_45 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.57  fof(f455,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_4 | ~spl3_8 | ~spl3_45)),
% 0.22/0.57    inference(subsumption_resolution,[],[f454,f94])).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    v1_funct_1(sK1) | ~spl3_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f92])).
% 0.22/0.57  fof(f454,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_1(sK1)) ) | (~spl3_4 | ~spl3_8 | ~spl3_45)),
% 0.22/0.57    inference(subsumption_resolution,[],[f453,f109])).
% 0.22/0.57  fof(f453,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | (~spl3_8 | ~spl3_45)),
% 0.22/0.57    inference(subsumption_resolution,[],[f452,f129])).
% 0.22/0.57  fof(f452,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | ~spl3_45),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f451])).
% 0.22/0.57  fof(f451,plain,(
% 0.22/0.57    ( ! [X0] : (sK0 != sK0 | k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | ~spl3_45),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f450])).
% 0.22/0.57  fof(f450,plain,(
% 0.22/0.57    ( ! [X0] : (sK0 != sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | ~spl3_45),
% 0.22/0.57    inference(superposition,[],[f266,f443])).
% 0.22/0.57  fof(f443,plain,(
% 0.22/0.57    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl3_45),
% 0.22/0.57    inference(avatar_component_clause,[],[f441])).
% 0.22/0.57  fof(f266,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_funct_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f83,f81])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.57    inference(flattening,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.57    inference(flattening,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.22/0.57  fof(f557,plain,(
% 0.22/0.57    spl3_59 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_49),
% 0.22/0.57    inference(avatar_split_clause,[],[f510,f475,f132,f122,f117,f554])).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    spl3_7 <=> v3_funct_2(sK2,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.57  fof(f475,plain,(
% 0.22/0.57    spl3_49 <=> ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(sK2,X1,X1) | ~v1_funct_2(sK2,X1,X1) | k2_funct_2(X1,sK2) = k2_funct_1(sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.57  fof(f510,plain,(
% 0.22/0.57    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | (~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_49)),
% 0.22/0.57    inference(subsumption_resolution,[],[f509,f134])).
% 0.22/0.57  fof(f509,plain,(
% 0.22/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | (~spl3_6 | ~spl3_7 | ~spl3_49)),
% 0.22/0.57    inference(subsumption_resolution,[],[f508,f124])).
% 0.22/0.57  fof(f124,plain,(
% 0.22/0.57    v3_funct_2(sK2,sK0,sK0) | ~spl3_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f122])).
% 0.22/0.57  fof(f508,plain,(
% 0.22/0.57    ~v3_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | (~spl3_6 | ~spl3_49)),
% 0.22/0.57    inference(resolution,[],[f476,f119])).
% 0.22/0.57  fof(f476,plain,(
% 0.22/0.57    ( ! [X1] : (~v1_funct_2(sK2,X1,X1) | ~v3_funct_2(sK2,X1,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | k2_funct_2(X1,sK2) = k2_funct_1(sK2)) ) | ~spl3_49),
% 0.22/0.57    inference(avatar_component_clause,[],[f475])).
% 0.22/0.57  fof(f543,plain,(
% 0.22/0.57    spl3_57 | ~spl3_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f243,f92,f541])).
% 0.22/0.57  fof(f243,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK1,X0,X0) | ~v1_funct_2(sK1,X0,X0) | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl3_1),
% 0.22/0.57    inference(resolution,[],[f69,f94])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.57    inference(flattening,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.57  fof(f497,plain,(
% 0.22/0.57    ~spl3_51 | ~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_10 | ~spl3_47),
% 0.22/0.57    inference(avatar_split_clause,[],[f487,f466,f137,f127,f112,f107,f494])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    spl3_10 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.57  fof(f466,plain,(
% 0.22/0.57    spl3_47 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK1,X0,X0) | ~v1_funct_2(sK1,X0,X0) | k2_funct_2(X0,sK1) = k2_funct_1(sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.57  fof(f487,plain,(
% 0.22/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_10 | ~spl3_47)),
% 0.22/0.57    inference(backward_demodulation,[],[f139,f485])).
% 0.22/0.57  fof(f485,plain,(
% 0.22/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_47)),
% 0.22/0.57    inference(subsumption_resolution,[],[f484,f129])).
% 0.22/0.57  fof(f484,plain,(
% 0.22/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_4 | ~spl3_5 | ~spl3_47)),
% 0.22/0.57    inference(subsumption_resolution,[],[f483,f114])).
% 0.22/0.57  fof(f483,plain,(
% 0.22/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_4 | ~spl3_47)),
% 0.22/0.57    inference(resolution,[],[f467,f109])).
% 0.22/0.57  fof(f467,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_2(sK1,X0,X0) | ~v3_funct_2(sK1,X0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,sK1) = k2_funct_1(sK1)) ) | ~spl3_47),
% 0.22/0.57    inference(avatar_component_clause,[],[f466])).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | spl3_10),
% 0.22/0.57    inference(avatar_component_clause,[],[f137])).
% 0.22/0.57  fof(f477,plain,(
% 0.22/0.57    spl3_49 | ~spl3_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f230,f97,f475])).
% 0.22/0.57  fof(f230,plain,(
% 0.22/0.57    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(sK2,X1,X1) | ~v1_funct_2(sK2,X1,X1) | k2_funct_2(X1,sK2) = k2_funct_1(sK2)) ) | ~spl3_2),
% 0.22/0.57    inference(resolution,[],[f65,f99])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.57    inference(flattening,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.57  fof(f468,plain,(
% 0.22/0.57    spl3_47 | ~spl3_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f229,f92,f466])).
% 0.22/0.57  fof(f229,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK1,X0,X0) | ~v1_funct_2(sK1,X0,X0) | k2_funct_2(X0,sK1) = k2_funct_1(sK1)) ) | ~spl3_1),
% 0.22/0.57    inference(resolution,[],[f65,f94])).
% 0.22/0.57  fof(f444,plain,(
% 0.22/0.57    spl3_45 | ~spl3_12 | ~spl3_16 | ~spl3_26 | ~spl3_41),
% 0.22/0.57    inference(avatar_split_clause,[],[f434,f416,f290,f196,f157,f441])).
% 0.22/0.57  fof(f157,plain,(
% 0.22/0.57    spl3_12 <=> v1_relat_1(sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.57  fof(f196,plain,(
% 0.22/0.57    spl3_16 <=> v5_relat_1(sK1,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.57  fof(f290,plain,(
% 0.22/0.57    spl3_26 <=> k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.57  fof(f416,plain,(
% 0.22/0.57    spl3_41 <=> v2_funct_2(sK1,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.57  fof(f434,plain,(
% 0.22/0.57    sK0 = k2_relset_1(sK0,sK0,sK1) | (~spl3_12 | ~spl3_16 | ~spl3_26 | ~spl3_41)),
% 0.22/0.57    inference(backward_demodulation,[],[f292,f430])).
% 0.22/0.57  fof(f430,plain,(
% 0.22/0.57    sK0 = k2_relat_1(sK1) | (~spl3_12 | ~spl3_16 | ~spl3_41)),
% 0.22/0.57    inference(subsumption_resolution,[],[f216,f418])).
% 0.22/0.57  fof(f418,plain,(
% 0.22/0.57    v2_funct_2(sK1,sK0) | ~spl3_41),
% 0.22/0.57    inference(avatar_component_clause,[],[f416])).
% 0.22/0.57  fof(f216,plain,(
% 0.22/0.57    ~v2_funct_2(sK1,sK0) | sK0 = k2_relat_1(sK1) | (~spl3_12 | ~spl3_16)),
% 0.22/0.57    inference(subsumption_resolution,[],[f215,f159])).
% 0.22/0.57  fof(f159,plain,(
% 0.22/0.57    v1_relat_1(sK1) | ~spl3_12),
% 0.22/0.57    inference(avatar_component_clause,[],[f157])).
% 0.22/0.57  fof(f215,plain,(
% 0.22/0.57    ~v2_funct_2(sK1,sK0) | sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_16),
% 0.22/0.57    inference(resolution,[],[f198,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.22/0.57  fof(f198,plain,(
% 0.22/0.57    v5_relat_1(sK1,sK0) | ~spl3_16),
% 0.22/0.57    inference(avatar_component_clause,[],[f196])).
% 0.22/0.57  fof(f292,plain,(
% 0.22/0.57    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) | ~spl3_26),
% 0.22/0.57    inference(avatar_component_clause,[],[f290])).
% 0.22/0.57  fof(f419,plain,(
% 0.22/0.57    spl3_41 | ~spl3_5 | ~spl3_8 | ~spl3_39),
% 0.22/0.57    inference(avatar_split_clause,[],[f414,f404,f127,f112,f416])).
% 0.22/0.57  fof(f404,plain,(
% 0.22/0.57    spl3_39 <=> ! [X1,X0] : (~v3_funct_2(sK1,X0,X1) | v2_funct_2(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.57  fof(f414,plain,(
% 0.22/0.57    v2_funct_2(sK1,sK0) | (~spl3_5 | ~spl3_8 | ~spl3_39)),
% 0.22/0.57    inference(subsumption_resolution,[],[f413,f129])).
% 0.22/0.57  fof(f413,plain,(
% 0.22/0.57    v2_funct_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_5 | ~spl3_39)),
% 0.22/0.57    inference(resolution,[],[f405,f114])).
% 0.22/0.57  fof(f405,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v3_funct_2(sK1,X0,X1) | v2_funct_2(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_39),
% 0.22/0.57    inference(avatar_component_clause,[],[f404])).
% 0.22/0.57  fof(f406,plain,(
% 0.22/0.57    spl3_39 | ~spl3_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f221,f92,f404])).
% 0.22/0.57  fof(f221,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v3_funct_2(sK1,X0,X1) | v2_funct_2(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_1),
% 0.22/0.57    inference(resolution,[],[f80,f94])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(flattening,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.57  fof(f387,plain,(
% 0.22/0.57    spl3_36 | ~spl3_29),
% 0.22/0.57    inference(avatar_split_clause,[],[f355,f311,f385])).
% 0.22/0.57  fof(f355,plain,(
% 0.22/0.57    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)) ) | ~spl3_29),
% 0.22/0.57    inference(resolution,[],[f194,f313])).
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | r2_relset_1(k1_xboole_0,X2,X3,X3)) )),
% 0.22/0.57    inference(superposition,[],[f90,f88])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f46])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.57    inference(equality_resolution,[],[f85])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(nnf_transformation,[],[f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(flattening,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.57  fof(f314,plain,(
% 0.22/0.57    spl3_29 | ~spl3_11 | ~spl3_23 | ~spl3_25),
% 0.22/0.57    inference(avatar_split_clause,[],[f304,f285,f273,f144,f311])).
% 0.22/0.57  fof(f144,plain,(
% 0.22/0.57    spl3_11 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.57  fof(f285,plain,(
% 0.22/0.57    spl3_25 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.57  fof(f304,plain,(
% 0.22/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_11 | ~spl3_23 | ~spl3_25)),
% 0.22/0.57    inference(backward_demodulation,[],[f146,f294])).
% 0.22/0.57  fof(f294,plain,(
% 0.22/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl3_23 | ~spl3_25)),
% 0.22/0.57    inference(resolution,[],[f287,f274])).
% 0.22/0.57  fof(f287,plain,(
% 0.22/0.57    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl3_25),
% 0.22/0.57    inference(avatar_component_clause,[],[f285])).
% 0.22/0.57  fof(f146,plain,(
% 0.22/0.57    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_11),
% 0.22/0.57    inference(avatar_component_clause,[],[f144])).
% 0.22/0.57  fof(f293,plain,(
% 0.22/0.57    spl3_26 | ~spl3_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f210,f127,f290])).
% 0.22/0.57  fof(f210,plain,(
% 0.22/0.57    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) | ~spl3_8),
% 0.22/0.57    inference(resolution,[],[f75,f129])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.57  fof(f288,plain,(
% 0.22/0.57    spl3_25 | ~spl3_11 | ~spl3_24),
% 0.22/0.57    inference(avatar_split_clause,[],[f283,f278,f144,f285])).
% 0.22/0.57  fof(f283,plain,(
% 0.22/0.57    v1_xboole_0(k6_partfun1(k1_xboole_0)) | (~spl3_11 | ~spl3_24)),
% 0.22/0.57    inference(resolution,[],[f279,f146])).
% 0.22/0.57  fof(f282,plain,(
% 0.22/0.57    spl3_24 | ~spl3_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f177,f102,f278])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    spl3_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.57  fof(f177,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl3_3),
% 0.22/0.57    inference(forward_demodulation,[],[f176,f87])).
% 0.22/0.57  fof(f176,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl3_3),
% 0.22/0.57    inference(resolution,[],[f62,f104])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f102])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.57  fof(f275,plain,(
% 0.22/0.57    spl3_23 | ~spl3_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f148,f102,f273])).
% 0.22/0.57  fof(f148,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl3_3),
% 0.22/0.57    inference(resolution,[],[f73,f104])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.57  fof(f240,plain,(
% 0.22/0.57    spl3_20 | ~spl3_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f191,f132,f237])).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_9),
% 0.22/0.57    inference(resolution,[],[f90,f134])).
% 0.22/0.57  fof(f204,plain,(
% 0.22/0.57    spl3_17),
% 0.22/0.57    inference(avatar_split_clause,[],[f56,f201])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f42,f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.57    inference(flattening,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.22/0.57    inference(negated_conjecture,[],[f17])).
% 0.22/0.57  fof(f17,conjecture,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 0.22/0.57  fof(f199,plain,(
% 0.22/0.57    spl3_16 | ~spl3_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f171,f127,f196])).
% 0.22/0.57  fof(f171,plain,(
% 0.22/0.57    v5_relat_1(sK1,sK0) | ~spl3_8),
% 0.22/0.57    inference(resolution,[],[f77,f129])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.57  fof(f160,plain,(
% 0.22/0.57    spl3_12 | ~spl3_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f151,f127,f157])).
% 0.22/0.57  fof(f151,plain,(
% 0.22/0.57    v1_relat_1(sK1) | ~spl3_8),
% 0.22/0.57    inference(resolution,[],[f74,f129])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.57  fof(f149,plain,(
% 0.22/0.57    spl3_11),
% 0.22/0.57    inference(avatar_split_clause,[],[f142,f144])).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.57    inference(superposition,[],[f60,f88])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.57  fof(f140,plain,(
% 0.22/0.57    ~spl3_10),
% 0.22/0.57    inference(avatar_split_clause,[],[f57,f137])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    spl3_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f55,f132])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f130,plain,(
% 0.22/0.57    spl3_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f51,f127])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    spl3_7),
% 0.22/0.57    inference(avatar_split_clause,[],[f54,f122])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    v3_funct_2(sK2,sK0,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    spl3_6),
% 0.22/0.57    inference(avatar_split_clause,[],[f53,f117])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    v1_funct_2(sK2,sK0,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    spl3_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f50,f112])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f110,plain,(
% 0.22/0.57    spl3_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f49,f107])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    spl3_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f58,f102])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    v1_xboole_0(k1_xboole_0)),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    v1_xboole_0(k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    spl3_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f52,f97])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    v1_funct_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    spl3_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f48,f92])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    v1_funct_1(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (5812)------------------------------
% 0.22/0.57  % (5812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (5812)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (5812)Memory used [KB]: 7036
% 0.22/0.57  % (5812)Time elapsed: 0.136 s
% 0.22/0.57  % (5812)------------------------------
% 0.22/0.57  % (5812)------------------------------
% 0.22/0.57  % (5805)Success in time 0.203 s
%------------------------------------------------------------------------------
