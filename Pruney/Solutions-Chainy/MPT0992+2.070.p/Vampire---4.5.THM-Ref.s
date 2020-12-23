%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:20 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  246 ( 524 expanded)
%              Number of leaves         :   52 ( 212 expanded)
%              Depth                    :   10
%              Number of atoms          :  775 (1784 expanded)
%              Number of equality atoms :  116 ( 392 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1664,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f98,f102,f106,f110,f114,f158,f161,f168,f204,f212,f216,f218,f237,f258,f373,f381,f557,f562,f642,f762,f773,f837,f850,f878,f986,f996,f1011,f1021,f1028,f1037,f1055,f1209,f1229,f1282,f1314,f1344,f1430,f1654,f1663])).

fof(f1663,plain,
    ( ~ spl4_14
    | ~ spl4_6
    | spl4_41
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f1662,f504,f379,f100,f146])).

fof(f146,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f100,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f379,plain,
    ( spl4_41
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f504,plain,
    ( spl4_52
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1662,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_41
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f993,f505])).

fof(f505,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f504])).

fof(f993,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_41 ),
    inference(trivial_inequality_removal,[],[f992])).

fof(f992,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_41 ),
    inference(superposition,[],[f380,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f380,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f379])).

fof(f1654,plain,
    ( ~ spl4_7
    | ~ spl4_26
    | spl4_39
    | ~ spl4_131 ),
    inference(avatar_contradiction_clause,[],[f1653])).

fof(f1653,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_26
    | spl4_39
    | ~ spl4_131 ),
    inference(subsumption_resolution,[],[f105,f1648])).

fof(f1648,plain,
    ( ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ spl4_26
    | spl4_39
    | ~ spl4_131 ),
    inference(resolution,[],[f1642,f257])).

fof(f257,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1642,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl4_39
    | ~ spl4_131 ),
    inference(resolution,[],[f1431,f369])).

fof(f369,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl4_39
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1431,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl4_131 ),
    inference(resolution,[],[f1429,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1429,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k7_relat_1(sK3,sK2),X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) )
    | ~ spl4_131 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f1428,plain,
    ( spl4_131
  <=> ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v5_relat_1(k7_relat_1(sK3,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1430,plain,
    ( ~ spl4_107
    | spl4_131
    | ~ spl4_109 ),
    inference(avatar_split_clause,[],[f1424,f1019,f1428,f1013])).

fof(f1013,plain,
    ( spl4_107
  <=> v1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f1019,plain,
    ( spl4_109
  <=> ! [X2] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f1424,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v5_relat_1(k7_relat_1(sK3,sK2),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_109 ),
    inference(resolution,[],[f1020,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1020,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) )
    | ~ spl4_109 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1344,plain,
    ( ~ spl4_7
    | ~ spl4_26
    | spl4_107 ),
    inference(avatar_contradiction_clause,[],[f1339])).

fof(f1339,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_26
    | spl4_107 ),
    inference(subsumption_resolution,[],[f105,f1333])).

fof(f1333,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_26
    | spl4_107 ),
    inference(resolution,[],[f1329,f257])).

fof(f1329,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_107 ),
    inference(resolution,[],[f1316,f50])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1316,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X0)) )
    | spl4_107 ),
    inference(resolution,[],[f1014,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1014,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_107 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f1314,plain,
    ( ~ spl4_107
    | ~ spl4_121
    | spl4_120 ),
    inference(avatar_split_clause,[],[f1294,f1207,f1218,f1013])).

fof(f1218,plain,
    ( spl4_121
  <=> v5_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f1207,plain,
    ( spl4_120
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f1294,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_120 ),
    inference(resolution,[],[f1208,f52])).

fof(f1208,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0)
    | spl4_120 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1282,plain,
    ( ~ spl4_7
    | ~ spl4_26
    | ~ spl4_105 ),
    inference(avatar_contradiction_clause,[],[f1277])).

fof(f1277,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_26
    | ~ spl4_105 ),
    inference(subsumption_resolution,[],[f105,f1271])).

fof(f1271,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_26
    | ~ spl4_105 ),
    inference(resolution,[],[f1233,f257])).

fof(f1233,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_105 ),
    inference(resolution,[],[f1007,f50])).

fof(f1007,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X1)) )
    | ~ spl4_105 ),
    inference(avatar_component_clause,[],[f1006])).

fof(f1006,plain,
    ( spl4_105
  <=> ! [X1] :
        ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).

fof(f1229,plain,
    ( ~ spl4_86
    | spl4_121 ),
    inference(avatar_split_clause,[],[f1228,f1218,f756])).

fof(f756,plain,
    ( spl4_86
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1228,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_121 ),
    inference(forward_demodulation,[],[f1225,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1225,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl4_121 ),
    inference(resolution,[],[f1219,f65])).

fof(f1219,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0)
    | spl4_121 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1209,plain,
    ( ~ spl4_120
    | spl4_98
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1204,f1009,f876,f1207])).

fof(f876,plain,
    ( spl4_98
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f1009,plain,
    ( spl4_106
  <=> ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f1204,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0)
    | spl4_98
    | ~ spl4_106 ),
    inference(resolution,[],[f1010,f877])).

fof(f877,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_98 ),
    inference(avatar_component_clause,[],[f876])).

fof(f1010,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) )
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1055,plain,
    ( ~ spl4_20
    | spl4_108 ),
    inference(avatar_contradiction_clause,[],[f1053])).

fof(f1053,plain,
    ( $false
    | ~ spl4_20
    | spl4_108 ),
    inference(resolution,[],[f1017,f211])).

fof(f211,plain,
    ( ! [X12] : v1_funct_1(k7_relat_1(sK3,X12))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_20
  <=> ! [X12] : v1_funct_1(k7_relat_1(sK3,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1017,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl4_108 ),
    inference(avatar_component_clause,[],[f1016])).

fof(f1016,plain,
    ( spl4_108
  <=> v1_funct_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1037,plain,
    ( spl4_52
    | spl4_4
    | ~ spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f722,f104,f108,f93,f504])).

fof(f93,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f108,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f722,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f105,f297])).

fof(f297,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f66,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f1028,plain,
    ( spl4_84
    | ~ spl4_24
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1027,f760,f235,f748])).

fof(f748,plain,
    ( spl4_84
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f235,plain,
    ( spl4_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f760,plain,
    ( spl4_87
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f1027,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f987,f75])).

fof(f987,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_87 ),
    inference(superposition,[],[f761,f63])).

fof(f761,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f760])).

fof(f1021,plain,
    ( ~ spl4_107
    | ~ spl4_108
    | spl4_109
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1002,f379,f1019,f1016,f1013])).

fof(f1002,plain,
    ( ! [X2] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_41 ),
    inference(superposition,[],[f56,f998])).

fof(f998,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f379])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1011,plain,
    ( spl4_105
    | spl4_106
    | ~ spl4_18
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1001,f379,f202,f1009,f1006])).

fof(f202,plain,
    ( spl4_18
  <=> ! [X3,X2] :
        ( v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1001,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_18
    | ~ spl4_41 ),
    inference(superposition,[],[f262,f998])).

fof(f262,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),X1)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X2))
        | ~ v1_relat_1(X2) )
    | ~ spl4_18 ),
    inference(resolution,[],[f203,f49])).

fof(f203,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X2))
        | v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f202])).

fof(f996,plain,
    ( ~ spl4_14
    | ~ spl4_58
    | spl4_41
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f994,f748,f379,f552,f146])).

fof(f552,plain,
    ( spl4_58
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f994,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl4_41
    | ~ spl4_84 ),
    inference(forward_demodulation,[],[f993,f749])).

fof(f749,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f748])).

fof(f986,plain,
    ( ~ spl4_14
    | ~ spl4_22
    | ~ spl4_24
    | spl4_86 ),
    inference(avatar_split_clause,[],[f984,f756,f235,f225,f146])).

fof(f225,plain,
    ( spl4_22
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f984,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_86 ),
    inference(superposition,[],[f757,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f757,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_86 ),
    inference(avatar_component_clause,[],[f756])).

fof(f878,plain,
    ( ~ spl4_98
    | ~ spl4_4
    | spl4_21 ),
    inference(avatar_split_clause,[],[f874,f214,f93,f876])).

fof(f214,plain,
    ( spl4_21
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f874,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | ~ spl4_4
    | spl4_21 ),
    inference(forward_demodulation,[],[f215,f362])).

fof(f362,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f215,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f214])).

fof(f850,plain,
    ( ~ spl4_24
    | ~ spl4_4
    | ~ spl4_26
    | spl4_39 ),
    inference(avatar_split_clause,[],[f849,f368,f256,f93,f235])).

fof(f849,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_26
    | spl4_39 ),
    inference(forward_demodulation,[],[f848,f75])).

fof(f848,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_26
    | spl4_39 ),
    inference(forward_demodulation,[],[f382,f362])).

fof(f382,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_26
    | spl4_39 ),
    inference(resolution,[],[f369,f257])).

fof(f837,plain,
    ( spl4_58
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f535,f100,f96,f552])).

fof(f96,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f535,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f101,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f101,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f773,plain,
    ( ~ spl4_7
    | ~ spl4_39
    | spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f392,f112,f89,f368,f104])).

fof(f89,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f112,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f392,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f90,f188])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(resolution,[],[f72,f113])).

fof(f113,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f90,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f762,plain,
    ( ~ spl4_25
    | spl4_87
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f679,f560,f760,f240])).

fof(f240,plain,
    ( spl4_25
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f560,plain,
    ( spl4_59
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f679,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_59 ),
    inference(resolution,[],[f561,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1)
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f125,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f125,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f81,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f561,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f560])).

fof(f642,plain,
    ( ~ spl4_24
    | spl4_25 ),
    inference(avatar_split_clause,[],[f243,f240,f235])).

fof(f243,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl4_25 ),
    inference(resolution,[],[f241,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f241,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f562,plain,
    ( spl4_59
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f558,f108,f96,f93,f560])).

fof(f558,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f537,f362])).

fof(f537,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(superposition,[],[f109,f97])).

fof(f109,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f557,plain,
    ( spl4_24
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f555,f104,f96,f235])).

fof(f555,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f536,f76])).

fof(f536,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f105,f97])).

fof(f381,plain,
    ( ~ spl4_39
    | ~ spl4_41
    | spl4_40 ),
    inference(avatar_split_clause,[],[f376,f371,f379,f368])).

fof(f371,plain,
    ( spl4_40
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f376,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_40 ),
    inference(superposition,[],[f372,f63])).

fof(f372,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f371])).

fof(f373,plain,
    ( ~ spl4_39
    | spl4_4
    | ~ spl4_40
    | spl4_21 ),
    inference(avatar_split_clause,[],[f361,f214,f371,f93,f368])).

fof(f361,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_21 ),
    inference(resolution,[],[f68,f215])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f258,plain,
    ( ~ spl4_9
    | spl4_26
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f253,f112,f256,f112])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(superposition,[],[f74,f188])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f237,plain,
    ( ~ spl4_24
    | spl4_22 ),
    inference(avatar_split_clause,[],[f233,f225,f235])).

fof(f233,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl4_22 ),
    inference(superposition,[],[f231,f75])).

fof(f231,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl4_22 ),
    inference(resolution,[],[f226,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f226,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f225])).

fof(f218,plain,
    ( ~ spl4_7
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f105,f200])).

fof(f200,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_17
  <=> ! [X1,X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f216,plain,
    ( ~ spl4_7
    | ~ spl4_21
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f194,f112,f86,f214,f104])).

fof(f86,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f194,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f87,f188])).

fof(f87,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f212,plain,
    ( spl4_17
    | spl4_20
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f195,f112,f210,f199])).

fof(f195,plain,
    ( ! [X12,X10,X11] :
        ( v1_funct_1(k7_relat_1(sK3,X12))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X12,X10,X11] :
        ( v1_funct_1(k7_relat_1(sK3,X12))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
    | ~ spl4_9 ),
    inference(superposition,[],[f163,f188])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(resolution,[],[f73,f113])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f204,plain,
    ( spl4_17
    | spl4_18
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f197,f112,f202,f199])).

fof(f197,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_relat_1(k7_relat_1(sK3,X2)) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(superposition,[],[f166,f188])).

fof(f166,plain,
    ( ! [X6,X8,X7,X9] :
        ( v1_funct_2(k2_partfun1(X6,X7,sK3,X8),k1_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_relat_1(k2_partfun1(X6,X7,sK3,X8)) )
    | ~ spl4_9 ),
    inference(resolution,[],[f163,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f168,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f164,f112,f83,f104])).

fof(f83,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f164,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_9 ),
    inference(resolution,[],[f163,f84])).

fof(f84,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f161,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f157,f50])).

fof(f157,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_16
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f158,plain,
    ( ~ spl4_16
    | ~ spl4_7
    | spl4_14 ),
    inference(avatar_split_clause,[],[f153,f146,f104,f156])).

fof(f153,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_7
    | spl4_14 ),
    inference(resolution,[],[f152,f105])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_14 ),
    inference(resolution,[],[f147,f49])).

fof(f147,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f114,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f42,f112])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f110,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f43,f108])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f44,f104])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f46,f96,f93])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f47,f89,f86,f83])).

fof(f47,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:27:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (19093)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (19101)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (19099)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (19091)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (19094)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.54  % (19102)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.56  % (19103)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.56  % (19092)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.56  % (19089)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (19089)Refutation not found, incomplete strategy% (19089)------------------------------
% 0.22/0.57  % (19089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (19089)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (19089)Memory used [KB]: 10618
% 0.22/0.57  % (19089)Time elapsed: 0.132 s
% 0.22/0.57  % (19089)------------------------------
% 0.22/0.57  % (19089)------------------------------
% 0.22/0.57  % (19090)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.57  % (19108)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.57  % (19098)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.68/0.58  % (19105)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.68/0.58  % (19088)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.68/0.59  % (19095)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.68/0.59  % (19108)Refutation not found, incomplete strategy% (19108)------------------------------
% 1.68/0.59  % (19108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (19108)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (19108)Memory used [KB]: 10618
% 1.68/0.59  % (19108)Time elapsed: 0.135 s
% 1.68/0.59  % (19108)------------------------------
% 1.68/0.59  % (19108)------------------------------
% 1.68/0.59  % (19097)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.68/0.59  % (19100)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.88/0.60  % (19107)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.88/0.60  % (19104)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.88/0.61  % (19096)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.88/0.61  % (19106)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.88/0.62  % (19094)Refutation found. Thanks to Tanya!
% 1.88/0.62  % SZS status Theorem for theBenchmark
% 1.88/0.62  % SZS output start Proof for theBenchmark
% 1.88/0.62  fof(f1664,plain,(
% 1.88/0.62    $false),
% 1.88/0.62    inference(avatar_sat_refutation,[],[f91,f98,f102,f106,f110,f114,f158,f161,f168,f204,f212,f216,f218,f237,f258,f373,f381,f557,f562,f642,f762,f773,f837,f850,f878,f986,f996,f1011,f1021,f1028,f1037,f1055,f1209,f1229,f1282,f1314,f1344,f1430,f1654,f1663])).
% 1.88/0.62  fof(f1663,plain,(
% 1.88/0.62    ~spl4_14 | ~spl4_6 | spl4_41 | ~spl4_52),
% 1.88/0.62    inference(avatar_split_clause,[],[f1662,f504,f379,f100,f146])).
% 1.88/0.62  fof(f146,plain,(
% 1.88/0.62    spl4_14 <=> v1_relat_1(sK3)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.88/0.62  fof(f100,plain,(
% 1.88/0.62    spl4_6 <=> r1_tarski(sK2,sK0)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.88/0.62  fof(f379,plain,(
% 1.88/0.62    spl4_41 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.88/0.62  fof(f504,plain,(
% 1.88/0.62    spl4_52 <=> sK0 = k1_relat_1(sK3)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.88/0.62  fof(f1662,plain,(
% 1.88/0.62    ~r1_tarski(sK2,sK0) | ~v1_relat_1(sK3) | (spl4_41 | ~spl4_52)),
% 1.88/0.62    inference(forward_demodulation,[],[f993,f505])).
% 1.88/0.62  fof(f505,plain,(
% 1.88/0.62    sK0 = k1_relat_1(sK3) | ~spl4_52),
% 1.88/0.62    inference(avatar_component_clause,[],[f504])).
% 1.88/0.62  fof(f993,plain,(
% 1.88/0.62    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_41),
% 1.88/0.62    inference(trivial_inequality_removal,[],[f992])).
% 1.88/0.62  fof(f992,plain,(
% 1.88/0.62    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_41),
% 1.88/0.62    inference(superposition,[],[f380,f51])).
% 1.88/0.62  fof(f51,plain,(
% 1.88/0.62    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f21])).
% 1.88/0.62  fof(f21,plain,(
% 1.88/0.62    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.88/0.62    inference(flattening,[],[f20])).
% 1.88/0.62  fof(f20,plain,(
% 1.88/0.62    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.88/0.62    inference(ennf_transformation,[],[f8])).
% 1.88/0.62  fof(f8,axiom,(
% 1.88/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.88/0.62  fof(f380,plain,(
% 1.88/0.62    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_41),
% 1.88/0.62    inference(avatar_component_clause,[],[f379])).
% 1.88/0.62  fof(f1654,plain,(
% 1.88/0.62    ~spl4_7 | ~spl4_26 | spl4_39 | ~spl4_131),
% 1.88/0.62    inference(avatar_contradiction_clause,[],[f1653])).
% 1.88/0.62  fof(f1653,plain,(
% 1.88/0.62    $false | (~spl4_7 | ~spl4_26 | spl4_39 | ~spl4_131)),
% 1.88/0.62    inference(subsumption_resolution,[],[f105,f1648])).
% 1.88/0.62  fof(f1648,plain,(
% 1.88/0.62    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))) ) | (~spl4_26 | spl4_39 | ~spl4_131)),
% 1.88/0.62    inference(resolution,[],[f1642,f257])).
% 1.88/0.62  fof(f257,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_26),
% 1.88/0.62    inference(avatar_component_clause,[],[f256])).
% 1.88/0.62  fof(f256,plain,(
% 1.88/0.62    spl4_26 <=> ! [X1,X0,X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.88/0.62  fof(f1642,plain,(
% 1.88/0.62    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (spl4_39 | ~spl4_131)),
% 1.88/0.62    inference(resolution,[],[f1431,f369])).
% 1.88/0.62  fof(f369,plain,(
% 1.88/0.62    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_39),
% 1.88/0.62    inference(avatar_component_clause,[],[f368])).
% 1.88/0.62  fof(f368,plain,(
% 1.88/0.62    spl4_39 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.88/0.62  fof(f1431,plain,(
% 1.88/0.62    ( ! [X0,X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl4_131),
% 1.88/0.62    inference(resolution,[],[f1429,f65])).
% 1.88/0.62  fof(f65,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f28])).
% 1.88/0.62  fof(f28,plain,(
% 1.88/0.62    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/0.62    inference(ennf_transformation,[],[f9])).
% 1.88/0.62  fof(f9,axiom,(
% 1.88/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.88/0.62  fof(f1429,plain,(
% 1.88/0.62    ( ! [X0] : (~v5_relat_1(k7_relat_1(sK3,sK2),X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl4_131),
% 1.88/0.62    inference(avatar_component_clause,[],[f1428])).
% 1.88/0.62  fof(f1428,plain,(
% 1.88/0.62    spl4_131 <=> ! [X0] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v5_relat_1(k7_relat_1(sK3,sK2),X0))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).
% 1.88/0.62  fof(f105,plain,(
% 1.88/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 1.88/0.62    inference(avatar_component_clause,[],[f104])).
% 1.88/0.62  fof(f104,plain,(
% 1.88/0.62    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.88/0.62  fof(f1430,plain,(
% 1.88/0.62    ~spl4_107 | spl4_131 | ~spl4_109),
% 1.88/0.62    inference(avatar_split_clause,[],[f1424,f1019,f1428,f1013])).
% 1.88/0.62  fof(f1013,plain,(
% 1.88/0.62    spl4_107 <=> v1_relat_1(k7_relat_1(sK3,sK2))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 1.88/0.62  fof(f1019,plain,(
% 1.88/0.62    spl4_109 <=> ! [X2] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).
% 1.88/0.62  fof(f1424,plain,(
% 1.88/0.62    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v5_relat_1(k7_relat_1(sK3,sK2),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_109),
% 1.88/0.62    inference(resolution,[],[f1020,f52])).
% 1.88/0.62  fof(f52,plain,(
% 1.88/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f37])).
% 1.88/0.62  fof(f37,plain,(
% 1.88/0.62    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.88/0.62    inference(nnf_transformation,[],[f22])).
% 1.88/0.62  fof(f22,plain,(
% 1.88/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.88/0.62    inference(ennf_transformation,[],[f5])).
% 1.88/0.62  fof(f5,axiom,(
% 1.88/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.88/0.62  fof(f1020,plain,(
% 1.88/0.62    ( ! [X2] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))) ) | ~spl4_109),
% 1.88/0.62    inference(avatar_component_clause,[],[f1019])).
% 1.88/0.62  fof(f1344,plain,(
% 1.88/0.62    ~spl4_7 | ~spl4_26 | spl4_107),
% 1.88/0.62    inference(avatar_contradiction_clause,[],[f1339])).
% 1.88/0.62  fof(f1339,plain,(
% 1.88/0.62    $false | (~spl4_7 | ~spl4_26 | spl4_107)),
% 1.88/0.62    inference(subsumption_resolution,[],[f105,f1333])).
% 1.88/0.62  fof(f1333,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_26 | spl4_107)),
% 1.88/0.62    inference(resolution,[],[f1329,f257])).
% 1.88/0.62  fof(f1329,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_107),
% 1.88/0.62    inference(resolution,[],[f1316,f50])).
% 1.88/0.62  fof(f50,plain,(
% 1.88/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f6])).
% 1.88/0.62  fof(f6,axiom,(
% 1.88/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.88/0.62  fof(f1316,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X0))) ) | spl4_107),
% 1.88/0.62    inference(resolution,[],[f1014,f49])).
% 1.88/0.62  fof(f49,plain,(
% 1.88/0.62    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f19])).
% 1.88/0.62  fof(f19,plain,(
% 1.88/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f4])).
% 1.88/0.62  fof(f4,axiom,(
% 1.88/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.88/0.62  fof(f1014,plain,(
% 1.88/0.62    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_107),
% 1.88/0.62    inference(avatar_component_clause,[],[f1013])).
% 1.88/0.62  fof(f1314,plain,(
% 1.88/0.62    ~spl4_107 | ~spl4_121 | spl4_120),
% 1.88/0.62    inference(avatar_split_clause,[],[f1294,f1207,f1218,f1013])).
% 1.88/0.62  fof(f1218,plain,(
% 1.88/0.62    spl4_121 <=> v5_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).
% 1.88/0.62  fof(f1207,plain,(
% 1.88/0.62    spl4_120 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).
% 1.88/0.62  fof(f1294,plain,(
% 1.88/0.62    ~v5_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_120),
% 1.88/0.62    inference(resolution,[],[f1208,f52])).
% 1.88/0.62  fof(f1208,plain,(
% 1.88/0.62    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0) | spl4_120),
% 1.88/0.62    inference(avatar_component_clause,[],[f1207])).
% 1.88/0.62  fof(f1282,plain,(
% 1.88/0.62    ~spl4_7 | ~spl4_26 | ~spl4_105),
% 1.88/0.62    inference(avatar_contradiction_clause,[],[f1277])).
% 1.88/0.62  fof(f1277,plain,(
% 1.88/0.62    $false | (~spl4_7 | ~spl4_26 | ~spl4_105)),
% 1.88/0.62    inference(subsumption_resolution,[],[f105,f1271])).
% 1.88/0.62  fof(f1271,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_26 | ~spl4_105)),
% 1.88/0.62    inference(resolution,[],[f1233,f257])).
% 1.88/0.62  fof(f1233,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_105),
% 1.88/0.62    inference(resolution,[],[f1007,f50])).
% 1.88/0.62  fof(f1007,plain,(
% 1.88/0.62    ( ! [X1] : (~v1_relat_1(X1) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X1))) ) | ~spl4_105),
% 1.88/0.62    inference(avatar_component_clause,[],[f1006])).
% 1.88/0.62  fof(f1006,plain,(
% 1.88/0.62    spl4_105 <=> ! [X1] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X1)) | ~v1_relat_1(X1))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).
% 1.88/0.62  fof(f1229,plain,(
% 1.88/0.62    ~spl4_86 | spl4_121),
% 1.88/0.62    inference(avatar_split_clause,[],[f1228,f1218,f756])).
% 1.88/0.62  fof(f756,plain,(
% 1.88/0.62    spl4_86 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 1.88/0.62  fof(f1228,plain,(
% 1.88/0.62    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_121),
% 1.88/0.62    inference(forward_demodulation,[],[f1225,f75])).
% 1.88/0.62  fof(f75,plain,(
% 1.88/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.88/0.62    inference(equality_resolution,[],[f62])).
% 1.88/0.62  fof(f62,plain,(
% 1.88/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.88/0.62    inference(cnf_transformation,[],[f40])).
% 1.88/0.62  fof(f40,plain,(
% 1.88/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.88/0.62    inference(flattening,[],[f39])).
% 1.88/0.62  fof(f39,plain,(
% 1.88/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.88/0.62    inference(nnf_transformation,[],[f2])).
% 1.88/0.62  fof(f2,axiom,(
% 1.88/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.88/0.62  fof(f1225,plain,(
% 1.88/0.62    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | spl4_121),
% 1.88/0.62    inference(resolution,[],[f1219,f65])).
% 1.88/0.62  fof(f1219,plain,(
% 1.88/0.62    ~v5_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0) | spl4_121),
% 1.88/0.62    inference(avatar_component_clause,[],[f1218])).
% 1.88/0.62  fof(f1209,plain,(
% 1.88/0.62    ~spl4_120 | spl4_98 | ~spl4_106),
% 1.88/0.62    inference(avatar_split_clause,[],[f1204,f1009,f876,f1207])).
% 1.88/0.62  fof(f876,plain,(
% 1.88/0.62    spl4_98 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).
% 1.88/0.62  fof(f1009,plain,(
% 1.88/0.62    spl4_106 <=> ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 1.88/0.62  fof(f1204,plain,(
% 1.88/0.62    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0) | (spl4_98 | ~spl4_106)),
% 1.88/0.62    inference(resolution,[],[f1010,f877])).
% 1.88/0.62  fof(f877,plain,(
% 1.88/0.62    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | spl4_98),
% 1.88/0.62    inference(avatar_component_clause,[],[f876])).
% 1.88/0.62  fof(f1010,plain,(
% 1.88/0.62    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)) ) | ~spl4_106),
% 1.88/0.62    inference(avatar_component_clause,[],[f1009])).
% 1.88/0.62  fof(f1055,plain,(
% 1.88/0.62    ~spl4_20 | spl4_108),
% 1.88/0.62    inference(avatar_contradiction_clause,[],[f1053])).
% 1.88/0.62  fof(f1053,plain,(
% 1.88/0.62    $false | (~spl4_20 | spl4_108)),
% 1.88/0.62    inference(resolution,[],[f1017,f211])).
% 1.88/0.62  fof(f211,plain,(
% 1.88/0.62    ( ! [X12] : (v1_funct_1(k7_relat_1(sK3,X12))) ) | ~spl4_20),
% 1.88/0.62    inference(avatar_component_clause,[],[f210])).
% 1.88/0.62  fof(f210,plain,(
% 1.88/0.62    spl4_20 <=> ! [X12] : v1_funct_1(k7_relat_1(sK3,X12))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.88/0.62  fof(f1017,plain,(
% 1.88/0.62    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl4_108),
% 1.88/0.62    inference(avatar_component_clause,[],[f1016])).
% 1.88/0.62  fof(f1016,plain,(
% 1.88/0.62    spl4_108 <=> v1_funct_1(k7_relat_1(sK3,sK2))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).
% 1.88/0.62  fof(f1037,plain,(
% 1.88/0.62    spl4_52 | spl4_4 | ~spl4_8 | ~spl4_7),
% 1.88/0.62    inference(avatar_split_clause,[],[f722,f104,f108,f93,f504])).
% 1.88/0.62  fof(f93,plain,(
% 1.88/0.62    spl4_4 <=> k1_xboole_0 = sK1),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.88/0.62  fof(f108,plain,(
% 1.88/0.62    spl4_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.88/0.62  fof(f722,plain,(
% 1.88/0.62    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK3) | ~spl4_7),
% 1.88/0.62    inference(resolution,[],[f105,f297])).
% 1.88/0.62  fof(f297,plain,(
% 1.88/0.62    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3) )),
% 1.88/0.62    inference(duplicate_literal_removal,[],[f294])).
% 1.88/0.62  fof(f294,plain,(
% 1.88/0.62    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.88/0.62    inference(superposition,[],[f66,f63])).
% 1.88/0.62  fof(f63,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f27])).
% 1.88/0.62  fof(f27,plain,(
% 1.88/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/0.62    inference(ennf_transformation,[],[f10])).
% 1.88/0.62  fof(f10,axiom,(
% 1.88/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.88/0.62  fof(f66,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f41])).
% 1.88/0.62  fof(f41,plain,(
% 1.88/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/0.62    inference(nnf_transformation,[],[f30])).
% 1.88/0.62  fof(f30,plain,(
% 1.88/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/0.62    inference(flattening,[],[f29])).
% 1.88/0.62  fof(f29,plain,(
% 1.88/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/0.62    inference(ennf_transformation,[],[f11])).
% 1.88/0.62  fof(f11,axiom,(
% 1.88/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.88/0.62  fof(f1028,plain,(
% 1.88/0.62    spl4_84 | ~spl4_24 | ~spl4_87),
% 1.88/0.62    inference(avatar_split_clause,[],[f1027,f760,f235,f748])).
% 1.88/0.62  fof(f748,plain,(
% 1.88/0.62    spl4_84 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 1.88/0.62  fof(f235,plain,(
% 1.88/0.62    spl4_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.88/0.62  fof(f760,plain,(
% 1.88/0.62    spl4_87 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 1.88/0.62  fof(f1027,plain,(
% 1.88/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_87),
% 1.88/0.62    inference(forward_demodulation,[],[f987,f75])).
% 1.88/0.62  fof(f987,plain,(
% 1.88/0.62    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_87),
% 1.88/0.62    inference(superposition,[],[f761,f63])).
% 1.88/0.62  fof(f761,plain,(
% 1.88/0.62    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl4_87),
% 1.88/0.62    inference(avatar_component_clause,[],[f760])).
% 1.88/0.62  fof(f1021,plain,(
% 1.88/0.62    ~spl4_107 | ~spl4_108 | spl4_109 | ~spl4_41),
% 1.88/0.62    inference(avatar_split_clause,[],[f1002,f379,f1019,f1016,f1013])).
% 1.88/0.62  fof(f1002,plain,(
% 1.88/0.62    ( ! [X2] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_41),
% 1.88/0.62    inference(superposition,[],[f56,f998])).
% 1.88/0.62  fof(f998,plain,(
% 1.88/0.62    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_41),
% 1.88/0.62    inference(avatar_component_clause,[],[f379])).
% 1.88/0.62  fof(f56,plain,(
% 1.88/0.62    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f24])).
% 1.88/0.62  fof(f24,plain,(
% 1.88/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.88/0.62    inference(flattening,[],[f23])).
% 1.88/0.62  fof(f23,plain,(
% 1.88/0.62    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.88/0.62    inference(ennf_transformation,[],[f14])).
% 1.88/0.62  fof(f14,axiom,(
% 1.88/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.88/0.62  fof(f1011,plain,(
% 1.88/0.62    spl4_105 | spl4_106 | ~spl4_18 | ~spl4_41),
% 1.88/0.62    inference(avatar_split_clause,[],[f1001,f379,f202,f1009,f1006])).
% 1.88/0.62  fof(f202,plain,(
% 1.88/0.62    spl4_18 <=> ! [X3,X2] : (v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~v1_relat_1(k7_relat_1(sK3,X2)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.88/0.62  fof(f1001,plain,(
% 1.88/0.62    ( ! [X0,X1] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) ) | (~spl4_18 | ~spl4_41)),
% 1.88/0.62    inference(superposition,[],[f262,f998])).
% 1.88/0.62  fof(f262,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),X1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X2)) | ~v1_relat_1(X2)) ) | ~spl4_18),
% 1.88/0.62    inference(resolution,[],[f203,f49])).
% 1.88/0.62  fof(f203,plain,(
% 1.88/0.62    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK3,X2)) | v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3)) ) | ~spl4_18),
% 1.88/0.62    inference(avatar_component_clause,[],[f202])).
% 1.88/0.62  fof(f996,plain,(
% 1.88/0.62    ~spl4_14 | ~spl4_58 | spl4_41 | ~spl4_84),
% 1.88/0.62    inference(avatar_split_clause,[],[f994,f748,f379,f552,f146])).
% 1.88/0.62  fof(f552,plain,(
% 1.88/0.62    spl4_58 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.88/0.62  fof(f994,plain,(
% 1.88/0.62    ~r1_tarski(sK2,k1_xboole_0) | ~v1_relat_1(sK3) | (spl4_41 | ~spl4_84)),
% 1.88/0.62    inference(forward_demodulation,[],[f993,f749])).
% 1.88/0.62  fof(f749,plain,(
% 1.88/0.62    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_84),
% 1.88/0.62    inference(avatar_component_clause,[],[f748])).
% 1.88/0.62  fof(f986,plain,(
% 1.88/0.62    ~spl4_14 | ~spl4_22 | ~spl4_24 | spl4_86),
% 1.88/0.62    inference(avatar_split_clause,[],[f984,f756,f235,f225,f146])).
% 1.88/0.62  fof(f225,plain,(
% 1.88/0.62    spl4_22 <=> v4_relat_1(sK3,sK2)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.88/0.62  fof(f984,plain,(
% 1.88/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | spl4_86),
% 1.88/0.62    inference(superposition,[],[f757,f57])).
% 1.88/0.62  fof(f57,plain,(
% 1.88/0.62    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f26])).
% 1.88/0.62  fof(f26,plain,(
% 1.88/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.88/0.62    inference(flattening,[],[f25])).
% 1.88/0.62  fof(f25,plain,(
% 1.88/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.88/0.62    inference(ennf_transformation,[],[f7])).
% 1.88/0.62  fof(f7,axiom,(
% 1.88/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.88/0.62  fof(f757,plain,(
% 1.88/0.62    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_86),
% 1.88/0.62    inference(avatar_component_clause,[],[f756])).
% 1.88/0.62  fof(f878,plain,(
% 1.88/0.62    ~spl4_98 | ~spl4_4 | spl4_21),
% 1.88/0.62    inference(avatar_split_clause,[],[f874,f214,f93,f876])).
% 1.88/0.62  fof(f214,plain,(
% 1.88/0.62    spl4_21 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.88/0.62  fof(f874,plain,(
% 1.88/0.62    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (~spl4_4 | spl4_21)),
% 1.88/0.62    inference(forward_demodulation,[],[f215,f362])).
% 1.88/0.62  fof(f362,plain,(
% 1.88/0.62    k1_xboole_0 = sK1 | ~spl4_4),
% 1.88/0.62    inference(avatar_component_clause,[],[f93])).
% 1.88/0.62  fof(f215,plain,(
% 1.88/0.62    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_21),
% 1.88/0.62    inference(avatar_component_clause,[],[f214])).
% 1.88/0.62  fof(f850,plain,(
% 1.88/0.62    ~spl4_24 | ~spl4_4 | ~spl4_26 | spl4_39),
% 1.88/0.62    inference(avatar_split_clause,[],[f849,f368,f256,f93,f235])).
% 1.88/0.62  fof(f849,plain,(
% 1.88/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_26 | spl4_39)),
% 1.88/0.62    inference(forward_demodulation,[],[f848,f75])).
% 1.88/0.62  fof(f848,plain,(
% 1.88/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (~spl4_4 | ~spl4_26 | spl4_39)),
% 1.88/0.62    inference(forward_demodulation,[],[f382,f362])).
% 1.88/0.62  fof(f382,plain,(
% 1.88/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_26 | spl4_39)),
% 1.88/0.62    inference(resolution,[],[f369,f257])).
% 1.88/0.62  fof(f837,plain,(
% 1.88/0.62    spl4_58 | ~spl4_5 | ~spl4_6),
% 1.88/0.62    inference(avatar_split_clause,[],[f535,f100,f96,f552])).
% 1.88/0.62  fof(f96,plain,(
% 1.88/0.62    spl4_5 <=> k1_xboole_0 = sK0),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.88/0.62  fof(f535,plain,(
% 1.88/0.62    r1_tarski(sK2,k1_xboole_0) | (~spl4_5 | ~spl4_6)),
% 1.88/0.62    inference(superposition,[],[f101,f97])).
% 1.88/0.62  fof(f97,plain,(
% 1.88/0.62    k1_xboole_0 = sK0 | ~spl4_5),
% 1.88/0.62    inference(avatar_component_clause,[],[f96])).
% 1.88/0.62  fof(f101,plain,(
% 1.88/0.62    r1_tarski(sK2,sK0) | ~spl4_6),
% 1.88/0.62    inference(avatar_component_clause,[],[f100])).
% 1.88/0.62  fof(f773,plain,(
% 1.88/0.62    ~spl4_7 | ~spl4_39 | spl4_3 | ~spl4_9),
% 1.88/0.62    inference(avatar_split_clause,[],[f392,f112,f89,f368,f104])).
% 1.88/0.62  fof(f89,plain,(
% 1.88/0.62    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.88/0.62  fof(f112,plain,(
% 1.88/0.62    spl4_9 <=> v1_funct_1(sK3)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.88/0.62  fof(f392,plain,(
% 1.88/0.62    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_9)),
% 1.88/0.62    inference(superposition,[],[f90,f188])).
% 1.88/0.62  fof(f188,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 1.88/0.62    inference(resolution,[],[f72,f113])).
% 1.88/0.62  fof(f113,plain,(
% 1.88/0.62    v1_funct_1(sK3) | ~spl4_9),
% 1.88/0.62    inference(avatar_component_clause,[],[f112])).
% 1.88/0.62  fof(f72,plain,(
% 1.88/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f32])).
% 1.88/0.62  fof(f32,plain,(
% 1.88/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.88/0.62    inference(flattening,[],[f31])).
% 1.88/0.62  fof(f31,plain,(
% 1.88/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.88/0.62    inference(ennf_transformation,[],[f13])).
% 1.88/0.62  fof(f13,axiom,(
% 1.88/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.88/0.62  fof(f90,plain,(
% 1.88/0.62    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.88/0.62    inference(avatar_component_clause,[],[f89])).
% 1.88/0.62  fof(f762,plain,(
% 1.88/0.62    ~spl4_25 | spl4_87 | ~spl4_59),
% 1.88/0.62    inference(avatar_split_clause,[],[f679,f560,f760,f240])).
% 1.88/0.62  fof(f240,plain,(
% 1.88/0.62    spl4_25 <=> r1_tarski(sK3,k1_xboole_0)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.88/0.62  fof(f560,plain,(
% 1.88/0.62    spl4_59 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.88/0.62  fof(f679,plain,(
% 1.88/0.62    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~r1_tarski(sK3,k1_xboole_0) | ~spl4_59),
% 1.88/0.62    inference(resolution,[],[f561,f175])).
% 1.88/0.62  fof(f175,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~v1_funct_2(X1,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1) | ~r1_tarski(X1,k1_xboole_0)) )),
% 1.88/0.62    inference(resolution,[],[f125,f59])).
% 1.88/0.62  fof(f59,plain,(
% 1.88/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f38])).
% 1.88/0.62  fof(f38,plain,(
% 1.88/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.88/0.62    inference(nnf_transformation,[],[f3])).
% 1.88/0.62  fof(f3,axiom,(
% 1.88/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.88/0.62  fof(f125,plain,(
% 1.88/0.62    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.88/0.62    inference(forward_demodulation,[],[f81,f76])).
% 1.88/0.62  fof(f76,plain,(
% 1.88/0.62    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.88/0.62    inference(equality_resolution,[],[f61])).
% 1.88/0.62  fof(f61,plain,(
% 1.88/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.88/0.62    inference(cnf_transformation,[],[f40])).
% 1.88/0.62  fof(f81,plain,(
% 1.88/0.62    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.88/0.62    inference(equality_resolution,[],[f67])).
% 1.88/0.62  fof(f67,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f41])).
% 1.88/0.62  fof(f561,plain,(
% 1.88/0.62    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl4_59),
% 1.88/0.62    inference(avatar_component_clause,[],[f560])).
% 1.88/0.62  fof(f642,plain,(
% 1.88/0.62    ~spl4_24 | spl4_25),
% 1.88/0.62    inference(avatar_split_clause,[],[f243,f240,f235])).
% 1.88/0.62  fof(f243,plain,(
% 1.88/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl4_25),
% 1.88/0.62    inference(resolution,[],[f241,f58])).
% 1.88/0.62  fof(f58,plain,(
% 1.88/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f38])).
% 1.88/0.62  fof(f241,plain,(
% 1.88/0.62    ~r1_tarski(sK3,k1_xboole_0) | spl4_25),
% 1.88/0.62    inference(avatar_component_clause,[],[f240])).
% 1.88/0.62  fof(f562,plain,(
% 1.88/0.62    spl4_59 | ~spl4_4 | ~spl4_5 | ~spl4_8),
% 1.88/0.62    inference(avatar_split_clause,[],[f558,f108,f96,f93,f560])).
% 1.88/0.62  fof(f558,plain,(
% 1.88/0.62    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.88/0.62    inference(forward_demodulation,[],[f537,f362])).
% 1.88/0.62  fof(f537,plain,(
% 1.88/0.62    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl4_5 | ~spl4_8)),
% 1.88/0.62    inference(superposition,[],[f109,f97])).
% 1.88/0.62  fof(f109,plain,(
% 1.88/0.62    v1_funct_2(sK3,sK0,sK1) | ~spl4_8),
% 1.88/0.62    inference(avatar_component_clause,[],[f108])).
% 1.88/0.62  fof(f557,plain,(
% 1.88/0.62    spl4_24 | ~spl4_5 | ~spl4_7),
% 1.88/0.62    inference(avatar_split_clause,[],[f555,f104,f96,f235])).
% 1.88/0.62  fof(f555,plain,(
% 1.88/0.62    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl4_5 | ~spl4_7)),
% 1.88/0.62    inference(forward_demodulation,[],[f536,f76])).
% 1.88/0.62  fof(f536,plain,(
% 1.88/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_5 | ~spl4_7)),
% 1.88/0.62    inference(superposition,[],[f105,f97])).
% 1.88/0.62  fof(f381,plain,(
% 1.88/0.62    ~spl4_39 | ~spl4_41 | spl4_40),
% 1.88/0.62    inference(avatar_split_clause,[],[f376,f371,f379,f368])).
% 1.88/0.62  fof(f371,plain,(
% 1.88/0.62    spl4_40 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 1.88/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.88/0.62  fof(f376,plain,(
% 1.88/0.62    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_40),
% 1.88/0.62    inference(superposition,[],[f372,f63])).
% 1.88/0.62  fof(f372,plain,(
% 1.88/0.62    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_40),
% 1.88/0.62    inference(avatar_component_clause,[],[f371])).
% 1.88/0.62  fof(f373,plain,(
% 1.88/0.62    ~spl4_39 | spl4_4 | ~spl4_40 | spl4_21),
% 1.88/0.62    inference(avatar_split_clause,[],[f361,f214,f371,f93,f368])).
% 1.88/0.62  fof(f361,plain,(
% 1.88/0.62    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_21),
% 1.88/0.62    inference(resolution,[],[f68,f215])).
% 1.88/0.62  fof(f68,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f41])).
% 1.88/0.62  fof(f258,plain,(
% 1.88/0.62    ~spl4_9 | spl4_26 | ~spl4_9),
% 1.88/0.62    inference(avatar_split_clause,[],[f253,f112,f256,f112])).
% 1.88/0.62  fof(f253,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3)) ) | ~spl4_9),
% 1.88/0.62    inference(duplicate_literal_removal,[],[f250])).
% 1.88/0.62  fof(f250,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 1.88/0.62    inference(superposition,[],[f74,f188])).
% 1.88/0.62  fof(f74,plain,(
% 1.88/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f34])).
% 1.88/0.62  fof(f34,plain,(
% 1.88/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.88/0.62    inference(flattening,[],[f33])).
% 1.88/0.62  fof(f33,plain,(
% 1.88/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.88/0.62    inference(ennf_transformation,[],[f12])).
% 1.88/0.62  fof(f12,axiom,(
% 1.88/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.88/0.62  fof(f237,plain,(
% 1.88/0.62    ~spl4_24 | spl4_22),
% 1.88/0.62    inference(avatar_split_clause,[],[f233,f225,f235])).
% 1.88/0.62  fof(f233,plain,(
% 1.88/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl4_22),
% 1.88/0.62    inference(superposition,[],[f231,f75])).
% 1.88/0.62  fof(f231,plain,(
% 1.88/0.62    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl4_22),
% 1.88/0.62    inference(resolution,[],[f226,f64])).
% 1.88/0.62  fof(f64,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f28])).
% 1.88/0.62  fof(f226,plain,(
% 1.88/0.62    ~v4_relat_1(sK3,sK2) | spl4_22),
% 1.88/0.62    inference(avatar_component_clause,[],[f225])).
% 1.88/0.62  fof(f218,plain,(
% 1.88/0.62    ~spl4_7 | ~spl4_17),
% 1.88/0.62    inference(avatar_contradiction_clause,[],[f217])).
% 1.88/0.63  fof(f217,plain,(
% 1.88/0.63    $false | (~spl4_7 | ~spl4_17)),
% 1.88/0.63    inference(subsumption_resolution,[],[f105,f200])).
% 1.88/0.63  fof(f200,plain,(
% 1.88/0.63    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_17),
% 1.88/0.63    inference(avatar_component_clause,[],[f199])).
% 1.88/0.63  fof(f199,plain,(
% 1.88/0.63    spl4_17 <=> ! [X1,X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 1.88/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.88/0.63  fof(f216,plain,(
% 1.88/0.63    ~spl4_7 | ~spl4_21 | spl4_2 | ~spl4_9),
% 1.88/0.63    inference(avatar_split_clause,[],[f194,f112,f86,f214,f104])).
% 1.88/0.63  fof(f86,plain,(
% 1.88/0.63    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.88/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.88/0.63  fof(f194,plain,(
% 1.88/0.63    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_2 | ~spl4_9)),
% 1.88/0.63    inference(superposition,[],[f87,f188])).
% 1.88/0.63  fof(f87,plain,(
% 1.88/0.63    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.88/0.63    inference(avatar_component_clause,[],[f86])).
% 1.88/0.63  fof(f212,plain,(
% 1.88/0.63    spl4_17 | spl4_20 | ~spl4_9),
% 1.88/0.63    inference(avatar_split_clause,[],[f195,f112,f210,f199])).
% 1.88/0.63  fof(f195,plain,(
% 1.88/0.63    ( ! [X12,X10,X11] : (v1_funct_1(k7_relat_1(sK3,X12)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) | ~spl4_9),
% 1.88/0.63    inference(duplicate_literal_removal,[],[f193])).
% 1.88/0.63  fof(f193,plain,(
% 1.88/0.63    ( ! [X12,X10,X11] : (v1_funct_1(k7_relat_1(sK3,X12)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) | ~spl4_9),
% 1.88/0.63    inference(superposition,[],[f163,f188])).
% 1.88/0.63  fof(f163,plain,(
% 1.88/0.63    ( ! [X2,X0,X1] : (v1_funct_1(k2_partfun1(X0,X1,sK3,X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 1.88/0.63    inference(resolution,[],[f73,f113])).
% 1.88/0.63  fof(f73,plain,(
% 1.88/0.63    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.88/0.63    inference(cnf_transformation,[],[f34])).
% 1.88/0.63  fof(f204,plain,(
% 1.88/0.63    spl4_17 | spl4_18 | ~spl4_9),
% 1.88/0.63    inference(avatar_split_clause,[],[f197,f112,f202,f199])).
% 1.88/0.63  fof(f197,plain,(
% 1.88/0.63    ( ! [X2,X0,X3,X1] : (v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k7_relat_1(sK3,X2))) ) | ~spl4_9),
% 1.88/0.63    inference(duplicate_literal_removal,[],[f191])).
% 1.88/0.63  fof(f191,plain,(
% 1.88/0.63    ( ! [X2,X0,X3,X1] : (v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k7_relat_1(sK3,X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 1.88/0.63    inference(superposition,[],[f166,f188])).
% 1.88/0.63  fof(f166,plain,(
% 1.88/0.63    ( ! [X6,X8,X7,X9] : (v1_funct_2(k2_partfun1(X6,X7,sK3,X8),k1_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9) | ~r1_tarski(k2_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_relat_1(k2_partfun1(X6,X7,sK3,X8))) ) | ~spl4_9),
% 1.88/0.63    inference(resolution,[],[f163,f55])).
% 1.88/0.63  fof(f55,plain,(
% 1.88/0.63    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f24])).
% 1.88/0.63  fof(f168,plain,(
% 1.88/0.63    ~spl4_7 | spl4_1 | ~spl4_9),
% 1.88/0.63    inference(avatar_split_clause,[],[f164,f112,f83,f104])).
% 1.88/0.63  fof(f83,plain,(
% 1.88/0.63    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.88/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.88/0.63  fof(f164,plain,(
% 1.88/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_1 | ~spl4_9)),
% 1.88/0.63    inference(resolution,[],[f163,f84])).
% 1.88/0.63  fof(f84,plain,(
% 1.88/0.63    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.88/0.63    inference(avatar_component_clause,[],[f83])).
% 1.88/0.63  fof(f161,plain,(
% 1.88/0.63    spl4_16),
% 1.88/0.63    inference(avatar_contradiction_clause,[],[f159])).
% 1.88/0.63  fof(f159,plain,(
% 1.88/0.63    $false | spl4_16),
% 1.88/0.63    inference(resolution,[],[f157,f50])).
% 1.88/0.63  fof(f157,plain,(
% 1.88/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_16),
% 1.88/0.63    inference(avatar_component_clause,[],[f156])).
% 1.88/0.63  fof(f156,plain,(
% 1.88/0.63    spl4_16 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.88/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.88/0.63  fof(f158,plain,(
% 1.88/0.63    ~spl4_16 | ~spl4_7 | spl4_14),
% 1.88/0.63    inference(avatar_split_clause,[],[f153,f146,f104,f156])).
% 1.88/0.63  fof(f153,plain,(
% 1.88/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl4_7 | spl4_14)),
% 1.88/0.63    inference(resolution,[],[f152,f105])).
% 1.88/0.63  fof(f152,plain,(
% 1.88/0.63    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_14),
% 1.88/0.63    inference(resolution,[],[f147,f49])).
% 1.88/0.63  fof(f147,plain,(
% 1.88/0.63    ~v1_relat_1(sK3) | spl4_14),
% 1.88/0.63    inference(avatar_component_clause,[],[f146])).
% 1.88/0.63  fof(f114,plain,(
% 1.88/0.63    spl4_9),
% 1.88/0.63    inference(avatar_split_clause,[],[f42,f112])).
% 1.88/0.63  fof(f42,plain,(
% 1.88/0.63    v1_funct_1(sK3)),
% 1.88/0.63    inference(cnf_transformation,[],[f36])).
% 1.88/0.63  fof(f36,plain,(
% 1.88/0.63    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.88/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f35])).
% 1.88/0.63  fof(f35,plain,(
% 1.88/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.88/0.63    introduced(choice_axiom,[])).
% 1.88/0.63  fof(f18,plain,(
% 1.88/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.88/0.63    inference(flattening,[],[f17])).
% 1.88/0.63  fof(f17,plain,(
% 1.88/0.63    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.88/0.63    inference(ennf_transformation,[],[f16])).
% 1.88/0.63  fof(f16,negated_conjecture,(
% 1.88/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.88/0.63    inference(negated_conjecture,[],[f15])).
% 1.88/0.63  fof(f15,conjecture,(
% 1.88/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.88/0.63  fof(f110,plain,(
% 1.88/0.63    spl4_8),
% 1.88/0.63    inference(avatar_split_clause,[],[f43,f108])).
% 1.88/0.63  fof(f43,plain,(
% 1.88/0.63    v1_funct_2(sK3,sK0,sK1)),
% 1.88/0.63    inference(cnf_transformation,[],[f36])).
% 1.88/0.63  fof(f106,plain,(
% 1.88/0.63    spl4_7),
% 1.88/0.63    inference(avatar_split_clause,[],[f44,f104])).
% 1.88/0.64  fof(f44,plain,(
% 1.88/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.88/0.64    inference(cnf_transformation,[],[f36])).
% 1.88/0.64  fof(f102,plain,(
% 1.88/0.64    spl4_6),
% 1.88/0.64    inference(avatar_split_clause,[],[f45,f100])).
% 1.88/0.64  fof(f45,plain,(
% 1.88/0.64    r1_tarski(sK2,sK0)),
% 1.88/0.64    inference(cnf_transformation,[],[f36])).
% 1.88/0.64  fof(f98,plain,(
% 1.88/0.64    ~spl4_4 | spl4_5),
% 1.88/0.64    inference(avatar_split_clause,[],[f46,f96,f93])).
% 1.88/0.64  fof(f46,plain,(
% 1.88/0.64    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.88/0.64    inference(cnf_transformation,[],[f36])).
% 1.88/0.64  fof(f91,plain,(
% 1.88/0.64    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.88/0.64    inference(avatar_split_clause,[],[f47,f89,f86,f83])).
% 1.88/0.64  fof(f47,plain,(
% 1.88/0.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.88/0.64    inference(cnf_transformation,[],[f36])).
% 1.88/0.64  % SZS output end Proof for theBenchmark
% 1.88/0.64  % (19094)------------------------------
% 1.88/0.64  % (19094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.64  % (19094)Termination reason: Refutation
% 1.88/0.64  
% 1.88/0.64  % (19094)Memory used [KB]: 11641
% 1.88/0.64  % (19094)Time elapsed: 0.171 s
% 1.88/0.64  % (19094)------------------------------
% 1.88/0.64  % (19094)------------------------------
% 1.88/0.64  % (19087)Success in time 0.276 s
%------------------------------------------------------------------------------
