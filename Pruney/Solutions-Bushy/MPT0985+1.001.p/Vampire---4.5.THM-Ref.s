%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0985+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:01 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  377 ( 762 expanded)
%              Number of leaves         :   89 ( 367 expanded)
%              Depth                    :    9
%              Number of atoms          : 1227 (2350 expanded)
%              Number of equality atoms :  156 ( 407 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1824,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f97,f101,f111,f115,f119,f125,f135,f139,f143,f151,f155,f161,f165,f169,f173,f181,f185,f189,f193,f197,f201,f213,f221,f241,f254,f258,f269,f273,f279,f296,f319,f328,f346,f362,f401,f421,f440,f444,f482,f486,f497,f505,f612,f658,f684,f728,f729,f758,f761,f769,f775,f822,f852,f857,f865,f876,f894,f1054,f1062,f1119,f1181,f1243,f1313,f1322,f1366,f1481,f1495,f1527,f1676,f1805,f1823])).

fof(f1823,plain,
    ( spl4_55
    | ~ spl4_66
    | ~ spl4_91 ),
    inference(avatar_split_clause,[],[f1713,f863,f682,f477])).

fof(f477,plain,
    ( spl4_55
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f682,plain,
    ( spl4_66
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f863,plain,
    ( spl4_91
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
        | k1_xboole_0 = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1713,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_66
    | ~ spl4_91 ),
    inference(resolution,[],[f683,f864])).

fof(f864,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
        | k1_xboole_0 = X5 )
    | ~ spl4_91 ),
    inference(avatar_component_clause,[],[f863])).

fof(f683,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f682])).

fof(f1805,plain,
    ( ~ spl4_4
    | ~ spl4_13
    | ~ spl4_56
    | ~ spl4_74 ),
    inference(avatar_contradiction_clause,[],[f1804])).

fof(f1804,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_13
    | ~ spl4_56
    | ~ spl4_74 ),
    inference(subsumption_resolution,[],[f1803,f124])).

fof(f124,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1803,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_56
    | ~ spl4_74 ),
    inference(forward_demodulation,[],[f776,f481])).

fof(f481,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl4_56
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f776,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(resolution,[],[f768,f88])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f768,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl4_74
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1676,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | ~ spl4_40
    | ~ spl4_44
    | ~ spl4_56
    | ~ spl4_160 ),
    inference(avatar_contradiction_clause,[],[f1675])).

fof(f1675,plain,
    ( $false
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | ~ spl4_40
    | ~ spl4_44
    | ~ spl4_56
    | ~ spl4_160 ),
    inference(subsumption_resolution,[],[f1642,f1486])).

fof(f1486,plain,
    ( ! [X6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
    | ~ spl4_7
    | ~ spl4_160 ),
    inference(superposition,[],[f100,f1480])).

fof(f1480,plain,
    ( ! [X11] : k1_xboole_0 = sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X11)))
    | ~ spl4_160 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1479,plain,
    ( spl4_160
  <=> ! [X11] : k1_xboole_0 = sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f100,plain,
    ( ! [X0] : m1_subset_1(sK3(X0),X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_7
  <=> ! [X0] : m1_subset_1(sK3(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1642,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_8
    | ~ spl4_11
    | ~ spl4_40
    | ~ spl4_44
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f1609,f1627])).

fof(f1627,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_11
    | ~ spl4_44 ),
    inference(resolution,[],[f282,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f282,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl4_44
  <=> v1_xboole_0(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1609,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_8
    | ~ spl4_40
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f1548,f481])).

fof(f1548,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_8
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f104,f262])).

fof(f262,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl4_40
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f104,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1527,plain,
    ( spl4_130
    | ~ spl4_139
    | ~ spl4_161 ),
    inference(avatar_contradiction_clause,[],[f1502])).

fof(f1502,plain,
    ( $false
    | spl4_130
    | ~ spl4_139
    | ~ spl4_161 ),
    inference(unit_resulting_resolution,[],[f1312,f1494,f1365])).

fof(f1365,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) )
    | ~ spl4_139 ),
    inference(avatar_component_clause,[],[f1364])).

fof(f1364,plain,
    ( spl4_139
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f1494,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_161 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1493,plain,
    ( spl4_161
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_161])])).

fof(f1312,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_130 ),
    inference(avatar_component_clause,[],[f1311])).

fof(f1311,plain,
    ( spl4_130
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f1495,plain,
    ( spl4_161
    | ~ spl4_92
    | ~ spl4_132
    | ~ spl4_160 ),
    inference(avatar_split_clause,[],[f1487,f1479,f1320,f874,f1493])).

fof(f874,plain,
    ( spl4_92
  <=> ! [X1,X0] : m1_subset_1(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f1320,plain,
    ( spl4_132
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f1487,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_92
    | ~ spl4_132
    | ~ spl4_160 ),
    inference(forward_demodulation,[],[f1482,f1321])).

fof(f1321,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_132 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f1482,plain,
    ( ! [X0] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_92
    | ~ spl4_160 ),
    inference(superposition,[],[f875,f1480])).

fof(f875,plain,
    ( ! [X0,X1] : m1_subset_1(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f874])).

fof(f1481,plain,
    ( spl4_160
    | ~ spl4_7
    | ~ spl4_91 ),
    inference(avatar_split_clause,[],[f871,f863,f99,f1479])).

fof(f871,plain,
    ( ! [X11] : k1_xboole_0 = sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X11)))
    | ~ spl4_7
    | ~ spl4_91 ),
    inference(resolution,[],[f864,f100])).

fof(f1366,plain,
    ( spl4_139
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55
    | ~ spl4_82
    | ~ spl4_124 ),
    inference(avatar_split_clause,[],[f1260,f1241,f820,f477,f219,f171,f123,f113,f1364])).

fof(f171,plain,
    ( spl4_23
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f219,plain,
    ( spl4_32
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f820,plain,
    ( spl4_82
  <=> ! [X3,X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1241,plain,
    ( spl4_124
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f1260,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) )
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55
    | ~ spl4_82
    | ~ spl4_124 ),
    inference(backward_demodulation,[],[f1202,f1251])).

fof(f1251,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_124 ),
    inference(resolution,[],[f1242,f114])).

fof(f1242,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl4_124 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1202,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f1149,f1182])).

fof(f1182,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f1141,f124])).

fof(f1141,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55 ),
    inference(backward_demodulation,[],[f697,f478])).

fof(f478,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f477])).

fof(f697,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_xboole_0(sK2)
    | ~ spl4_23
    | ~ spl4_32 ),
    inference(superposition,[],[f172,f220])).

fof(f220,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f219])).

fof(f172,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f171])).

fof(f1149,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(sK1,k1_zfmisc_1(X2)) )
    | ~ spl4_55
    | ~ spl4_82 ),
    inference(backward_demodulation,[],[f821,f478])).

fof(f821,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(sK1,k1_zfmisc_1(X2)) )
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f820])).

fof(f1322,plain,
    ( spl4_132
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f1190,f477,f219,f171,f123,f1320])).

fof(f1190,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55 ),
    inference(backward_demodulation,[],[f1131,f1182])).

fof(f1131,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | ~ spl4_32
    | ~ spl4_55 ),
    inference(backward_demodulation,[],[f220,f478])).

fof(f1313,plain,
    ( ~ spl4_130
    | spl4_8
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55
    | ~ spl4_124 ),
    inference(avatar_split_clause,[],[f1266,f1241,f477,f219,f171,f123,f113,f103,f1311])).

fof(f1266,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_8
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55
    | ~ spl4_124 ),
    inference(backward_demodulation,[],[f1231,f1251])).

fof(f1231,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_8
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f1230,f478])).

fof(f1230,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_8
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_32
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f104,f1182])).

fof(f1243,plain,
    ( spl4_124
    | ~ spl4_44
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f1228,f477,f281,f1241])).

fof(f1228,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl4_44
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f282,f478])).

fof(f1181,plain,
    ( ~ spl4_55
    | ~ spl4_62
    | spl4_64 ),
    inference(avatar_contradiction_clause,[],[f1180])).

fof(f1180,plain,
    ( $false
    | ~ spl4_55
    | ~ spl4_62
    | spl4_64 ),
    inference(subsumption_resolution,[],[f1139,f657])).

fof(f657,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_64 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl4_64
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f1139,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_55
    | ~ spl4_62 ),
    inference(backward_demodulation,[],[f610,f478])).

fof(f610,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl4_62
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1119,plain,
    ( ~ spl4_8
    | spl4_9
    | spl4_56
    | ~ spl4_89 ),
    inference(avatar_contradiction_clause,[],[f1118])).

fof(f1118,plain,
    ( $false
    | ~ spl4_8
    | spl4_9
    | spl4_56
    | ~ spl4_89 ),
    inference(subsumption_resolution,[],[f1117,f107])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1117,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_8
    | spl4_56
    | ~ spl4_89 ),
    inference(subsumption_resolution,[],[f1111,f826])).

fof(f826,plain,
    ( k1_xboole_0 != sK0
    | spl4_56 ),
    inference(avatar_component_clause,[],[f480])).

fof(f1111,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_8
    | ~ spl4_89 ),
    inference(trivial_inequality_removal,[],[f1107])).

fof(f1107,plain,
    ( k1_xboole_0 = sK0
    | sK1 != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_8
    | ~ spl4_89 ),
    inference(resolution,[],[f1077,f856])).

fof(f856,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = X3
        | sK1 != X2
        | v1_funct_2(k2_funct_1(sK2),X2,X3) )
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f855])).

fof(f855,plain,
    ( spl4_89
  <=> ! [X3,X2] :
        ( sK1 != X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_2(k2_funct_1(sK2),X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f1077,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f1062,plain,
    ( spl4_8
    | ~ spl4_38
    | ~ spl4_60
    | ~ spl4_116 ),
    inference(avatar_contradiction_clause,[],[f1059])).

fof(f1059,plain,
    ( $false
    | spl4_8
    | ~ spl4_38
    | ~ spl4_60
    | ~ spl4_116 ),
    inference(unit_resulting_resolution,[],[f504,f253,f104,f1053])).

fof(f1053,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK0,k1_zfmisc_1(X1)) )
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f1052])).

fof(f1052,plain,
    ( spl4_116
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f253,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl4_38
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f504,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl4_60
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f1054,plain,
    ( spl4_116
    | ~ spl4_19
    | ~ spl4_95 ),
    inference(avatar_split_clause,[],[f899,f892,f149,f1052])).

fof(f149,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f892,plain,
    ( spl4_95
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f899,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK0,k1_zfmisc_1(X1)) )
    | ~ spl4_19
    | ~ spl4_95 ),
    inference(resolution,[],[f893,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f893,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) )
    | ~ spl4_95 ),
    inference(avatar_component_clause,[],[f892])).

fof(f894,plain,
    ( spl4_95
    | ~ spl4_19
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f853,f850,f149,f892])).

fof(f850,plain,
    ( spl4_88
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_tarski(sK1,X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f853,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) )
    | ~ spl4_19
    | ~ spl4_88 ),
    inference(resolution,[],[f851,f150])).

fof(f851,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(sK0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f850])).

fof(f876,plain,
    ( spl4_92
    | ~ spl4_7
    | ~ spl4_28
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f760,f756,f195,f99,f874])).

fof(f195,plain,
    ( spl4_28
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f756,plain,
    ( spl4_72
  <=> ! [X1,X0] : k2_relset_1(X0,X1,sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f760,plain,
    ( ! [X0,X1] : m1_subset_1(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1))
    | ~ spl4_7
    | ~ spl4_28
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f759,f100])).

fof(f759,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1))
        | ~ m1_subset_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_28
    | ~ spl4_72 ),
    inference(superposition,[],[f196,f757])).

fof(f757,plain,
    ( ! [X0,X1] : k2_relset_1(X0,X1,sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f756])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f195])).

fof(f865,plain,
    ( spl4_91
    | ~ spl4_13
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f492,f484,f123,f863])).

fof(f484,plain,
    ( spl4_57
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f492,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
        | k1_xboole_0 = X5 )
    | ~ spl4_13
    | ~ spl4_57 ),
    inference(resolution,[],[f485,f124])).

fof(f485,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X0 )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f484])).

fof(f857,plain,
    ( spl4_89
    | ~ spl4_41
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f779,f773,f267,f855])).

fof(f267,plain,
    ( spl4_41
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f773,plain,
    ( spl4_75
  <=> ! [X1,X0,X2] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f779,plain,
    ( ! [X2,X3] :
        ( sK1 != X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_2(k2_funct_1(sK2),X2,X3) )
    | ~ spl4_41
    | ~ spl4_75 ),
    inference(superposition,[],[f774,f268])).

fof(f268,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f267])).

fof(f774,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f773])).

fof(f852,plain,
    ( ~ spl4_45
    | spl4_88
    | ~ spl4_35
    | ~ spl4_41
    | ~ spl4_46
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f690,f399,f294,f267,f239,f850,f284])).

fof(f284,plain,
    ( spl4_45
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f239,plain,
    ( spl4_35
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ r1_tarski(k2_relat_1(X2),X1)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f294,plain,
    ( spl4_46
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f399,plain,
    ( spl4_51
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f690,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_tarski(sK1,X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_35
    | ~ spl4_41
    | ~ spl4_46
    | ~ spl4_51 ),
    inference(backward_demodulation,[],[f297,f400])).

fof(f400,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f399])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | ~ r1_tarski(sK1,X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_35
    | ~ spl4_41
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f274,f295])).

fof(f295,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f294])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_35
    | ~ spl4_41 ),
    inference(superposition,[],[f240,f268])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k2_relat_1(X2),X1)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f239])).

fof(f822,plain,
    ( spl4_82
    | ~ spl4_41
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f501,f495,f267,f820])).

fof(f495,plain,
    ( spl4_59
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f501,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl4_41
    | ~ spl4_59 ),
    inference(superposition,[],[f496,f268])).

fof(f496,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f495])).

fof(f775,plain,
    ( spl4_75
    | ~ spl4_26
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f289,f271,f187,f773])).

fof(f187,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f271,plain,
    ( spl4_42
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f289,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl4_26
    | ~ spl4_42 ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_26
    | ~ spl4_42 ),
    inference(superposition,[],[f272,f188])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f187])).

fof(f272,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f271])).

fof(f769,plain,
    ( spl4_74
    | ~ spl4_22
    | spl4_33 ),
    inference(avatar_split_clause,[],[f692,f232,f167,f767])).

fof(f167,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f232,plain,
    ( spl4_33
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f692,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_22
    | spl4_33 ),
    inference(resolution,[],[f233,f168])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f167])).

fof(f233,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f232])).

fof(f761,plain,
    ( spl4_44
    | ~ spl4_45
    | ~ spl4_34
    | ~ spl4_15
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f330,f267,f133,f235,f284,f281])).

fof(f235,plain,
    ( spl4_34
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f133,plain,
    ( spl4_15
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f330,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ spl4_15
    | ~ spl4_41 ),
    inference(superposition,[],[f134,f268])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f758,plain,
    ( spl4_72
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f215,f191,f99,f756])).

fof(f191,plain,
    ( spl4_27
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f215,plain,
    ( ! [X0,X1] : k2_relset_1(X0,X1,sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(resolution,[],[f192,f100])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f191])).

fof(f729,plain,
    ( spl4_47
    | spl4_40
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f506,f277,f87,f83,f261,f305])).

fof(f305,plain,
    ( spl4_47
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f83,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f277,plain,
    ( spl4_43
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f506,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f449,f88])).

fof(f449,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_43 ),
    inference(resolution,[],[f84,f278])).

fof(f278,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f277])).

fof(f84,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f728,plain,
    ( ~ spl4_33
    | spl4_40
    | ~ spl4_23
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f322,f219,f171,f261,f232])).

fof(f322,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_xboole_0(sK2)
    | ~ spl4_23
    | ~ spl4_32 ),
    inference(superposition,[],[f220,f172])).

fof(f684,plain,
    ( spl4_66
    | ~ spl4_54
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f643,f480,f442,f682])).

fof(f442,plain,
    ( spl4_54
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f643,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_54
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f443,f481])).

fof(f443,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f442])).

fof(f658,plain,
    ( ~ spl4_64
    | spl4_53
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f646,f480,f438,f656])).

fof(f438,plain,
    ( spl4_53
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f646,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_53
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f439,f481])).

fof(f439,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f438])).

fof(f612,plain,
    ( spl4_62
    | ~ spl4_49
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f594,f480,f360,f609])).

fof(f360,plain,
    ( spl4_49
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f594,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_49
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f361,f481])).

fof(f361,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f360])).

fof(f505,plain,
    ( spl4_60
    | ~ spl4_4
    | ~ spl4_29
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f469,f305,f199,f87,f503])).

fof(f199,plain,
    ( spl4_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f469,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_29
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f466,f88])).

fof(f466,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_29
    | ~ spl4_47 ),
    inference(superposition,[],[f200,f306])).

fof(f306,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f305])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f199])).

fof(f497,plain,
    ( spl4_59
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f230,f199,f187,f495])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(superposition,[],[f200,f188])).

fof(f486,plain,
    ( spl4_57
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f174,f167,f113,f484])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(resolution,[],[f168,f114])).

fof(f482,plain,
    ( ~ spl4_54
    | spl4_55
    | spl4_56
    | ~ spl4_39
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f415,f360,f256,f480,f477,f442])).

fof(f256,plain,
    ( spl4_39
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f415,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_39
    | ~ spl4_49 ),
    inference(resolution,[],[f361,f257])).

fof(f257,plain,
    ( ! [X2,X0] :
        ( ~ v1_funct_2(X2,X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f256])).

fof(f444,plain,
    ( spl4_54
    | ~ spl4_4
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f405,f261,f87,f442])).

fof(f405,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_40 ),
    inference(backward_demodulation,[],[f88,f262])).

fof(f440,plain,
    ( ~ spl4_53
    | ~ spl4_11
    | ~ spl4_44
    | spl4_52 ),
    inference(avatar_split_clause,[],[f430,f419,f281,f113,f438])).

fof(f419,plain,
    ( spl4_52
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f430,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl4_11
    | ~ spl4_44
    | spl4_52 ),
    inference(backward_demodulation,[],[f420,f422])).

fof(f422,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_11
    | ~ spl4_44 ),
    inference(resolution,[],[f282,f114])).

fof(f420,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_52 ),
    inference(avatar_component_clause,[],[f419])).

fof(f421,plain,
    ( ~ spl4_52
    | spl4_9
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f408,f261,f106,f419])).

fof(f408,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_9
    | ~ spl4_40 ),
    inference(backward_demodulation,[],[f107,f262])).

fof(f401,plain,
    ( spl4_51
    | ~ spl4_46
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f363,f344,f294,f399])).

fof(f344,plain,
    ( spl4_48
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f363,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_46
    | ~ spl4_48 ),
    inference(backward_demodulation,[],[f295,f345])).

fof(f345,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f344])).

fof(f362,plain,
    ( spl4_49
    | ~ spl4_3
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f348,f261,f83,f360])).

fof(f348,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_40 ),
    inference(backward_demodulation,[],[f84,f262])).

fof(f346,plain,
    ( spl4_48
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f341,f305,f294,f187,f87,f344])).

fof(f341,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(backward_demodulation,[],[f295,f337])).

fof(f337,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f332,f88])).

fof(f332,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_26
    | ~ spl4_47 ),
    inference(superposition,[],[f306,f188])).

fof(f328,plain,
    ( ~ spl4_21
    | ~ spl4_1
    | ~ spl4_16
    | spl4_45 ),
    inference(avatar_split_clause,[],[f300,f284,f137,f75,f159])).

fof(f159,plain,
    ( spl4_21
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f75,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f137,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f300,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_16
    | spl4_45 ),
    inference(subsumption_resolution,[],[f298,f76])).

fof(f76,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f298,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_16
    | spl4_45 ),
    inference(resolution,[],[f285,f138])).

fof(f138,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f137])).

fof(f285,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f284])).

fof(f319,plain,
    ( ~ spl4_13
    | spl4_34
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl4_13
    | spl4_34
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f316,f124])).

fof(f316,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_34
    | ~ spl4_40 ),
    inference(backward_demodulation,[],[f286,f262])).

fof(f286,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f235])).

fof(f296,plain,
    ( spl4_46
    | ~ spl4_21
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f209,f183,f79,f75,f159,f294])).

fof(f79,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f183,plain,
    ( spl4_25
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f209,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f208,f76])).

fof(f208,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(resolution,[],[f184,f80])).

fof(f80,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f183])).

fof(f279,plain,(
    spl4_43 ),
    inference(avatar_split_clause,[],[f68,f277])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f273,plain,(
    spl4_42 ),
    inference(avatar_split_clause,[],[f67,f271])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f269,plain,
    ( spl4_41
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f217,f211,f191,f91,f87,f267])).

fof(f91,plain,
    ( spl4_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f211,plain,
    ( spl4_31
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f217,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f212,f216])).

fof(f216,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f214,f92])).

fof(f92,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f214,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(resolution,[],[f192,f88])).

fof(f212,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f211])).

fof(f258,plain,(
    spl4_39 ),
    inference(avatar_split_clause,[],[f71,f256])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f254,plain,
    ( spl4_38
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f224,f195,f91,f87,f252])).

fof(f224,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f223,f88])).

fof(f223,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(superposition,[],[f196,f92])).

fof(f241,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f57,f239])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f221,plain,
    ( spl4_32
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f216,f191,f91,f87,f219])).

fof(f213,plain,
    ( spl4_31
    | ~ spl4_21
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f207,f179,f79,f75,f159,f211])).

fof(f179,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f207,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f206,f76])).

fof(f206,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(resolution,[],[f180,f80])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f179])).

fof(f201,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f62,f199])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f197,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f61,f195])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f193,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f60,f191])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f189,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f59,f187])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f185,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f52,f183])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f181,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f51,f179])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,
    ( spl4_23
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f131,f117,f113,f171])).

fof(f117,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_relat_1(X0) )
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f118,f114])).

fof(f118,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f169,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f54,f167])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f165,plain,
    ( ~ spl4_4
    | ~ spl4_20
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_20
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f160,f88,f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f160,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( ~ spl4_21
    | ~ spl4_1
    | spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f157,f141,f109,f75,f159])).

fof(f109,plain,
    ( spl4_10
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f141,plain,
    ( spl4_17
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f157,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_1
    | spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f156,f76])).

fof(f156,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_10
    | ~ spl4_17 ),
    inference(resolution,[],[f142,f110])).

fof(f110,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f142,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f155,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f58,f153])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f151,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f56,f149])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f143,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f50,f141])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f139,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f49,f137])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f135,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f48,f133])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f125,plain,
    ( spl4_13
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f121,f113,f95,f123])).

fof(f95,plain,
    ( spl4_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f121,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f96,f120])).

fof(f120,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(resolution,[],[f114,f96])).

fof(f96,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f119,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f47,f117])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f115,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f46,f113])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f111,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f39,f109,f106,f103])).

fof(f39,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f101,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f97,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f45,f95])).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f93,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f41,f83])).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
