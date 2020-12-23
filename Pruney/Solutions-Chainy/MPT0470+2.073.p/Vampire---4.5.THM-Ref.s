%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  268 ( 550 expanded)
%              Number of leaves         :   69 ( 240 expanded)
%              Depth                    :   12
%              Number of atoms          :  753 (1362 expanded)
%              Number of equality atoms :  175 ( 397 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1584,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f94,f99,f104,f108,f112,f116,f120,f128,f138,f159,f171,f210,f214,f218,f246,f256,f273,f300,f320,f325,f403,f433,f535,f564,f769,f773,f864,f922,f945,f966,f973,f1174,f1201,f1254,f1288,f1297,f1318,f1379,f1408,f1425,f1551,f1583])).

fof(f1583,plain,
    ( spl1_17
    | ~ spl1_22
    | ~ spl1_35
    | ~ spl1_93
    | ~ spl1_111
    | ~ spl1_115 ),
    inference(avatar_contradiction_clause,[],[f1582])).

fof(f1582,plain,
    ( $false
    | spl1_17
    | ~ spl1_22
    | ~ spl1_35
    | ~ spl1_93
    | ~ spl1_111
    | ~ spl1_115 ),
    inference(subsumption_resolution,[],[f170,f1484])).

fof(f1484,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_22
    | ~ spl1_35
    | ~ spl1_93
    | ~ spl1_111
    | ~ spl1_115 ),
    inference(forward_demodulation,[],[f1483,f209])).

fof(f209,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl1_22
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f1483,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0))
    | ~ spl1_35
    | ~ spl1_93
    | ~ spl1_111
    | ~ spl1_115 ),
    inference(forward_demodulation,[],[f1482,f1253])).

fof(f1253,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_111 ),
    inference(avatar_component_clause,[],[f1252])).

fof(f1252,plain,
    ( spl1_111
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_111])])).

fof(f1482,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)))
    | ~ spl1_35
    | ~ spl1_93
    | ~ spl1_115 ),
    inference(forward_demodulation,[],[f1436,f965])).

fof(f965,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_93 ),
    inference(avatar_component_clause,[],[f963])).

fof(f963,plain,
    ( spl1_93
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_93])])).

fof(f1436,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
    | ~ spl1_35
    | ~ spl1_115 ),
    inference(resolution,[],[f1287,f316])).

fof(f316,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_35 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl1_35
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f1287,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 )
    | ~ spl1_115 ),
    inference(avatar_component_clause,[],[f1286])).

fof(f1286,plain,
    ( spl1_115
  <=> ! [X0] :
        ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_115])])).

fof(f170,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl1_17
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f1551,plain,
    ( spl1_16
    | ~ spl1_22
    | ~ spl1_30
    | ~ spl1_34
    | ~ spl1_35
    | ~ spl1_72
    | ~ spl1_93
    | ~ spl1_104
    | ~ spl1_111
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121
    | ~ spl1_124 ),
    inference(avatar_contradiction_clause,[],[f1550])).

fof(f1550,plain,
    ( $false
    | spl1_16
    | ~ spl1_22
    | ~ spl1_30
    | ~ spl1_34
    | ~ spl1_35
    | ~ spl1_72
    | ~ spl1_93
    | ~ spl1_104
    | ~ spl1_111
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121
    | ~ spl1_124 ),
    inference(subsumption_resolution,[],[f1549,f166])).

fof(f166,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl1_16
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f1549,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_22
    | ~ spl1_30
    | ~ spl1_34
    | ~ spl1_35
    | ~ spl1_72
    | ~ spl1_93
    | ~ spl1_104
    | ~ spl1_111
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121
    | ~ spl1_124 ),
    inference(forward_demodulation,[],[f1548,f1173])).

fof(f1173,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_104 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f1171,plain,
    ( spl1_104
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_104])])).

fof(f1548,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_22
    | ~ spl1_30
    | ~ spl1_34
    | ~ spl1_35
    | ~ spl1_72
    | ~ spl1_93
    | ~ spl1_104
    | ~ spl1_111
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121
    | ~ spl1_124 ),
    inference(forward_demodulation,[],[f1547,f1464])).

fof(f1464,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | ~ spl1_22
    | ~ spl1_111
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121
    | ~ spl1_124 ),
    inference(backward_demodulation,[],[f1424,f1445])).

fof(f1445,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_22
    | ~ spl1_111
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121 ),
    inference(forward_demodulation,[],[f1444,f209])).

fof(f1444,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0))
    | ~ spl1_111
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121 ),
    inference(forward_demodulation,[],[f1443,f1253])).

fof(f1443,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0)))
    | ~ spl1_115
    | ~ spl1_120
    | ~ spl1_121 ),
    inference(forward_demodulation,[],[f1432,f1407])).

fof(f1407,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_121 ),
    inference(avatar_component_clause,[],[f1405])).

fof(f1405,plain,
    ( spl1_121
  <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_121])])).

fof(f1432,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))))
    | ~ spl1_115
    | ~ spl1_120 ),
    inference(resolution,[],[f1287,f1378])).

fof(f1378,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_120 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1376,plain,
    ( spl1_120
  <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_120])])).

fof(f1424,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_124 ),
    inference(avatar_component_clause,[],[f1422])).

fof(f1422,plain,
    ( spl1_124
  <=> k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_124])])).

fof(f1547,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_22
    | ~ spl1_30
    | ~ spl1_34
    | ~ spl1_35
    | ~ spl1_72
    | ~ spl1_93
    | ~ spl1_104
    | ~ spl1_111
    | ~ spl1_115 ),
    inference(forward_demodulation,[],[f1503,f1173])).

fof(f1503,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)))
    | ~ spl1_22
    | ~ spl1_30
    | ~ spl1_34
    | ~ spl1_35
    | ~ spl1_72
    | ~ spl1_93
    | ~ spl1_111
    | ~ spl1_115 ),
    inference(backward_demodulation,[],[f910,f1484])).

fof(f910,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0)
    | ~ spl1_30
    | ~ spl1_34
    | ~ spl1_72 ),
    inference(forward_demodulation,[],[f897,f272])).

fof(f272,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl1_30
  <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f897,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),sK0)
    | ~ spl1_34
    | ~ spl1_72 ),
    inference(resolution,[],[f768,f311])).

fof(f311,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_34 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl1_34
  <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).

fof(f768,plain,
    ( ! [X11] :
        ( ~ v1_relat_1(X11)
        | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),sK0) )
    | ~ spl1_72 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl1_72
  <=> ! [X11] :
        ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),sK0)
        | ~ v1_relat_1(X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_72])])).

fof(f1425,plain,
    ( spl1_124
    | ~ spl1_9
    | ~ spl1_116
    | ~ spl1_118 ),
    inference(avatar_split_clause,[],[f1347,f1306,f1294,f118,f1422])).

fof(f118,plain,
    ( spl1_9
  <=> ! [X0] :
        ( k4_relat_1(k4_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f1294,plain,
    ( spl1_116
  <=> k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_116])])).

fof(f1306,plain,
    ( spl1_118
  <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_118])])).

fof(f1347,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_9
    | ~ spl1_116
    | ~ spl1_118 ),
    inference(forward_demodulation,[],[f1334,f1296])).

fof(f1296,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_116 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1334,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))
    | ~ spl1_9
    | ~ spl1_118 ),
    inference(resolution,[],[f1307,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k4_relat_1(X0)) = X0 )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f1307,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_118 ),
    inference(avatar_component_clause,[],[f1306])).

fof(f1408,plain,
    ( spl1_121
    | ~ spl1_9
    | ~ spl1_94
    | ~ spl1_116
    | ~ spl1_118 ),
    inference(avatar_split_clause,[],[f1351,f1306,f1294,f970,f118,f1405])).

fof(f970,plain,
    ( spl1_94
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_94])])).

fof(f1351,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_9
    | ~ spl1_94
    | ~ spl1_116
    | ~ spl1_118 ),
    inference(backward_demodulation,[],[f972,f1347])).

fof(f972,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_94 ),
    inference(avatar_component_clause,[],[f970])).

fof(f1379,plain,
    ( spl1_120
    | ~ spl1_9
    | ~ spl1_116
    | ~ spl1_118 ),
    inference(avatar_split_clause,[],[f1349,f1306,f1294,f118,f1376])).

fof(f1349,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_9
    | ~ spl1_116
    | ~ spl1_118 ),
    inference(backward_demodulation,[],[f1307,f1347])).

fof(f1318,plain,
    ( ~ spl1_12
    | ~ spl1_15
    | ~ spl1_45
    | spl1_118 ),
    inference(avatar_contradiction_clause,[],[f1317])).

fof(f1317,plain,
    ( $false
    | ~ spl1_12
    | ~ spl1_15
    | ~ spl1_45
    | spl1_118 ),
    inference(subsumption_resolution,[],[f1316,f427])).

fof(f427,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_45 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl1_45
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_45])])).

fof(f1316,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_12
    | ~ spl1_15
    | spl1_118 ),
    inference(subsumption_resolution,[],[f1314,f152])).

fof(f152,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl1_15
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f1314,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_12
    | spl1_118 ),
    inference(resolution,[],[f1308,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl1_12
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f1308,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | spl1_118 ),
    inference(avatar_component_clause,[],[f1306])).

fof(f1297,plain,
    ( spl1_116
    | ~ spl1_7
    | ~ spl1_23
    | ~ spl1_52
    | ~ spl1_84
    | ~ spl1_89 ),
    inference(avatar_split_clause,[],[f1113,f919,f862,f561,f212,f110,f1294])).

fof(f110,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f212,plain,
    ( spl1_23
  <=> ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f561,plain,
    ( spl1_52
  <=> k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).

fof(f862,plain,
    ( spl1_84
  <=> ! [X1,X0] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_84])])).

fof(f919,plain,
    ( spl1_89
  <=> k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_89])])).

fof(f1113,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_7
    | ~ spl1_23
    | ~ spl1_52
    | ~ spl1_84
    | ~ spl1_89 ),
    inference(backward_demodulation,[],[f921,f1085])).

fof(f1085,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_23
    | ~ spl1_52
    | ~ spl1_84 ),
    inference(forward_demodulation,[],[f1054,f1037])).

fof(f1037,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1)
    | ~ spl1_7
    | ~ spl1_23
    | ~ spl1_84 ),
    inference(forward_demodulation,[],[f1026,f111])).

fof(f111,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1026,plain,
    ( ! [X1] : k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)
    | ~ spl1_23
    | ~ spl1_84 ),
    inference(superposition,[],[f863,f213])).

fof(f213,plain,
    ( ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f863,plain,
    ( ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl1_84 ),
    inference(avatar_component_clause,[],[f862])).

fof(f1054,plain,
    ( k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0))
    | ~ spl1_7
    | ~ spl1_23
    | ~ spl1_52
    | ~ spl1_84 ),
    inference(backward_demodulation,[],[f563,f1037])).

fof(f563,plain,
    ( k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl1_52 ),
    inference(avatar_component_clause,[],[f561])).

fof(f921,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)
    | ~ spl1_89 ),
    inference(avatar_component_clause,[],[f919])).

fof(f1288,plain,(
    spl1_115 ),
    inference(avatar_split_clause,[],[f76,f1286])).

fof(f76,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f1254,plain,
    ( spl1_111
    | ~ spl1_24
    | ~ spl1_109 ),
    inference(avatar_split_clause,[],[f1206,f1199,f216,f1252])).

fof(f216,plain,
    ( spl1_24
  <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f1199,plain,
    ( spl1_109
  <=> ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_109])])).

fof(f1206,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_24
    | ~ spl1_109 ),
    inference(forward_demodulation,[],[f1202,f1200])).

fof(f1200,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1)
    | ~ spl1_109 ),
    inference(avatar_component_clause,[],[f1199])).

fof(f1202,plain,
    ( ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k6_subset_1(X1,X1))
    | ~ spl1_24
    | ~ spl1_109 ),
    inference(superposition,[],[f1200,f217])).

fof(f217,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1201,plain,
    ( spl1_109
    | ~ spl1_7
    | ~ spl1_23
    | ~ spl1_84 ),
    inference(avatar_split_clause,[],[f1037,f862,f212,f110,f1199])).

fof(f1174,plain,
    ( spl1_104
    | ~ spl1_7
    | ~ spl1_23
    | ~ spl1_52
    | ~ spl1_84 ),
    inference(avatar_split_clause,[],[f1085,f862,f561,f212,f110,f1171])).

fof(f973,plain,
    ( spl1_94
    | ~ spl1_45
    | ~ spl1_92 ),
    inference(avatar_split_clause,[],[f953,f943,f426,f970])).

fof(f943,plain,
    ( spl1_92
  <=> ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_92])])).

fof(f953,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_45
    | ~ spl1_92 ),
    inference(resolution,[],[f944,f427])).

fof(f944,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_92 ),
    inference(avatar_component_clause,[],[f943])).

fof(f966,plain,
    ( spl1_93
    | ~ spl1_1
    | ~ spl1_92 ),
    inference(avatar_split_clause,[],[f961,f943,f82,f963])).

fof(f82,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f961,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_92 ),
    inference(resolution,[],[f944,f84])).

fof(f84,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f945,plain,
    ( spl1_92
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_15
    | ~ spl1_73 ),
    inference(avatar_split_clause,[],[f940,f771,f150,f101,f96,f92,f943])).

fof(f92,plain,
    ( spl1_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f96,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f101,plain,
    ( spl1_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f771,plain,
    ( spl1_73
  <=> ! [X1,X0] :
        ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
        | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_73])])).

fof(f940,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_15
    | ~ spl1_73 ),
    inference(forward_demodulation,[],[f939,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f939,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_15
    | ~ spl1_73 ),
    inference(subsumption_resolution,[],[f938,f152])).

fof(f938,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_73 ),
    inference(subsumption_resolution,[],[f936,f93])).

fof(f93,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f936,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_73 ),
    inference(superposition,[],[f772,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f772,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_73 ),
    inference(avatar_component_clause,[],[f771])).

fof(f922,plain,
    ( spl1_89
    | ~ spl1_15
    | ~ spl1_72 ),
    inference(avatar_split_clause,[],[f894,f767,f150,f919])).

fof(f894,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)
    | ~ spl1_15
    | ~ spl1_72 ),
    inference(resolution,[],[f768,f152])).

fof(f864,plain,(
    spl1_84 ),
    inference(avatar_split_clause,[],[f78,f862])).

fof(f78,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f57,f74])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f773,plain,(
    spl1_73 ),
    inference(avatar_split_clause,[],[f55,f771])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f769,plain,
    ( spl1_72
    | ~ spl1_10
    | ~ spl1_41
    | ~ spl1_45 ),
    inference(avatar_split_clause,[],[f637,f426,f401,f125,f767])).

fof(f125,plain,
    ( spl1_10
  <=> sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f401,plain,
    ( spl1_41
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).

fof(f637,plain,
    ( ! [X11] :
        ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),sK0)
        | ~ v1_relat_1(X11) )
    | ~ spl1_10
    | ~ spl1_41
    | ~ spl1_45 ),
    inference(forward_demodulation,[],[f623,f127])).

fof(f127,plain,
    ( sK0 = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f623,plain,
    ( ! [X11] :
        ( ~ v1_relat_1(X11)
        | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),k4_relat_1(k4_relat_1(sK0))) )
    | ~ spl1_41
    | ~ spl1_45 ),
    inference(resolution,[],[f402,f427])).

fof(f402,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl1_41 ),
    inference(avatar_component_clause,[],[f401])).

fof(f564,plain,
    ( spl1_52
    | ~ spl1_1
    | ~ spl1_51 ),
    inference(avatar_split_clause,[],[f552,f533,f82,f561])).

fof(f533,plain,
    ( spl1_51
  <=> ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).

fof(f552,plain,
    ( k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_51 ),
    inference(resolution,[],[f534,f84])).

fof(f534,plain,
    ( ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) )
    | ~ spl1_51 ),
    inference(avatar_component_clause,[],[f533])).

fof(f535,plain,
    ( spl1_51
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(avatar_split_clause,[],[f506,f298,f82,f533])).

fof(f298,plain,
    ( spl1_33
  <=> ! [X1,X0] :
        ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f506,plain,
    ( ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) )
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(resolution,[],[f299,f84])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) )
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f298])).

fof(f433,plain,
    ( ~ spl1_1
    | ~ spl1_8
    | spl1_45 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_8
    | spl1_45 ),
    inference(subsumption_resolution,[],[f430,f84])).

fof(f430,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_8
    | spl1_45 ),
    inference(resolution,[],[f428,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl1_8
  <=> ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f428,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_45 ),
    inference(avatar_component_clause,[],[f426])).

fof(f403,plain,(
    spl1_41 ),
    inference(avatar_split_clause,[],[f54,f401])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f325,plain,
    ( ~ spl1_1
    | ~ spl1_12
    | ~ spl1_15
    | spl1_35 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_12
    | ~ spl1_15
    | spl1_35 ),
    inference(subsumption_resolution,[],[f323,f84])).

fof(f323,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_12
    | ~ spl1_15
    | spl1_35 ),
    inference(subsumption_resolution,[],[f321,f152])).

fof(f321,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_12
    | spl1_35 ),
    inference(resolution,[],[f315,f137])).

fof(f315,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_35 ),
    inference(avatar_component_clause,[],[f314])).

fof(f320,plain,
    ( ~ spl1_35
    | ~ spl1_8
    | spl1_34 ),
    inference(avatar_split_clause,[],[f318,f310,f114,f314])).

fof(f318,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_8
    | spl1_34 ),
    inference(resolution,[],[f312,f115])).

fof(f312,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_34 ),
    inference(avatar_component_clause,[],[f310])).

fof(f300,plain,(
    spl1_33 ),
    inference(avatar_split_clause,[],[f53,f298])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f273,plain,
    ( spl1_30
    | ~ spl1_15
    | ~ spl1_28 ),
    inference(avatar_split_clause,[],[f258,f254,f150,f270])).

fof(f254,plain,
    ( spl1_28
  <=> ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f258,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_15
    | ~ spl1_28 ),
    inference(resolution,[],[f255,f152])).

fof(f255,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_28 ),
    inference(avatar_component_clause,[],[f254])).

fof(f256,plain,
    ( spl1_28
    | ~ spl1_1
    | ~ spl1_27 ),
    inference(avatar_split_clause,[],[f252,f244,f82,f254])).

fof(f244,plain,
    ( spl1_27
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f252,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_1
    | ~ spl1_27 ),
    inference(resolution,[],[f245,f84])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f246,plain,
    ( spl1_27
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f162,f136,f118,f244])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(resolution,[],[f137,f119])).

fof(f218,plain,(
    spl1_24 ),
    inference(avatar_split_clause,[],[f79,f216])).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(definition_unfolding,[],[f64,f57,f57])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f214,plain,(
    spl1_23 ),
    inference(avatar_split_clause,[],[f77,f212])).

fof(f77,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f210,plain,(
    spl1_22 ),
    inference(avatar_split_clause,[],[f75,f208])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f171,plain,
    ( ~ spl1_16
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f42,f168,f164])).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f159,plain,
    ( ~ spl1_2
    | ~ spl1_6
    | spl1_15 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_6
    | spl1_15 ),
    inference(subsumption_resolution,[],[f157,f89])).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f157,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_6
    | spl1_15 ),
    inference(resolution,[],[f151,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f151,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f138,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f61,f136])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f128,plain,
    ( spl1_10
    | ~ spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f121,f118,f82,f125])).

fof(f121,plain,
    ( sK0 = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_9 ),
    inference(resolution,[],[f119,f84])).

fof(f120,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f51,f118])).

fof(f51,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f116,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f112,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f48,f110])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f108,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f49,f106])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f104,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f45,f101])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f99,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f90,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

% (31381)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f85,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (31366)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (31367)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (31378)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (31372)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (31377)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (31371)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (31380)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (31379)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (31383)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (31374)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (31376)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (31369)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (31375)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (31368)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (31365)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (31370)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (31373)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (31372)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1584,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f85,f90,f94,f99,f104,f108,f112,f116,f120,f128,f138,f159,f171,f210,f214,f218,f246,f256,f273,f300,f320,f325,f403,f433,f535,f564,f769,f773,f864,f922,f945,f966,f973,f1174,f1201,f1254,f1288,f1297,f1318,f1379,f1408,f1425,f1551,f1583])).
% 0.21/0.53  fof(f1583,plain,(
% 0.21/0.53    spl1_17 | ~spl1_22 | ~spl1_35 | ~spl1_93 | ~spl1_111 | ~spl1_115),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1582])).
% 0.21/0.53  fof(f1582,plain,(
% 0.21/0.53    $false | (spl1_17 | ~spl1_22 | ~spl1_35 | ~spl1_93 | ~spl1_111 | ~spl1_115)),
% 0.21/0.53    inference(subsumption_resolution,[],[f170,f1484])).
% 0.21/0.53  fof(f1484,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_22 | ~spl1_35 | ~spl1_93 | ~spl1_111 | ~spl1_115)),
% 0.21/0.53    inference(forward_demodulation,[],[f1483,f209])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ) | ~spl1_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl1_22 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.21/0.53  fof(f1483,plain,(
% 0.21/0.53    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)) | (~spl1_35 | ~spl1_93 | ~spl1_111 | ~spl1_115)),
% 0.21/0.53    inference(forward_demodulation,[],[f1482,f1253])).
% 0.21/0.53  fof(f1253,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl1_111),
% 0.21/0.53    inference(avatar_component_clause,[],[f1252])).
% 0.21/0.53  fof(f1252,plain,(
% 0.21/0.53    spl1_111 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_111])])).
% 0.21/0.53  fof(f1482,plain,(
% 0.21/0.53    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) | (~spl1_35 | ~spl1_93 | ~spl1_115)),
% 0.21/0.53    inference(forward_demodulation,[],[f1436,f965])).
% 0.21/0.53  fof(f965,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_93),
% 0.21/0.53    inference(avatar_component_clause,[],[f963])).
% 0.21/0.53  fof(f963,plain,(
% 0.21/0.53    spl1_93 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_93])])).
% 0.21/0.53  fof(f1436,plain,(
% 0.21/0.53    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) | (~spl1_35 | ~spl1_115)),
% 0.21/0.53    inference(resolution,[],[f1287,f316])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f314])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    spl1_35 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.21/0.53  fof(f1287,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) ) | ~spl1_115),
% 0.21/0.53    inference(avatar_component_clause,[],[f1286])).
% 0.21/0.53  fof(f1286,plain,(
% 0.21/0.53    spl1_115 <=> ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_115])])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    spl1_17 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.53  fof(f1551,plain,(
% 0.21/0.53    spl1_16 | ~spl1_22 | ~spl1_30 | ~spl1_34 | ~spl1_35 | ~spl1_72 | ~spl1_93 | ~spl1_104 | ~spl1_111 | ~spl1_115 | ~spl1_120 | ~spl1_121 | ~spl1_124),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1550])).
% 0.21/0.53  fof(f1550,plain,(
% 0.21/0.53    $false | (spl1_16 | ~spl1_22 | ~spl1_30 | ~spl1_34 | ~spl1_35 | ~spl1_72 | ~spl1_93 | ~spl1_104 | ~spl1_111 | ~spl1_115 | ~spl1_120 | ~spl1_121 | ~spl1_124)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1549,f166])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f164])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    spl1_16 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.53  fof(f1549,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_22 | ~spl1_30 | ~spl1_34 | ~spl1_35 | ~spl1_72 | ~spl1_93 | ~spl1_104 | ~spl1_111 | ~spl1_115 | ~spl1_120 | ~spl1_121 | ~spl1_124)),
% 0.21/0.53    inference(forward_demodulation,[],[f1548,f1173])).
% 0.21/0.53  fof(f1173,plain,(
% 0.21/0.53    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_104),
% 0.21/0.53    inference(avatar_component_clause,[],[f1171])).
% 0.21/0.53  fof(f1171,plain,(
% 0.21/0.53    spl1_104 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_104])])).
% 0.21/0.53  fof(f1548,plain,(
% 0.21/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) | (~spl1_22 | ~spl1_30 | ~spl1_34 | ~spl1_35 | ~spl1_72 | ~spl1_93 | ~spl1_104 | ~spl1_111 | ~spl1_115 | ~spl1_120 | ~spl1_121 | ~spl1_124)),
% 0.21/0.53    inference(forward_demodulation,[],[f1547,f1464])).
% 0.21/0.53  fof(f1464,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) | (~spl1_22 | ~spl1_111 | ~spl1_115 | ~spl1_120 | ~spl1_121 | ~spl1_124)),
% 0.21/0.53    inference(backward_demodulation,[],[f1424,f1445])).
% 0.21/0.53  fof(f1445,plain,(
% 0.21/0.53    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_22 | ~spl1_111 | ~spl1_115 | ~spl1_120 | ~spl1_121)),
% 0.21/0.53    inference(forward_demodulation,[],[f1444,f209])).
% 0.21/0.53  fof(f1444,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)) | (~spl1_111 | ~spl1_115 | ~spl1_120 | ~spl1_121)),
% 0.21/0.53    inference(forward_demodulation,[],[f1443,f1253])).
% 0.21/0.53  fof(f1443,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0))) | (~spl1_115 | ~spl1_120 | ~spl1_121)),
% 0.21/0.53    inference(forward_demodulation,[],[f1432,f1407])).
% 0.21/0.53  fof(f1407,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_121),
% 0.21/0.53    inference(avatar_component_clause,[],[f1405])).
% 0.21/0.53  fof(f1405,plain,(
% 0.21/0.53    spl1_121 <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_121])])).
% 0.21/0.53  fof(f1432,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))))) | (~spl1_115 | ~spl1_120)),
% 0.21/0.53    inference(resolution,[],[f1287,f1378])).
% 0.21/0.53  fof(f1378,plain,(
% 0.21/0.53    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_120),
% 0.21/0.53    inference(avatar_component_clause,[],[f1376])).
% 0.21/0.53  fof(f1376,plain,(
% 0.21/0.53    spl1_120 <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_120])])).
% 0.21/0.53  fof(f1424,plain,(
% 0.21/0.53    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_124),
% 0.21/0.53    inference(avatar_component_clause,[],[f1422])).
% 0.21/0.53  fof(f1422,plain,(
% 0.21/0.53    spl1_124 <=> k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_124])])).
% 0.21/0.53  fof(f1547,plain,(
% 0.21/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_22 | ~spl1_30 | ~spl1_34 | ~spl1_35 | ~spl1_72 | ~spl1_93 | ~spl1_104 | ~spl1_111 | ~spl1_115)),
% 0.21/0.53    inference(forward_demodulation,[],[f1503,f1173])).
% 0.21/0.53  fof(f1503,plain,(
% 0.21/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))) | (~spl1_22 | ~spl1_30 | ~spl1_34 | ~spl1_35 | ~spl1_72 | ~spl1_93 | ~spl1_111 | ~spl1_115)),
% 0.21/0.53    inference(backward_demodulation,[],[f910,f1484])).
% 0.21/0.53  fof(f910,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) | (~spl1_30 | ~spl1_34 | ~spl1_72)),
% 0.21/0.53    inference(forward_demodulation,[],[f897,f272])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f270])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    spl1_30 <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 0.21/0.53  fof(f897,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),sK0) | (~spl1_34 | ~spl1_72)),
% 0.21/0.53    inference(resolution,[],[f768,f311])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f310])).
% 0.21/0.53  fof(f310,plain,(
% 0.21/0.53    spl1_34 <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).
% 0.21/0.53  fof(f768,plain,(
% 0.21/0.53    ( ! [X11] : (~v1_relat_1(X11) | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),sK0)) ) | ~spl1_72),
% 0.21/0.53    inference(avatar_component_clause,[],[f767])).
% 0.21/0.53  fof(f767,plain,(
% 0.21/0.53    spl1_72 <=> ! [X11] : (k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),sK0) | ~v1_relat_1(X11))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_72])])).
% 0.21/0.53  fof(f1425,plain,(
% 0.21/0.53    spl1_124 | ~spl1_9 | ~spl1_116 | ~spl1_118),
% 0.21/0.53    inference(avatar_split_clause,[],[f1347,f1306,f1294,f118,f1422])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl1_9 <=> ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.53  fof(f1294,plain,(
% 0.21/0.53    spl1_116 <=> k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_116])])).
% 0.21/0.53  fof(f1306,plain,(
% 0.21/0.53    spl1_118 <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_118])])).
% 0.21/0.53  fof(f1347,plain,(
% 0.21/0.53    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_9 | ~spl1_116 | ~spl1_118)),
% 0.21/0.53    inference(forward_demodulation,[],[f1334,f1296])).
% 0.21/0.53  fof(f1296,plain,(
% 0.21/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_116),
% 0.21/0.53    inference(avatar_component_clause,[],[f1294])).
% 0.21/0.53  fof(f1334,plain,(
% 0.21/0.53    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) | (~spl1_9 | ~spl1_118)),
% 0.21/0.53    inference(resolution,[],[f1307,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) ) | ~spl1_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f1307,plain,(
% 0.21/0.53    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_118),
% 0.21/0.53    inference(avatar_component_clause,[],[f1306])).
% 0.21/0.53  fof(f1408,plain,(
% 0.21/0.53    spl1_121 | ~spl1_9 | ~spl1_94 | ~spl1_116 | ~spl1_118),
% 0.21/0.53    inference(avatar_split_clause,[],[f1351,f1306,f1294,f970,f118,f1405])).
% 0.21/0.53  fof(f970,plain,(
% 0.21/0.53    spl1_94 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_94])])).
% 0.21/0.53  fof(f1351,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_9 | ~spl1_94 | ~spl1_116 | ~spl1_118)),
% 0.21/0.53    inference(backward_demodulation,[],[f972,f1347])).
% 0.21/0.53  fof(f972,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_94),
% 0.21/0.53    inference(avatar_component_clause,[],[f970])).
% 0.21/0.53  fof(f1379,plain,(
% 0.21/0.53    spl1_120 | ~spl1_9 | ~spl1_116 | ~spl1_118),
% 0.21/0.53    inference(avatar_split_clause,[],[f1349,f1306,f1294,f118,f1376])).
% 0.21/0.53  fof(f1349,plain,(
% 0.21/0.53    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_9 | ~spl1_116 | ~spl1_118)),
% 0.21/0.53    inference(backward_demodulation,[],[f1307,f1347])).
% 0.21/0.53  fof(f1318,plain,(
% 0.21/0.53    ~spl1_12 | ~spl1_15 | ~spl1_45 | spl1_118),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1317])).
% 0.21/0.53  fof(f1317,plain,(
% 0.21/0.53    $false | (~spl1_12 | ~spl1_15 | ~spl1_45 | spl1_118)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1316,f427])).
% 0.21/0.53  fof(f427,plain,(
% 0.21/0.53    v1_relat_1(k4_relat_1(sK0)) | ~spl1_45),
% 0.21/0.53    inference(avatar_component_clause,[],[f426])).
% 0.21/0.53  fof(f426,plain,(
% 0.21/0.53    spl1_45 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_45])])).
% 0.21/0.53  fof(f1316,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_12 | ~spl1_15 | spl1_118)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1314,f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    v1_relat_1(k1_xboole_0) | ~spl1_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    spl1_15 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.53  fof(f1314,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_12 | spl1_118)),
% 0.21/0.53    inference(resolution,[],[f1308,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl1_12 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.53  fof(f1308,plain,(
% 0.21/0.53    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | spl1_118),
% 0.21/0.53    inference(avatar_component_clause,[],[f1306])).
% 0.21/0.53  fof(f1297,plain,(
% 0.21/0.53    spl1_116 | ~spl1_7 | ~spl1_23 | ~spl1_52 | ~spl1_84 | ~spl1_89),
% 0.21/0.53    inference(avatar_split_clause,[],[f1113,f919,f862,f561,f212,f110,f1294])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl1_7 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    spl1_23 <=> ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.21/0.53  fof(f561,plain,(
% 0.21/0.53    spl1_52 <=> k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).
% 0.21/0.53  fof(f862,plain,(
% 0.21/0.53    spl1_84 <=> ! [X1,X0] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_84])])).
% 0.21/0.53  fof(f919,plain,(
% 0.21/0.53    spl1_89 <=> k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_89])])).
% 0.21/0.53  fof(f1113,plain,(
% 0.21/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_7 | ~spl1_23 | ~spl1_52 | ~spl1_84 | ~spl1_89)),
% 0.21/0.53    inference(backward_demodulation,[],[f921,f1085])).
% 0.21/0.53  fof(f1085,plain,(
% 0.21/0.53    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_7 | ~spl1_23 | ~spl1_52 | ~spl1_84)),
% 0.21/0.53    inference(forward_demodulation,[],[f1054,f1037])).
% 0.21/0.53  fof(f1037,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) ) | (~spl1_7 | ~spl1_23 | ~spl1_84)),
% 0.21/0.53    inference(forward_demodulation,[],[f1026,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl1_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f1026,plain,(
% 0.21/0.53    ( ! [X1] : (k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)) ) | (~spl1_23 | ~spl1_84)),
% 0.21/0.53    inference(superposition,[],[f863,f213])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) ) | ~spl1_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f212])).
% 0.21/0.53  fof(f863,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl1_84),
% 0.21/0.53    inference(avatar_component_clause,[],[f862])).
% 0.21/0.53  fof(f1054,plain,(
% 0.21/0.53    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0)) | (~spl1_7 | ~spl1_23 | ~spl1_52 | ~spl1_84)),
% 0.21/0.53    inference(backward_demodulation,[],[f563,f1037])).
% 0.21/0.53  fof(f563,plain,(
% 0.21/0.53    k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) | ~spl1_52),
% 0.21/0.53    inference(avatar_component_clause,[],[f561])).
% 0.21/0.53  fof(f921,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) | ~spl1_89),
% 0.21/0.53    inference(avatar_component_clause,[],[f919])).
% 0.21/0.53  fof(f1288,plain,(
% 0.21/0.53    spl1_115),
% 0.21/0.53    inference(avatar_split_clause,[],[f76,f1286])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f52,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f58,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f59,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f62,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f65,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f66,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f67,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.53  fof(f1254,plain,(
% 0.21/0.53    spl1_111 | ~spl1_24 | ~spl1_109),
% 0.21/0.53    inference(avatar_split_clause,[],[f1206,f1199,f216,f1252])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    spl1_24 <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 0.21/0.53  fof(f1199,plain,(
% 0.21/0.53    spl1_109 <=> ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_109])])).
% 0.21/0.53  fof(f1206,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | (~spl1_24 | ~spl1_109)),
% 0.21/0.53    inference(forward_demodulation,[],[f1202,f1200])).
% 0.21/0.53  fof(f1200,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) ) | ~spl1_109),
% 0.21/0.53    inference(avatar_component_clause,[],[f1199])).
% 0.21/0.53  fof(f1202,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k6_subset_1(X1,X1))) ) | (~spl1_24 | ~spl1_109)),
% 0.21/0.53    inference(superposition,[],[f1200,f217])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ) | ~spl1_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f216])).
% 0.21/0.53  fof(f1201,plain,(
% 0.21/0.53    spl1_109 | ~spl1_7 | ~spl1_23 | ~spl1_84),
% 0.21/0.53    inference(avatar_split_clause,[],[f1037,f862,f212,f110,f1199])).
% 0.21/0.53  fof(f1174,plain,(
% 0.21/0.53    spl1_104 | ~spl1_7 | ~spl1_23 | ~spl1_52 | ~spl1_84),
% 0.21/0.53    inference(avatar_split_clause,[],[f1085,f862,f561,f212,f110,f1171])).
% 0.21/0.53  fof(f973,plain,(
% 0.21/0.53    spl1_94 | ~spl1_45 | ~spl1_92),
% 0.21/0.53    inference(avatar_split_clause,[],[f953,f943,f426,f970])).
% 0.21/0.53  fof(f943,plain,(
% 0.21/0.53    spl1_92 <=> ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_92])])).
% 0.21/0.53  fof(f953,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_45 | ~spl1_92)),
% 0.21/0.53    inference(resolution,[],[f944,f427])).
% 0.21/0.53  fof(f944,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_92),
% 0.21/0.53    inference(avatar_component_clause,[],[f943])).
% 0.21/0.53  fof(f966,plain,(
% 0.21/0.53    spl1_93 | ~spl1_1 | ~spl1_92),
% 0.21/0.53    inference(avatar_split_clause,[],[f961,f943,f82,f963])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.53  fof(f961,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_92)),
% 0.21/0.53    inference(resolution,[],[f944,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f945,plain,(
% 0.21/0.53    spl1_92 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_15 | ~spl1_73),
% 0.21/0.53    inference(avatar_split_clause,[],[f940,f771,f150,f101,f96,f92,f943])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl1_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl1_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.53  fof(f771,plain,(
% 0.21/0.53    spl1_73 <=> ! [X1,X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_73])])).
% 0.21/0.53  fof(f940,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_15 | ~spl1_73)),
% 0.21/0.53    inference(forward_demodulation,[],[f939,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f939,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_15 | ~spl1_73)),
% 0.21/0.53    inference(subsumption_resolution,[],[f938,f152])).
% 0.21/0.53  fof(f938,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_73)),
% 0.21/0.53    inference(subsumption_resolution,[],[f936,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f936,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_73)),
% 0.21/0.53    inference(superposition,[],[f772,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f772,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_73),
% 0.21/0.53    inference(avatar_component_clause,[],[f771])).
% 0.21/0.53  fof(f922,plain,(
% 0.21/0.53    spl1_89 | ~spl1_15 | ~spl1_72),
% 0.21/0.53    inference(avatar_split_clause,[],[f894,f767,f150,f919])).
% 0.21/0.53  fof(f894,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) | (~spl1_15 | ~spl1_72)),
% 0.21/0.53    inference(resolution,[],[f768,f152])).
% 0.21/0.53  fof(f864,plain,(
% 0.21/0.53    spl1_84),
% 0.21/0.53    inference(avatar_split_clause,[],[f78,f862])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f60,f57,f74])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f773,plain,(
% 0.21/0.53    spl1_73),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f771])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.53  fof(f769,plain,(
% 0.21/0.53    spl1_72 | ~spl1_10 | ~spl1_41 | ~spl1_45),
% 0.21/0.53    inference(avatar_split_clause,[],[f637,f426,f401,f125,f767])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl1_10 <=> sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.53  fof(f401,plain,(
% 0.21/0.53    spl1_41 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).
% 0.21/0.53  fof(f637,plain,(
% 0.21/0.53    ( ! [X11] : (k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),sK0) | ~v1_relat_1(X11)) ) | (~spl1_10 | ~spl1_41 | ~spl1_45)),
% 0.21/0.53    inference(forward_demodulation,[],[f623,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    sK0 = k4_relat_1(k4_relat_1(sK0)) | ~spl1_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f623,plain,(
% 0.21/0.53    ( ! [X11] : (~v1_relat_1(X11) | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X11)) = k5_relat_1(k4_relat_1(X11),k4_relat_1(k4_relat_1(sK0)))) ) | (~spl1_41 | ~spl1_45)),
% 0.21/0.53    inference(resolution,[],[f402,f427])).
% 0.21/0.53  fof(f402,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl1_41),
% 0.21/0.53    inference(avatar_component_clause,[],[f401])).
% 0.21/0.53  fof(f564,plain,(
% 0.21/0.53    spl1_52 | ~spl1_1 | ~spl1_51),
% 0.21/0.53    inference(avatar_split_clause,[],[f552,f533,f82,f561])).
% 0.21/0.53  fof(f533,plain,(
% 0.21/0.53    spl1_51 <=> ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).
% 0.21/0.53  fof(f552,plain,(
% 0.21/0.53    k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) | (~spl1_1 | ~spl1_51)),
% 0.21/0.53    inference(resolution,[],[f534,f84])).
% 0.21/0.53  fof(f534,plain,(
% 0.21/0.53    ( ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18))) ) | ~spl1_51),
% 0.21/0.53    inference(avatar_component_clause,[],[f533])).
% 0.21/0.53  fof(f535,plain,(
% 0.21/0.53    spl1_51 | ~spl1_1 | ~spl1_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f506,f298,f82,f533])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    spl1_33 <=> ! [X1,X0] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.21/0.53  fof(f506,plain,(
% 0.21/0.53    ( ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18))) ) | (~spl1_1 | ~spl1_33)),
% 0.21/0.53    inference(resolution,[],[f299,f84])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))) ) | ~spl1_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f298])).
% 0.21/0.53  fof(f433,plain,(
% 0.21/0.53    ~spl1_1 | ~spl1_8 | spl1_45),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f432])).
% 0.21/0.53  fof(f432,plain,(
% 0.21/0.53    $false | (~spl1_1 | ~spl1_8 | spl1_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f430,f84])).
% 0.21/0.53  fof(f430,plain,(
% 0.21/0.53    ~v1_relat_1(sK0) | (~spl1_8 | spl1_45)),
% 0.21/0.53    inference(resolution,[],[f428,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl1_8 <=> ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.53  fof(f428,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(sK0)) | spl1_45),
% 0.21/0.53    inference(avatar_component_clause,[],[f426])).
% 0.21/0.53  fof(f403,plain,(
% 0.21/0.53    spl1_41),
% 0.21/0.53    inference(avatar_split_clause,[],[f54,f401])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    ~spl1_1 | ~spl1_12 | ~spl1_15 | spl1_35),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f324])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    $false | (~spl1_1 | ~spl1_12 | ~spl1_15 | spl1_35)),
% 0.21/0.53    inference(subsumption_resolution,[],[f323,f84])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    ~v1_relat_1(sK0) | (~spl1_12 | ~spl1_15 | spl1_35)),
% 0.21/0.53    inference(subsumption_resolution,[],[f321,f152])).
% 0.21/0.53  fof(f321,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | (~spl1_12 | spl1_35)),
% 0.21/0.53    inference(resolution,[],[f315,f137])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f314])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    ~spl1_35 | ~spl1_8 | spl1_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f318,f310,f114,f314])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_8 | spl1_34)),
% 0.21/0.53    inference(resolution,[],[f312,f115])).
% 0.21/0.53  fof(f312,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | spl1_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f310])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    spl1_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f298])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    spl1_30 | ~spl1_15 | ~spl1_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f258,f254,f150,f270])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    spl1_28 <=> ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_15 | ~spl1_28)),
% 0.21/0.53    inference(resolution,[],[f255,f152])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | ~spl1_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f254])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    spl1_28 | ~spl1_1 | ~spl1_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f252,f244,f82,f254])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    spl1_27 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | (~spl1_1 | ~spl1_27)),
% 0.21/0.53    inference(resolution,[],[f245,f84])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | ~spl1_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f244])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    spl1_27 | ~spl1_9 | ~spl1_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f162,f136,f118,f244])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | (~spl1_9 | ~spl1_12)),
% 0.21/0.53    inference(resolution,[],[f137,f119])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    spl1_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f216])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f64,f57,f57])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    spl1_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f77,f212])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f56,f74])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    spl1_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f75,f208])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f74])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ~spl1_16 | ~spl1_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f168,f164])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f25])).
% 0.21/0.53  fof(f25,conjecture,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    ~spl1_2 | ~spl1_6 | spl1_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    $false | (~spl1_2 | ~spl1_6 | spl1_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | (~spl1_6 | spl1_15)),
% 0.21/0.53    inference(resolution,[],[f151,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | spl1_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f150])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl1_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f61,f136])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl1_10 | ~spl1_1 | ~spl1_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f121,f118,f82,f125])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    sK0 = k4_relat_1(k4_relat_1(sK0)) | (~spl1_1 | ~spl1_9)),
% 0.21/0.53    inference(resolution,[],[f119,f84])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl1_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f118])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl1_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f114])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl1_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f110])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl1_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f106])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl1_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f101])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,axiom,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl1_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f96])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl1_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f92])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl1_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f87])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  % (31381)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl1_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f82])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v1_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (31372)------------------------------
% 0.21/0.53  % (31372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31372)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (31372)Memory used [KB]: 7291
% 0.21/0.53  % (31372)Time elapsed: 0.054 s
% 0.21/0.53  % (31372)------------------------------
% 0.21/0.53  % (31372)------------------------------
% 0.21/0.53  % (31364)Success in time 0.167 s
%------------------------------------------------------------------------------
