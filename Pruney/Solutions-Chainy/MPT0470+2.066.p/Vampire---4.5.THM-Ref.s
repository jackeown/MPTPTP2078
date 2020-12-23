%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  271 ( 589 expanded)
%              Number of leaves         :   70 ( 256 expanded)
%              Depth                    :   12
%              Number of atoms          :  784 (1508 expanded)
%              Number of equality atoms :  172 ( 425 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1489,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f95,f100,f105,f109,f113,f117,f121,f126,f131,f138,f143,f148,f158,f182,f194,f202,f261,f265,f275,f285,f296,f339,f344,f373,f453,f507,f533,f731,f765,f827,f877,f904,f964,f985,f992,f1179,f1227,f1260,f1271,f1313,f1456,f1488])).

fof(f1488,plain,
    ( ~ spl1_16
    | spl1_21
    | ~ spl1_23
    | ~ spl1_39
    | ~ spl1_95
    | ~ spl1_114 ),
    inference(avatar_contradiction_clause,[],[f1487])).

fof(f1487,plain,
    ( $false
    | ~ spl1_16
    | spl1_21
    | ~ spl1_23
    | ~ spl1_39
    | ~ spl1_95
    | ~ spl1_114 ),
    inference(subsumption_resolution,[],[f193,f1389])).

fof(f1389,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_39
    | ~ spl1_95
    | ~ spl1_114 ),
    inference(forward_demodulation,[],[f1388,f201])).

fof(f201,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl1_23
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f1388,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0))
    | ~ spl1_16
    | ~ spl1_39
    | ~ spl1_95
    | ~ spl1_114 ),
    inference(forward_demodulation,[],[f1387,f157])).

fof(f157,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl1_16
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f1387,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)))
    | ~ spl1_39
    | ~ spl1_95
    | ~ spl1_114 ),
    inference(forward_demodulation,[],[f1341,f984])).

fof(f984,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_95 ),
    inference(avatar_component_clause,[],[f982])).

fof(f982,plain,
    ( spl1_95
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_95])])).

fof(f1341,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
    | ~ spl1_39
    | ~ spl1_114 ),
    inference(resolution,[],[f1270,f335])).

fof(f335,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_39 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl1_39
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_39])])).

fof(f1270,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 )
    | ~ spl1_114 ),
    inference(avatar_component_clause,[],[f1269])).

fof(f1269,plain,
    ( spl1_114
  <=> ! [X0] :
        ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_114])])).

fof(f193,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl1_21
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f1456,plain,
    ( ~ spl1_16
    | spl1_20
    | ~ spl1_23
    | ~ spl1_35
    | ~ spl1_38
    | ~ spl1_39
    | ~ spl1_72
    | ~ spl1_95
    | ~ spl1_104
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114
    | ~ spl1_121 ),
    inference(avatar_contradiction_clause,[],[f1455])).

fof(f1455,plain,
    ( $false
    | ~ spl1_16
    | spl1_20
    | ~ spl1_23
    | ~ spl1_35
    | ~ spl1_38
    | ~ spl1_39
    | ~ spl1_72
    | ~ spl1_95
    | ~ spl1_104
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114
    | ~ spl1_121 ),
    inference(subsumption_resolution,[],[f1454,f189])).

fof(f189,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_20 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl1_20
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f1454,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_35
    | ~ spl1_38
    | ~ spl1_39
    | ~ spl1_72
    | ~ spl1_95
    | ~ spl1_104
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114
    | ~ spl1_121 ),
    inference(forward_demodulation,[],[f1453,f1178])).

fof(f1178,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_104 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f1176,plain,
    ( spl1_104
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_104])])).

fof(f1453,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_35
    | ~ spl1_38
    | ~ spl1_39
    | ~ spl1_72
    | ~ spl1_95
    | ~ spl1_104
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114
    | ~ spl1_121 ),
    inference(forward_demodulation,[],[f1452,f1366])).

fof(f1366,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114
    | ~ spl1_121 ),
    inference(backward_demodulation,[],[f1312,f1348])).

fof(f1348,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114 ),
    inference(forward_demodulation,[],[f1347,f201])).

fof(f1347,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0))
    | ~ spl1_16
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114 ),
    inference(forward_demodulation,[],[f1346,f157])).

fof(f1346,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0)))
    | ~ spl1_110
    | ~ spl1_112
    | ~ spl1_114 ),
    inference(forward_demodulation,[],[f1336,f1259])).

fof(f1259,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_112 ),
    inference(avatar_component_clause,[],[f1257])).

fof(f1257,plain,
    ( spl1_112
  <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_112])])).

fof(f1336,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))))
    | ~ spl1_110
    | ~ spl1_114 ),
    inference(resolution,[],[f1270,f1226])).

fof(f1226,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_110 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f1224,plain,
    ( spl1_110
  <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_110])])).

fof(f1312,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_121 ),
    inference(avatar_component_clause,[],[f1310])).

fof(f1310,plain,
    ( spl1_121
  <=> k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_121])])).

fof(f1452,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_35
    | ~ spl1_38
    | ~ spl1_39
    | ~ spl1_72
    | ~ spl1_95
    | ~ spl1_104
    | ~ spl1_114 ),
    inference(forward_demodulation,[],[f1408,f1178])).

fof(f1408,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)))
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_35
    | ~ spl1_38
    | ~ spl1_39
    | ~ spl1_72
    | ~ spl1_95
    | ~ spl1_114 ),
    inference(backward_demodulation,[],[f867,f1389])).

fof(f867,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0)
    | ~ spl1_35
    | ~ spl1_38
    | ~ spl1_72 ),
    inference(forward_demodulation,[],[f856,f295])).

fof(f295,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_35 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl1_35
  <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f856,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),sK0)
    | ~ spl1_38
    | ~ spl1_72 ),
    inference(resolution,[],[f730,f330])).

fof(f330,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_38 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl1_38
  <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).

fof(f730,plain,
    ( ! [X10] :
        ( ~ v1_relat_1(X10)
        | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),sK0) )
    | ~ spl1_72 ),
    inference(avatar_component_clause,[],[f729])).

fof(f729,plain,
    ( spl1_72
  <=> ! [X10] :
        ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),sK0)
        | ~ v1_relat_1(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_72])])).

fof(f1313,plain,
    ( spl1_121
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85
    | ~ spl1_89
    | ~ spl1_92 ),
    inference(avatar_split_clause,[],[f1086,f892,f874,f825,f530,f259,f129,f111,f1310])).

fof(f111,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f129,plain,
    ( spl1_11
  <=> ! [X0] :
        ( k4_relat_1(k4_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f259,plain,
    ( spl1_30
  <=> ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f530,plain,
    ( spl1_52
  <=> k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).

fof(f825,plain,
    ( spl1_85
  <=> ! [X1,X0] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_85])])).

fof(f874,plain,
    ( spl1_89
  <=> k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_89])])).

fof(f892,plain,
    ( spl1_92
  <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_92])])).

fof(f1086,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85
    | ~ spl1_89
    | ~ spl1_92 ),
    inference(backward_demodulation,[],[f923,f1054])).

fof(f1054,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85 ),
    inference(forward_demodulation,[],[f1048,f1047])).

fof(f1047,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1)
    | ~ spl1_7
    | ~ spl1_30
    | ~ spl1_85 ),
    inference(forward_demodulation,[],[f1036,f112])).

fof(f112,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f1036,plain,
    ( ! [X1] : k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)
    | ~ spl1_30
    | ~ spl1_85 ),
    inference(superposition,[],[f826,f260])).

fof(f260,plain,
    ( ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0
    | ~ spl1_30 ),
    inference(avatar_component_clause,[],[f259])).

fof(f826,plain,
    ( ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl1_85 ),
    inference(avatar_component_clause,[],[f825])).

fof(f1048,plain,
    ( k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0))
    | ~ spl1_7
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85 ),
    inference(backward_demodulation,[],[f532,f1047])).

fof(f532,plain,
    ( k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl1_52 ),
    inference(avatar_component_clause,[],[f530])).

fof(f923,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl1_11
    | ~ spl1_89
    | ~ spl1_92 ),
    inference(forward_demodulation,[],[f911,f876])).

fof(f876,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)
    | ~ spl1_89 ),
    inference(avatar_component_clause,[],[f874])).

fof(f911,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))
    | ~ spl1_11
    | ~ spl1_92 ),
    inference(resolution,[],[f893,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k4_relat_1(X0)) = X0 )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f893,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_92 ),
    inference(avatar_component_clause,[],[f892])).

fof(f1271,plain,(
    spl1_114 ),
    inference(avatar_split_clause,[],[f79,f1269])).

fof(f79,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f1260,plain,
    ( spl1_112
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85
    | ~ spl1_89
    | ~ spl1_92
    | ~ spl1_96 ),
    inference(avatar_split_clause,[],[f1134,f989,f892,f874,f825,f530,f259,f129,f111,f1257])).

fof(f989,plain,
    ( spl1_96
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_96])])).

fof(f1134,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85
    | ~ spl1_89
    | ~ spl1_92
    | ~ spl1_96 ),
    inference(backward_demodulation,[],[f991,f1086])).

fof(f991,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_96 ),
    inference(avatar_component_clause,[],[f989])).

fof(f1227,plain,
    ( spl1_110
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85
    | ~ spl1_89
    | ~ spl1_92 ),
    inference(avatar_split_clause,[],[f1130,f892,f874,f825,f530,f259,f129,f111,f1224])).

fof(f1130,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85
    | ~ spl1_89
    | ~ spl1_92 ),
    inference(backward_demodulation,[],[f893,f1086])).

fof(f1179,plain,
    ( spl1_104
    | ~ spl1_7
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_85 ),
    inference(avatar_split_clause,[],[f1054,f825,f530,f259,f111,f1176])).

fof(f992,plain,
    ( spl1_96
    | ~ spl1_49
    | ~ spl1_94 ),
    inference(avatar_split_clause,[],[f971,f962,f446,f989])).

fof(f446,plain,
    ( spl1_49
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_49])])).

fof(f962,plain,
    ( spl1_94
  <=> ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_94])])).

fof(f971,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_49
    | ~ spl1_94 ),
    inference(resolution,[],[f963,f447])).

fof(f447,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_49 ),
    inference(avatar_component_clause,[],[f446])).

fof(f963,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_94 ),
    inference(avatar_component_clause,[],[f962])).

fof(f985,plain,
    ( spl1_95
    | ~ spl1_1
    | ~ spl1_94 ),
    inference(avatar_split_clause,[],[f980,f962,f83,f982])).

fof(f83,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f980,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_94 ),
    inference(resolution,[],[f963,f85])).

fof(f85,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f964,plain,
    ( spl1_94
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_19
    | ~ spl1_74 ),
    inference(avatar_split_clause,[],[f909,f763,f173,f102,f97,f93,f962])).

fof(f93,plain,
    ( spl1_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f97,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f102,plain,
    ( spl1_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f173,plain,
    ( spl1_19
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f763,plain,
    ( spl1_74
  <=> ! [X1,X0] :
        ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
        | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_74])])).

fof(f909,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_19
    | ~ spl1_74 ),
    inference(forward_demodulation,[],[f908,f104])).

fof(f104,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f908,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_19
    | ~ spl1_74 ),
    inference(subsumption_resolution,[],[f907,f175])).

fof(f175,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f907,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_74 ),
    inference(subsumption_resolution,[],[f905,f94])).

fof(f94,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f905,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_74 ),
    inference(superposition,[],[f764,f99])).

fof(f99,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f764,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_74 ),
    inference(avatar_component_clause,[],[f763])).

fof(f904,plain,
    ( ~ spl1_12
    | ~ spl1_19
    | ~ spl1_49
    | spl1_92 ),
    inference(avatar_contradiction_clause,[],[f903])).

fof(f903,plain,
    ( $false
    | ~ spl1_12
    | ~ spl1_19
    | ~ spl1_49
    | spl1_92 ),
    inference(subsumption_resolution,[],[f902,f447])).

fof(f902,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_12
    | ~ spl1_19
    | spl1_92 ),
    inference(subsumption_resolution,[],[f900,f175])).

fof(f900,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_12
    | spl1_92 ),
    inference(resolution,[],[f894,f137])).

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

fof(f894,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | spl1_92 ),
    inference(avatar_component_clause,[],[f892])).

fof(f877,plain,
    ( spl1_89
    | ~ spl1_19
    | ~ spl1_72 ),
    inference(avatar_split_clause,[],[f852,f729,f173,f874])).

fof(f852,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)
    | ~ spl1_19
    | ~ spl1_72 ),
    inference(resolution,[],[f730,f175])).

fof(f827,plain,(
    spl1_85 ),
    inference(avatar_split_clause,[],[f81,f825])).

fof(f81,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f61,f77])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f765,plain,(
    spl1_74 ),
    inference(avatar_split_clause,[],[f59,f763])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f731,plain,
    ( spl1_72
    | ~ spl1_13
    | ~ spl1_42
    | ~ spl1_49 ),
    inference(avatar_split_clause,[],[f607,f446,f371,f140,f729])).

fof(f140,plain,
    ( spl1_13
  <=> sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f371,plain,
    ( spl1_42
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).

fof(f607,plain,
    ( ! [X10] :
        ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),sK0)
        | ~ v1_relat_1(X10) )
    | ~ spl1_13
    | ~ spl1_42
    | ~ spl1_49 ),
    inference(forward_demodulation,[],[f595,f142])).

fof(f142,plain,
    ( sK0 = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f595,plain,
    ( ! [X10] :
        ( ~ v1_relat_1(X10)
        | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),k4_relat_1(k4_relat_1(sK0))) )
    | ~ spl1_42
    | ~ spl1_49 ),
    inference(resolution,[],[f372,f447])).

fof(f372,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl1_42 ),
    inference(avatar_component_clause,[],[f371])).

fof(f533,plain,
    ( spl1_52
    | ~ spl1_1
    | ~ spl1_51 ),
    inference(avatar_split_clause,[],[f522,f505,f83,f530])).

fof(f505,plain,
    ( spl1_51
  <=> ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).

fof(f522,plain,
    ( k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_51 ),
    inference(resolution,[],[f506,f85])).

fof(f506,plain,
    ( ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) )
    | ~ spl1_51 ),
    inference(avatar_component_clause,[],[f505])).

fof(f507,plain,
    ( spl1_51
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(avatar_split_clause,[],[f497,f283,f83,f505])).

fof(f283,plain,
    ( spl1_33
  <=> ! [X1,X0] :
        ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f497,plain,
    ( ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) )
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(resolution,[],[f284,f85])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) )
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f283])).

fof(f453,plain,
    ( ~ spl1_1
    | ~ spl1_9
    | spl1_49 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_9
    | spl1_49 ),
    inference(subsumption_resolution,[],[f450,f85])).

fof(f450,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_9
    | spl1_49 ),
    inference(resolution,[],[f448,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl1_9
  <=> ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f448,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_49 ),
    inference(avatar_component_clause,[],[f446])).

fof(f373,plain,(
    spl1_42 ),
    inference(avatar_split_clause,[],[f58,f371])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f344,plain,
    ( ~ spl1_1
    | ~ spl1_12
    | ~ spl1_19
    | spl1_39 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_12
    | ~ spl1_19
    | spl1_39 ),
    inference(subsumption_resolution,[],[f342,f85])).

fof(f342,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_12
    | ~ spl1_19
    | spl1_39 ),
    inference(subsumption_resolution,[],[f340,f175])).

fof(f340,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_12
    | spl1_39 ),
    inference(resolution,[],[f334,f137])).

fof(f334,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_39 ),
    inference(avatar_component_clause,[],[f333])).

fof(f339,plain,
    ( ~ spl1_39
    | ~ spl1_9
    | spl1_38 ),
    inference(avatar_split_clause,[],[f337,f329,f119,f333])).

fof(f337,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_9
    | spl1_38 ),
    inference(resolution,[],[f331,f120])).

fof(f331,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_38 ),
    inference(avatar_component_clause,[],[f329])).

fof(f296,plain,
    ( spl1_35
    | ~ spl1_19
    | ~ spl1_32 ),
    inference(avatar_split_clause,[],[f277,f273,f173,f293])).

fof(f273,plain,
    ( spl1_32
  <=> ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).

fof(f277,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_19
    | ~ spl1_32 ),
    inference(resolution,[],[f274,f175])).

fof(f274,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_32 ),
    inference(avatar_component_clause,[],[f273])).

fof(f285,plain,(
    spl1_33 ),
    inference(avatar_split_clause,[],[f57,f283])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f275,plain,
    ( spl1_32
    | ~ spl1_1
    | ~ spl1_31 ),
    inference(avatar_split_clause,[],[f271,f263,f83,f273])).

fof(f263,plain,
    ( spl1_31
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f271,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_1
    | ~ spl1_31 ),
    inference(resolution,[],[f264,f85])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_31 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( spl1_31
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f185,f136,f129,f263])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(resolution,[],[f137,f130])).

fof(f261,plain,(
    spl1_30 ),
    inference(avatar_split_clause,[],[f80,f259])).

fof(f80,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f202,plain,(
    spl1_23 ),
    inference(avatar_split_clause,[],[f78,f200])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f50,f77])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f194,plain,
    ( ~ spl1_20
    | ~ spl1_21 ),
    inference(avatar_split_clause,[],[f45,f191,f187])).

fof(f45,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f182,plain,
    ( ~ spl1_2
    | ~ spl1_6
    | spl1_19 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_6
    | spl1_19 ),
    inference(subsumption_resolution,[],[f180,f90])).

fof(f90,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f180,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_6
    | spl1_19 ),
    inference(resolution,[],[f174,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f174,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f158,plain,
    ( spl1_16
    | ~ spl1_2
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f153,f146,f88,f156])).

fof(f146,plain,
    ( spl1_14
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f153,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_14 ),
    inference(resolution,[],[f147,f90])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_zfmisc_1(X1,X0) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( spl1_14
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f127,f124,f115,f146])).

fof(f115,plain,
    ( spl1_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f124,plain,
    ( spl1_10
  <=> ! [X1,X0] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_zfmisc_1(X1,X0) )
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(resolution,[],[f125,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f143,plain,
    ( spl1_13
    | ~ spl1_1
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f132,f129,f83,f140])).

fof(f132,plain,
    ( sK0 = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_11 ),
    inference(resolution,[],[f130,f85])).

fof(f138,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f66,f136])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f131,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f55,f129])).

fof(f55,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f126,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f65,f124])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f121,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f117,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f53,f115])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f113,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f109,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f52,f107])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f105,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f100,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f91,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f86,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (11935)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (11920)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (11919)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (11926)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (11925)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (11928)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (11921)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (11923)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (11932)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (11931)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (11924)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (11927)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (11929)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (11937)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (11922)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (11933)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (11930)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (11926)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f1489,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f86,f91,f95,f100,f105,f109,f113,f117,f121,f126,f131,f138,f143,f148,f158,f182,f194,f202,f261,f265,f275,f285,f296,f339,f344,f373,f453,f507,f533,f731,f765,f827,f877,f904,f964,f985,f992,f1179,f1227,f1260,f1271,f1313,f1456,f1488])).
% 0.22/0.51  fof(f1488,plain,(
% 0.22/0.51    ~spl1_16 | spl1_21 | ~spl1_23 | ~spl1_39 | ~spl1_95 | ~spl1_114),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f1487])).
% 0.22/0.51  fof(f1487,plain,(
% 0.22/0.51    $false | (~spl1_16 | spl1_21 | ~spl1_23 | ~spl1_39 | ~spl1_95 | ~spl1_114)),
% 0.22/0.51    inference(subsumption_resolution,[],[f193,f1389])).
% 0.22/0.51  fof(f1389,plain,(
% 0.22/0.51    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_16 | ~spl1_23 | ~spl1_39 | ~spl1_95 | ~spl1_114)),
% 0.22/0.51    inference(forward_demodulation,[],[f1388,f201])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ) | ~spl1_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f200])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    spl1_23 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.22/0.51  fof(f1388,plain,(
% 0.22/0.51    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)) | (~spl1_16 | ~spl1_39 | ~spl1_95 | ~spl1_114)),
% 0.22/0.51    inference(forward_demodulation,[],[f1387,f157])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl1_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f156])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    spl1_16 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.22/0.51  fof(f1387,plain,(
% 0.22/0.51    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) | (~spl1_39 | ~spl1_95 | ~spl1_114)),
% 0.22/0.51    inference(forward_demodulation,[],[f1341,f984])).
% 0.22/0.51  fof(f984,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_95),
% 0.22/0.51    inference(avatar_component_clause,[],[f982])).
% 0.22/0.51  fof(f982,plain,(
% 0.22/0.51    spl1_95 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_95])])).
% 0.22/0.51  fof(f1341,plain,(
% 0.22/0.51    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) | (~spl1_39 | ~spl1_114)),
% 0.22/0.51    inference(resolution,[],[f1270,f335])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_39),
% 0.22/0.51    inference(avatar_component_clause,[],[f333])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    spl1_39 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_39])])).
% 0.22/0.51  fof(f1270,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) ) | ~spl1_114),
% 0.22/0.51    inference(avatar_component_clause,[],[f1269])).
% 0.22/0.51  fof(f1269,plain,(
% 0.22/0.51    spl1_114 <=> ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_114])])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    spl1_21 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.22/0.51  fof(f1456,plain,(
% 0.22/0.51    ~spl1_16 | spl1_20 | ~spl1_23 | ~spl1_35 | ~spl1_38 | ~spl1_39 | ~spl1_72 | ~spl1_95 | ~spl1_104 | ~spl1_110 | ~spl1_112 | ~spl1_114 | ~spl1_121),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f1455])).
% 0.22/0.51  fof(f1455,plain,(
% 0.22/0.51    $false | (~spl1_16 | spl1_20 | ~spl1_23 | ~spl1_35 | ~spl1_38 | ~spl1_39 | ~spl1_72 | ~spl1_95 | ~spl1_104 | ~spl1_110 | ~spl1_112 | ~spl1_114 | ~spl1_121)),
% 0.22/0.51    inference(subsumption_resolution,[],[f1454,f189])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f187])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    spl1_20 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.22/0.51  fof(f1454,plain,(
% 0.22/0.51    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_16 | ~spl1_23 | ~spl1_35 | ~spl1_38 | ~spl1_39 | ~spl1_72 | ~spl1_95 | ~spl1_104 | ~spl1_110 | ~spl1_112 | ~spl1_114 | ~spl1_121)),
% 0.22/0.51    inference(forward_demodulation,[],[f1453,f1178])).
% 0.22/0.51  fof(f1178,plain,(
% 0.22/0.51    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_104),
% 0.22/0.51    inference(avatar_component_clause,[],[f1176])).
% 0.22/0.51  fof(f1176,plain,(
% 0.22/0.51    spl1_104 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_104])])).
% 0.22/0.51  fof(f1453,plain,(
% 0.22/0.51    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) | (~spl1_16 | ~spl1_23 | ~spl1_35 | ~spl1_38 | ~spl1_39 | ~spl1_72 | ~spl1_95 | ~spl1_104 | ~spl1_110 | ~spl1_112 | ~spl1_114 | ~spl1_121)),
% 0.22/0.51    inference(forward_demodulation,[],[f1452,f1366])).
% 0.22/0.51  fof(f1366,plain,(
% 0.22/0.51    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) | (~spl1_16 | ~spl1_23 | ~spl1_110 | ~spl1_112 | ~spl1_114 | ~spl1_121)),
% 0.22/0.51    inference(backward_demodulation,[],[f1312,f1348])).
% 0.22/0.51  fof(f1348,plain,(
% 0.22/0.51    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_16 | ~spl1_23 | ~spl1_110 | ~spl1_112 | ~spl1_114)),
% 0.22/0.51    inference(forward_demodulation,[],[f1347,f201])).
% 0.22/0.51  fof(f1347,plain,(
% 0.22/0.51    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)) | (~spl1_16 | ~spl1_110 | ~spl1_112 | ~spl1_114)),
% 0.22/0.51    inference(forward_demodulation,[],[f1346,f157])).
% 0.22/0.51  fof(f1346,plain,(
% 0.22/0.51    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0))) | (~spl1_110 | ~spl1_112 | ~spl1_114)),
% 0.22/0.51    inference(forward_demodulation,[],[f1336,f1259])).
% 0.22/0.51  fof(f1259,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_112),
% 0.22/0.51    inference(avatar_component_clause,[],[f1257])).
% 0.22/0.51  fof(f1257,plain,(
% 0.22/0.51    spl1_112 <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_112])])).
% 0.22/0.51  fof(f1336,plain,(
% 0.22/0.51    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))))) | (~spl1_110 | ~spl1_114)),
% 0.22/0.51    inference(resolution,[],[f1270,f1226])).
% 0.22/0.51  fof(f1226,plain,(
% 0.22/0.51    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_110),
% 0.22/0.51    inference(avatar_component_clause,[],[f1224])).
% 0.22/0.51  fof(f1224,plain,(
% 0.22/0.51    spl1_110 <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_110])])).
% 0.22/0.51  fof(f1312,plain,(
% 0.22/0.51    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_121),
% 0.22/0.51    inference(avatar_component_clause,[],[f1310])).
% 0.22/0.51  fof(f1310,plain,(
% 0.22/0.51    spl1_121 <=> k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_121])])).
% 0.22/0.51  fof(f1452,plain,(
% 0.22/0.51    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_16 | ~spl1_23 | ~spl1_35 | ~spl1_38 | ~spl1_39 | ~spl1_72 | ~spl1_95 | ~spl1_104 | ~spl1_114)),
% 0.22/0.51    inference(forward_demodulation,[],[f1408,f1178])).
% 0.22/0.51  fof(f1408,plain,(
% 0.22/0.51    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))) | (~spl1_16 | ~spl1_23 | ~spl1_35 | ~spl1_38 | ~spl1_39 | ~spl1_72 | ~spl1_95 | ~spl1_114)),
% 0.22/0.51    inference(backward_demodulation,[],[f867,f1389])).
% 0.22/0.51  fof(f867,plain,(
% 0.22/0.51    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) | (~spl1_35 | ~spl1_38 | ~spl1_72)),
% 0.22/0.51    inference(forward_demodulation,[],[f856,f295])).
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_35),
% 0.22/0.51    inference(avatar_component_clause,[],[f293])).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    spl1_35 <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.22/0.51  fof(f856,plain,(
% 0.22/0.51    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k5_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),sK0) | (~spl1_38 | ~spl1_72)),
% 0.22/0.51    inference(resolution,[],[f730,f330])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_38),
% 0.22/0.51    inference(avatar_component_clause,[],[f329])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    spl1_38 <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).
% 0.22/0.51  fof(f730,plain,(
% 0.22/0.51    ( ! [X10] : (~v1_relat_1(X10) | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),sK0)) ) | ~spl1_72),
% 0.22/0.51    inference(avatar_component_clause,[],[f729])).
% 0.22/0.51  fof(f729,plain,(
% 0.22/0.51    spl1_72 <=> ! [X10] : (k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),sK0) | ~v1_relat_1(X10))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_72])])).
% 0.22/0.51  fof(f1313,plain,(
% 0.22/0.51    spl1_121 | ~spl1_7 | ~spl1_11 | ~spl1_30 | ~spl1_52 | ~spl1_85 | ~spl1_89 | ~spl1_92),
% 0.22/0.51    inference(avatar_split_clause,[],[f1086,f892,f874,f825,f530,f259,f129,f111,f1310])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl1_7 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl1_11 <=> ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    spl1_30 <=> ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 0.22/0.51  fof(f530,plain,(
% 0.22/0.51    spl1_52 <=> k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).
% 0.22/0.51  fof(f825,plain,(
% 0.22/0.51    spl1_85 <=> ! [X1,X0] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_85])])).
% 0.22/0.51  fof(f874,plain,(
% 0.22/0.51    spl1_89 <=> k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_89])])).
% 0.22/0.51  fof(f892,plain,(
% 0.22/0.51    spl1_92 <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_92])])).
% 0.22/0.51  fof(f1086,plain,(
% 0.22/0.51    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_7 | ~spl1_11 | ~spl1_30 | ~spl1_52 | ~spl1_85 | ~spl1_89 | ~spl1_92)),
% 0.22/0.51    inference(backward_demodulation,[],[f923,f1054])).
% 0.22/0.51  fof(f1054,plain,(
% 0.22/0.51    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_7 | ~spl1_30 | ~spl1_52 | ~spl1_85)),
% 0.22/0.51    inference(forward_demodulation,[],[f1048,f1047])).
% 0.22/0.51  fof(f1047,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) ) | (~spl1_7 | ~spl1_30 | ~spl1_85)),
% 0.22/0.51    inference(forward_demodulation,[],[f1036,f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl1_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f111])).
% 0.22/0.51  fof(f1036,plain,(
% 0.22/0.51    ( ! [X1] : (k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)) ) | (~spl1_30 | ~spl1_85)),
% 0.22/0.51    inference(superposition,[],[f826,f260])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) ) | ~spl1_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f259])).
% 0.22/0.51  fof(f826,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl1_85),
% 0.22/0.51    inference(avatar_component_clause,[],[f825])).
% 0.22/0.51  fof(f1048,plain,(
% 0.22/0.51    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0)) | (~spl1_7 | ~spl1_30 | ~spl1_52 | ~spl1_85)),
% 0.22/0.51    inference(backward_demodulation,[],[f532,f1047])).
% 0.22/0.51  fof(f532,plain,(
% 0.22/0.51    k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) | ~spl1_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f530])).
% 0.22/0.51  fof(f923,plain,(
% 0.22/0.51    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | (~spl1_11 | ~spl1_89 | ~spl1_92)),
% 0.22/0.51    inference(forward_demodulation,[],[f911,f876])).
% 0.22/0.51  fof(f876,plain,(
% 0.22/0.51    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) | ~spl1_89),
% 0.22/0.51    inference(avatar_component_clause,[],[f874])).
% 0.22/0.51  fof(f911,plain,(
% 0.22/0.51    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) | (~spl1_11 | ~spl1_92)),
% 0.22/0.51    inference(resolution,[],[f893,f130])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) ) | ~spl1_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f893,plain,(
% 0.22/0.51    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_92),
% 0.22/0.51    inference(avatar_component_clause,[],[f892])).
% 0.22/0.51  fof(f1271,plain,(
% 0.22/0.51    spl1_114),
% 0.22/0.51    inference(avatar_split_clause,[],[f79,f1269])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f56,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f62,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f63,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f67,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f68,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f69,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f70,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.22/0.52  fof(f1260,plain,(
% 0.22/0.52    spl1_112 | ~spl1_7 | ~spl1_11 | ~spl1_30 | ~spl1_52 | ~spl1_85 | ~spl1_89 | ~spl1_92 | ~spl1_96),
% 0.22/0.52    inference(avatar_split_clause,[],[f1134,f989,f892,f874,f825,f530,f259,f129,f111,f1257])).
% 0.22/0.52  fof(f989,plain,(
% 0.22/0.52    spl1_96 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_96])])).
% 0.22/0.52  fof(f1134,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_7 | ~spl1_11 | ~spl1_30 | ~spl1_52 | ~spl1_85 | ~spl1_89 | ~spl1_92 | ~spl1_96)),
% 0.22/0.52    inference(backward_demodulation,[],[f991,f1086])).
% 0.22/0.52  fof(f991,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_96),
% 0.22/0.52    inference(avatar_component_clause,[],[f989])).
% 0.22/0.52  fof(f1227,plain,(
% 0.22/0.52    spl1_110 | ~spl1_7 | ~spl1_11 | ~spl1_30 | ~spl1_52 | ~spl1_85 | ~spl1_89 | ~spl1_92),
% 0.22/0.52    inference(avatar_split_clause,[],[f1130,f892,f874,f825,f530,f259,f129,f111,f1224])).
% 0.22/0.52  fof(f1130,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_7 | ~spl1_11 | ~spl1_30 | ~spl1_52 | ~spl1_85 | ~spl1_89 | ~spl1_92)),
% 0.22/0.52    inference(backward_demodulation,[],[f893,f1086])).
% 0.22/0.52  fof(f1179,plain,(
% 0.22/0.52    spl1_104 | ~spl1_7 | ~spl1_30 | ~spl1_52 | ~spl1_85),
% 0.22/0.52    inference(avatar_split_clause,[],[f1054,f825,f530,f259,f111,f1176])).
% 0.22/0.52  fof(f992,plain,(
% 0.22/0.52    spl1_96 | ~spl1_49 | ~spl1_94),
% 0.22/0.52    inference(avatar_split_clause,[],[f971,f962,f446,f989])).
% 0.22/0.52  fof(f446,plain,(
% 0.22/0.52    spl1_49 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_49])])).
% 0.22/0.52  fof(f962,plain,(
% 0.22/0.52    spl1_94 <=> ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_94])])).
% 0.22/0.52  fof(f971,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_49 | ~spl1_94)),
% 0.22/0.52    inference(resolution,[],[f963,f447])).
% 0.22/0.52  fof(f447,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(sK0)) | ~spl1_49),
% 0.22/0.52    inference(avatar_component_clause,[],[f446])).
% 0.22/0.52  fof(f963,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_94),
% 0.22/0.52    inference(avatar_component_clause,[],[f962])).
% 0.22/0.52  fof(f985,plain,(
% 0.22/0.52    spl1_95 | ~spl1_1 | ~spl1_94),
% 0.22/0.52    inference(avatar_split_clause,[],[f980,f962,f83,f982])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl1_1 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.52  fof(f980,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_94)),
% 0.22/0.52    inference(resolution,[],[f963,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl1_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f964,plain,(
% 0.22/0.52    spl1_94 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_19 | ~spl1_74),
% 0.22/0.52    inference(avatar_split_clause,[],[f909,f763,f173,f102,f97,f93,f962])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    spl1_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl1_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    spl1_19 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.22/0.52  fof(f763,plain,(
% 0.22/0.52    spl1_74 <=> ! [X1,X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_74])])).
% 0.22/0.52  fof(f909,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_19 | ~spl1_74)),
% 0.22/0.52    inference(forward_demodulation,[],[f908,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f102])).
% 0.22/0.52  fof(f908,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_19 | ~spl1_74)),
% 0.22/0.52    inference(subsumption_resolution,[],[f907,f175])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    v1_relat_1(k1_xboole_0) | ~spl1_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f173])).
% 0.22/0.52  fof(f907,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_74)),
% 0.22/0.52    inference(subsumption_resolution,[],[f905,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f93])).
% 0.22/0.52  fof(f905,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_74)),
% 0.22/0.52    inference(superposition,[],[f764,f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f97])).
% 0.22/0.52  fof(f764,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_74),
% 0.22/0.52    inference(avatar_component_clause,[],[f763])).
% 0.22/0.52  fof(f904,plain,(
% 0.22/0.52    ~spl1_12 | ~spl1_19 | ~spl1_49 | spl1_92),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f903])).
% 0.22/0.52  fof(f903,plain,(
% 0.22/0.52    $false | (~spl1_12 | ~spl1_19 | ~spl1_49 | spl1_92)),
% 0.22/0.52    inference(subsumption_resolution,[],[f902,f447])).
% 0.22/0.52  fof(f902,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_12 | ~spl1_19 | spl1_92)),
% 0.22/0.52    inference(subsumption_resolution,[],[f900,f175])).
% 0.22/0.52  fof(f900,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_12 | spl1_92)),
% 0.22/0.52    inference(resolution,[],[f894,f137])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f136])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    spl1_12 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.52  fof(f894,plain,(
% 0.22/0.52    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | spl1_92),
% 0.22/0.52    inference(avatar_component_clause,[],[f892])).
% 0.22/0.52  fof(f877,plain,(
% 0.22/0.52    spl1_89 | ~spl1_19 | ~spl1_72),
% 0.22/0.52    inference(avatar_split_clause,[],[f852,f729,f173,f874])).
% 0.22/0.52  fof(f852,plain,(
% 0.22/0.52    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) | (~spl1_19 | ~spl1_72)),
% 0.22/0.52    inference(resolution,[],[f730,f175])).
% 0.22/0.52  fof(f827,plain,(
% 0.22/0.52    spl1_85),
% 0.22/0.52    inference(avatar_split_clause,[],[f81,f825])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f64,f61,f77])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f765,plain,(
% 0.22/0.52    spl1_74),
% 0.22/0.52    inference(avatar_split_clause,[],[f59,f763])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.52  fof(f731,plain,(
% 0.22/0.52    spl1_72 | ~spl1_13 | ~spl1_42 | ~spl1_49),
% 0.22/0.52    inference(avatar_split_clause,[],[f607,f446,f371,f140,f729])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl1_13 <=> sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.52  fof(f371,plain,(
% 0.22/0.52    spl1_42 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).
% 0.22/0.52  fof(f607,plain,(
% 0.22/0.52    ( ! [X10] : (k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),sK0) | ~v1_relat_1(X10)) ) | (~spl1_13 | ~spl1_42 | ~spl1_49)),
% 0.22/0.52    inference(forward_demodulation,[],[f595,f142])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    sK0 = k4_relat_1(k4_relat_1(sK0)) | ~spl1_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f140])).
% 0.22/0.52  fof(f595,plain,(
% 0.22/0.52    ( ! [X10] : (~v1_relat_1(X10) | k4_relat_1(k5_relat_1(k4_relat_1(sK0),X10)) = k5_relat_1(k4_relat_1(X10),k4_relat_1(k4_relat_1(sK0)))) ) | (~spl1_42 | ~spl1_49)),
% 0.22/0.52    inference(resolution,[],[f372,f447])).
% 0.22/0.52  fof(f372,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl1_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f371])).
% 0.22/0.52  fof(f533,plain,(
% 0.22/0.52    spl1_52 | ~spl1_1 | ~spl1_51),
% 0.22/0.52    inference(avatar_split_clause,[],[f522,f505,f83,f530])).
% 0.22/0.52  fof(f505,plain,(
% 0.22/0.52    spl1_51 <=> ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).
% 0.22/0.52  fof(f522,plain,(
% 0.22/0.52    k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) | (~spl1_1 | ~spl1_51)),
% 0.22/0.52    inference(resolution,[],[f506,f85])).
% 0.22/0.52  fof(f506,plain,(
% 0.22/0.52    ( ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18))) ) | ~spl1_51),
% 0.22/0.52    inference(avatar_component_clause,[],[f505])).
% 0.22/0.52  fof(f507,plain,(
% 0.22/0.52    spl1_51 | ~spl1_1 | ~spl1_33),
% 0.22/0.52    inference(avatar_split_clause,[],[f497,f283,f83,f505])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    spl1_33 <=> ! [X1,X0] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.22/0.52  fof(f497,plain,(
% 0.22/0.52    ( ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18))) ) | (~spl1_1 | ~spl1_33)),
% 0.22/0.52    inference(resolution,[],[f284,f85])).
% 0.22/0.52  fof(f284,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))) ) | ~spl1_33),
% 0.22/0.52    inference(avatar_component_clause,[],[f283])).
% 0.22/0.52  fof(f453,plain,(
% 0.22/0.52    ~spl1_1 | ~spl1_9 | spl1_49),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f452])).
% 0.22/0.52  fof(f452,plain,(
% 0.22/0.52    $false | (~spl1_1 | ~spl1_9 | spl1_49)),
% 0.22/0.52    inference(subsumption_resolution,[],[f450,f85])).
% 0.22/0.52  fof(f450,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | (~spl1_9 | spl1_49)),
% 0.22/0.52    inference(resolution,[],[f448,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f119])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl1_9 <=> ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.52  fof(f448,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | spl1_49),
% 0.22/0.52    inference(avatar_component_clause,[],[f446])).
% 0.22/0.52  fof(f373,plain,(
% 0.22/0.52    spl1_42),
% 0.22/0.52    inference(avatar_split_clause,[],[f58,f371])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.52  fof(f344,plain,(
% 0.22/0.52    ~spl1_1 | ~spl1_12 | ~spl1_19 | spl1_39),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f343])).
% 0.22/0.52  fof(f343,plain,(
% 0.22/0.52    $false | (~spl1_1 | ~spl1_12 | ~spl1_19 | spl1_39)),
% 0.22/0.52    inference(subsumption_resolution,[],[f342,f85])).
% 0.22/0.52  fof(f342,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | (~spl1_12 | ~spl1_19 | spl1_39)),
% 0.22/0.52    inference(subsumption_resolution,[],[f340,f175])).
% 0.22/0.52  fof(f340,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | (~spl1_12 | spl1_39)),
% 0.22/0.52    inference(resolution,[],[f334,f137])).
% 0.22/0.52  fof(f334,plain,(
% 0.22/0.52    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_39),
% 0.22/0.52    inference(avatar_component_clause,[],[f333])).
% 0.22/0.52  fof(f339,plain,(
% 0.22/0.52    ~spl1_39 | ~spl1_9 | spl1_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f337,f329,f119,f333])).
% 0.22/0.52  fof(f337,plain,(
% 0.22/0.52    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_9 | spl1_38)),
% 0.22/0.52    inference(resolution,[],[f331,f120])).
% 0.22/0.52  fof(f331,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | spl1_38),
% 0.22/0.52    inference(avatar_component_clause,[],[f329])).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    spl1_35 | ~spl1_19 | ~spl1_32),
% 0.22/0.52    inference(avatar_split_clause,[],[f277,f273,f173,f293])).
% 0.22/0.52  fof(f273,plain,(
% 0.22/0.52    spl1_32 <=> ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_19 | ~spl1_32)),
% 0.22/0.52    inference(resolution,[],[f274,f175])).
% 0.22/0.52  fof(f274,plain,(
% 0.22/0.52    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | ~spl1_32),
% 0.22/0.52    inference(avatar_component_clause,[],[f273])).
% 0.22/0.52  fof(f285,plain,(
% 0.22/0.52    spl1_33),
% 0.22/0.52    inference(avatar_split_clause,[],[f57,f283])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 0.22/0.52  fof(f275,plain,(
% 0.22/0.52    spl1_32 | ~spl1_1 | ~spl1_31),
% 0.22/0.52    inference(avatar_split_clause,[],[f271,f263,f83,f273])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    spl1_31 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | (~spl1_1 | ~spl1_31)),
% 0.22/0.52    inference(resolution,[],[f264,f85])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | ~spl1_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f263])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    spl1_31 | ~spl1_11 | ~spl1_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f185,f136,f129,f263])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | (~spl1_11 | ~spl1_12)),
% 0.22/0.52    inference(resolution,[],[f137,f130])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    spl1_30),
% 0.22/0.52    inference(avatar_split_clause,[],[f80,f259])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f60,f77])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.52    inference(rectify,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    spl1_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f78,f200])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f50,f77])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~spl1_20 | ~spl1_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f191,f187])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f26])).
% 0.22/0.52  fof(f26,conjecture,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ~spl1_2 | ~spl1_6 | spl1_19),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    $false | (~spl1_2 | ~spl1_6 | spl1_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f180,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | (~spl1_6 | spl1_19)),
% 0.22/0.52    inference(resolution,[],[f174,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | spl1_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f173])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    spl1_16 | ~spl1_2 | ~spl1_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f153,f146,f88,f156])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    spl1_14 <=> ! [X1,X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | (~spl1_2 | ~spl1_14)),
% 0.22/0.52    inference(resolution,[],[f147,f90])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) ) | ~spl1_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f146])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl1_14 | ~spl1_8 | ~spl1_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f127,f124,f115,f146])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl1_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl1_10 <=> ! [X1,X0] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) ) | (~spl1_8 | ~spl1_10)),
% 0.22/0.52    inference(resolution,[],[f125,f116])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) ) | ~spl1_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f124])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    spl1_13 | ~spl1_1 | ~spl1_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f132,f129,f83,f140])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    sK0 = k4_relat_1(k4_relat_1(sK0)) | (~spl1_1 | ~spl1_11)),
% 0.22/0.52    inference(resolution,[],[f130,f85])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    spl1_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f66,f136])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl1_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f55,f129])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    spl1_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f65,f124])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl1_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f54,f119])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl1_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f53,f115])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    spl1_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f51,f111])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl1_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f107])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    spl1_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f102])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,axiom,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f97])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f49,f93])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl1_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f88])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl1_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f83])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (11926)------------------------------
% 0.22/0.52  % (11926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11926)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (11926)Memory used [KB]: 7164
% 0.22/0.52  % (11926)Time elapsed: 0.055 s
% 0.22/0.52  % (11926)------------------------------
% 0.22/0.52  % (11926)------------------------------
% 0.22/0.52  % (11914)Success in time 0.164 s
%------------------------------------------------------------------------------
