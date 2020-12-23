%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:26 EST 2020

% Result     : Theorem 25.79s
% Output     : Refutation 25.79s
% Verified   : 
% Statistics : Number of formulae       :  532 (1559 expanded)
%              Number of leaves         :  108 ( 759 expanded)
%              Depth                    :   19
%              Number of atoms          : 1731 (3934 expanded)
%              Number of equality atoms :  435 (1462 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70049,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f53,f57,f61,f65,f76,f85,f90,f100,f111,f146,f166,f178,f216,f265,f302,f335,f467,f686,f722,f726,f740,f749,f789,f815,f844,f877,f995,f1014,f1042,f1070,f1074,f1078,f1145,f1149,f1153,f1157,f1207,f1471,f1540,f1544,f1599,f1607,f1854,f1858,f1862,f2154,f2166,f2346,f2497,f2603,f2861,f3163,f3304,f3308,f3312,f3316,f3324,f3328,f3372,f3380,f3384,f4363,f4454,f9540,f9548,f16643,f18281,f18293,f19574,f20055,f21370,f22080,f22092,f22104,f25148,f25156,f25160,f32394,f36109,f36129,f37581,f39774,f49613,f50355,f54846,f58366,f58374,f61961,f66385,f67254,f68399,f69393,f69978])).

fof(f69978,plain,
    ( ~ spl2_6
    | spl2_34
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_125
    | ~ spl2_138
    | ~ spl2_207
    | ~ spl2_215 ),
    inference(avatar_contradiction_clause,[],[f69977])).

fof(f69977,plain,
    ( $false
    | ~ spl2_6
    | spl2_34
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_125
    | ~ spl2_138
    | ~ spl2_207
    | ~ spl2_215 ),
    inference(subsumption_resolution,[],[f748,f69976])).

fof(f69976,plain,
    ( ! [X134,X133] : k5_xboole_0(X133,X134) = k4_xboole_0(k5_xboole_0(X133,k4_xboole_0(X134,X133)),k4_xboole_0(X133,k4_xboole_0(X133,X134)))
    | ~ spl2_6
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_125
    | ~ spl2_138
    | ~ spl2_207
    | ~ spl2_215 ),
    inference(forward_demodulation,[],[f69548,f69718])).

fof(f69718,plain,
    ( ! [X23,X22] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k4_xboole_0(X22,k5_xboole_0(X22,X23))
    | ~ spl2_6
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_138
    | ~ spl2_207
    | ~ spl2_215 ),
    inference(forward_demodulation,[],[f69501,f62729])).

fof(f62729,plain,
    ( ! [X177,X176] : k4_xboole_0(X176,k4_xboole_0(X176,X177)) = k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177))
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_138
    | ~ spl2_207 ),
    inference(forward_demodulation,[],[f62728,f1152])).

fof(f1152,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f1151,plain,
    ( spl2_49
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f62728,plain,
    ( ! [X177,X176] : k5_xboole_0(X176,k4_xboole_0(X176,X177)) = k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177))
    | ~ spl2_41
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_138
    | ~ spl2_207 ),
    inference(forward_demodulation,[],[f62727,f994])).

fof(f994,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f993])).

fof(f993,plain,
    ( spl2_41
  <=> ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f62727,plain,
    ( ! [X177,X176] : k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X176,k4_xboole_0(X176,X177)))
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_138
    | ~ spl2_207 ),
    inference(forward_demodulation,[],[f62726,f21007])).

fof(f21007,plain,
    ( ! [X39,X38,X40] : k5_xboole_0(X40,k4_xboole_0(X39,X38)) = k5_xboole_0(X38,k5_xboole_0(X40,k5_xboole_0(X39,k4_xboole_0(X38,X39))))
    | ~ spl2_61
    | ~ spl2_115
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f20683,f16642])).

fof(f16642,plain,
    ( ! [X37,X35,X36] : k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(X37,k5_xboole_0(X36,X35))
    | ~ spl2_115 ),
    inference(avatar_component_clause,[],[f16641])).

fof(f16641,plain,
    ( spl2_115
  <=> ! [X36,X35,X37] : k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(X37,k5_xboole_0(X36,X35)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).

fof(f20683,plain,
    ( ! [X39,X38,X40] : k5_xboole_0(X40,k4_xboole_0(X39,X38)) = k5_xboole_0(X38,k5_xboole_0(X40,k5_xboole_0(k4_xboole_0(X38,X39),X39)))
    | ~ spl2_61
    | ~ spl2_123 ),
    inference(superposition,[],[f1861,f20054])).

fof(f20054,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k4_xboole_0(X2,X3),X3)
    | ~ spl2_123 ),
    inference(avatar_component_clause,[],[f20053])).

fof(f20053,plain,
    ( spl2_123
  <=> ! [X3,X2] : k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k4_xboole_0(X2,X3),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).

fof(f1861,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f1860])).

fof(f1860,plain,
    ( spl2_61
  <=> ! [X3,X5,X4] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f62726,plain,
    ( ! [X177,X176] : k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X177,k5_xboole_0(X176,k5_xboole_0(X176,k4_xboole_0(X177,X176)))))
    | ~ spl2_77
    | ~ spl2_115
    | ~ spl2_138
    | ~ spl2_207 ),
    inference(forward_demodulation,[],[f62725,f16642])).

fof(f62725,plain,
    ( ! [X177,X176] : k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X177,k5_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),X176)))
    | ~ spl2_77
    | ~ spl2_138
    | ~ spl2_207 ),
    inference(forward_demodulation,[],[f62230,f3311])).

fof(f3311,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f3310])).

fof(f3310,plain,
    ( spl2_77
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f62230,plain,
    ( ! [X177,X176] : k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)))
    | ~ spl2_138
    | ~ spl2_207 ),
    inference(superposition,[],[f25155,f61960])).

fof(f61960,plain,
    ( ! [X213,X214] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k4_xboole_0(X214,X213)))
    | ~ spl2_207 ),
    inference(avatar_component_clause,[],[f61959])).

fof(f61959,plain,
    ( spl2_207
  <=> ! [X214,X213] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k4_xboole_0(X214,X213))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_207])])).

fof(f25155,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X7,X8))
    | ~ spl2_138 ),
    inference(avatar_component_clause,[],[f25154])).

fof(f25154,plain,
    ( spl2_138
  <=> ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).

fof(f69501,plain,
    ( ! [X23,X22] : k4_xboole_0(X22,k5_xboole_0(X22,X23)) = k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X23,X22)),k5_xboole_0(X22,X23))
    | ~ spl2_6
    | ~ spl2_215 ),
    inference(superposition,[],[f60,f69392])).

fof(f69392,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)
    | ~ spl2_215 ),
    inference(avatar_component_clause,[],[f69391])).

fof(f69391,plain,
    ( spl2_215
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_215])])).

fof(f60,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_6
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f69548,plain,
    ( ! [X134,X133] : k5_xboole_0(X133,X134) = k4_xboole_0(k5_xboole_0(X133,k4_xboole_0(X134,X133)),k4_xboole_0(X133,k5_xboole_0(X133,X134)))
    | ~ spl2_125
    | ~ spl2_215 ),
    inference(superposition,[],[f21369,f69392])).

fof(f21369,plain,
    ( ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X3
    | ~ spl2_125 ),
    inference(avatar_component_clause,[],[f21368])).

fof(f21368,plain,
    ( spl2_125
  <=> ! [X3,X2] : k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).

fof(f748,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_34 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl2_34
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f69393,plain,
    ( spl2_215
    | ~ spl2_46
    | ~ spl2_213 ),
    inference(avatar_split_clause,[],[f68401,f68397,f1076,f69391])).

fof(f1076,plain,
    ( spl2_46
  <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f68397,plain,
    ( spl2_213
  <=> ! [X73,X74] : k4_xboole_0(X73,X74) = k4_xboole_0(k5_xboole_0(X73,X74),X74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).

fof(f68401,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)
    | ~ spl2_46
    | ~ spl2_213 ),
    inference(superposition,[],[f68398,f1077])).

fof(f1077,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f68398,plain,
    ( ! [X74,X73] : k4_xboole_0(X73,X74) = k4_xboole_0(k5_xboole_0(X73,X74),X74)
    | ~ spl2_213 ),
    inference(avatar_component_clause,[],[f68397])).

fof(f68399,plain,
    ( spl2_213
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_35
    | ~ spl2_54
    | ~ spl2_166
    | ~ spl2_212 ),
    inference(avatar_split_clause,[],[f67943,f67252,f37579,f1538,f787,f51,f39,f68397])).

fof(f39,plain,
    ( spl2_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f787,plain,
    ( spl2_35
  <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f1538,plain,
    ( spl2_54
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f37579,plain,
    ( spl2_166
  <=> ! [X3,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_166])])).

fof(f67252,plain,
    ( spl2_212
  <=> ! [X223,X222] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X222,X223),X223),k4_xboole_0(X222,X223)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_212])])).

fof(f67943,plain,
    ( ! [X74,X73] : k4_xboole_0(X73,X74) = k4_xboole_0(k5_xboole_0(X73,X74),X74)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_35
    | ~ spl2_54
    | ~ spl2_166
    | ~ spl2_212 ),
    inference(forward_demodulation,[],[f67942,f788])).

fof(f788,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f787])).

fof(f67942,plain,
    ( ! [X74,X73] : k4_xboole_0(k5_xboole_0(X73,X74),X74) = k4_xboole_0(k4_xboole_0(X73,X74),X74)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_54
    | ~ spl2_166
    | ~ spl2_212 ),
    inference(forward_demodulation,[],[f67941,f37938])).

fof(f37938,plain,
    ( ! [X70,X68,X69] : k4_xboole_0(k4_xboole_0(X68,X69),X70) = k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k5_xboole_0(X68,X69),X70)))
    | ~ spl2_1
    | ~ spl2_54
    | ~ spl2_166 ),
    inference(forward_demodulation,[],[f37770,f40])).

fof(f40,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f37770,plain,
    ( ! [X70,X68,X69] : k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k5_xboole_0(X68,X69),X70))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X68,X69),k1_xboole_0),X70)
    | ~ spl2_54
    | ~ spl2_166 ),
    inference(superposition,[],[f1539,f37580])).

fof(f37580,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4))
    | ~ spl2_166 ),
    inference(avatar_component_clause,[],[f37579])).

fof(f1539,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f67941,plain,
    ( ! [X74,X73] : k4_xboole_0(k5_xboole_0(X73,X74),X74) = k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k5_xboole_0(X73,X74),X74)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_212 ),
    inference(forward_demodulation,[],[f67486,f40])).

fof(f67486,plain,
    ( ! [X74,X73] : k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k5_xboole_0(X73,X74),X74))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X73,X74),X74),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_212 ),
    inference(superposition,[],[f52,f67253])).

fof(f67253,plain,
    ( ! [X222,X223] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X222,X223),X223),k4_xboole_0(X222,X223))
    | ~ spl2_212 ),
    inference(avatar_component_clause,[],[f67252])).

fof(f52,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f67254,plain,
    ( spl2_212
    | ~ spl2_171
    | ~ spl2_211 ),
    inference(avatar_split_clause,[],[f66658,f66383,f39772,f67252])).

fof(f39772,plain,
    ( spl2_171
  <=> ! [X214,X213] : k4_xboole_0(X213,X214) = k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).

fof(f66383,plain,
    ( spl2_211
  <=> ! [X106,X105,X107] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X107,X105),k4_xboole_0(X107,k4_xboole_0(X105,X106))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_211])])).

fof(f66658,plain,
    ( ! [X222,X223] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X222,X223),X223),k4_xboole_0(X222,X223))
    | ~ spl2_171
    | ~ spl2_211 ),
    inference(superposition,[],[f66384,f39773])).

fof(f39773,plain,
    ( ! [X213,X214] : k4_xboole_0(X213,X214) = k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213))
    | ~ spl2_171 ),
    inference(avatar_component_clause,[],[f39772])).

fof(f66384,plain,
    ( ! [X107,X105,X106] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X107,X105),k4_xboole_0(X107,k4_xboole_0(X105,X106)))
    | ~ spl2_211 ),
    inference(avatar_component_clause,[],[f66383])).

fof(f66385,plain,
    ( spl2_211
    | ~ spl2_73
    | ~ spl2_205 ),
    inference(avatar_split_clause,[],[f65834,f58372,f2859,f66383])).

fof(f2859,plain,
    ( spl2_73
  <=> ! [X34,X36,X35] : k4_xboole_0(X35,X36) = k4_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f58372,plain,
    ( spl2_205
  <=> ! [X124,X126,X125] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(X124,k4_xboole_0(X126,k4_xboole_0(X124,X125)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).

fof(f65834,plain,
    ( ! [X107,X105,X106] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X107,X105),k4_xboole_0(X107,k4_xboole_0(X105,X106)))
    | ~ spl2_73
    | ~ spl2_205 ),
    inference(superposition,[],[f58373,f2860])).

fof(f2860,plain,
    ( ! [X35,X36,X34] : k4_xboole_0(X35,X36) = k4_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35))
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f2859])).

fof(f58373,plain,
    ( ! [X125,X126,X124] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(X124,k4_xboole_0(X126,k4_xboole_0(X124,X125))))
    | ~ spl2_205 ),
    inference(avatar_component_clause,[],[f58372])).

fof(f61961,plain,
    ( spl2_207
    | ~ spl2_2
    | ~ spl2_59
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_78
    | ~ spl2_94
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_171
    | ~ spl2_203 ),
    inference(avatar_split_clause,[],[f61750,f58364,f39772,f20053,f16641,f3378,f3314,f3310,f1860,f1856,f1852,f43,f61959])).

fof(f43,plain,
    ( spl2_2
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1852,plain,
    ( spl2_59
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f1856,plain,
    ( spl2_60
  <=> ! [X5,X4] : k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f3314,plain,
    ( spl2_78
  <=> ! [X1,X3,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f3378,plain,
    ( spl2_94
  <=> ! [X20,X22,X21] : k5_xboole_0(X21,k5_xboole_0(X20,X22)) = k5_xboole_0(k5_xboole_0(X21,X22),X20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).

fof(f58364,plain,
    ( spl2_203
  <=> ! [X157,X156,X158] : k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(X156,k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).

fof(f61750,plain,
    ( ! [X213,X214] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k4_xboole_0(X214,X213)))
    | ~ spl2_2
    | ~ spl2_59
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_78
    | ~ spl2_94
    | ~ spl2_115
    | ~ spl2_123
    | ~ spl2_171
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f61749,f21007])).

fof(f61749,plain,
    ( ! [X213,X214] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k5_xboole_0(X213,k5_xboole_0(X214,k4_xboole_0(X213,X214)))))
    | ~ spl2_2
    | ~ spl2_59
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_78
    | ~ spl2_94
    | ~ spl2_171
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f61748,f8846])).

fof(f8846,plain,
    ( ! [X92,X90,X93,X91] : k5_xboole_0(X91,k5_xboole_0(X90,k5_xboole_0(X93,X92))) = k5_xboole_0(X91,k5_xboole_0(X90,k5_xboole_0(X92,X93)))
    | ~ spl2_2
    | ~ spl2_78
    | ~ spl2_94 ),
    inference(forward_demodulation,[],[f8845,f44])).

fof(f44,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f8845,plain,
    ( ! [X92,X90,X93,X91] : k5_xboole_0(X91,k5_xboole_0(k5_xboole_0(X90,X92),X93)) = k5_xboole_0(X91,k5_xboole_0(X90,k5_xboole_0(X93,X92)))
    | ~ spl2_2
    | ~ spl2_78
    | ~ spl2_94 ),
    inference(forward_demodulation,[],[f8844,f3315])).

fof(f3315,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f3314])).

fof(f8844,plain,
    ( ! [X92,X90,X93,X91] : k5_xboole_0(X91,k5_xboole_0(k5_xboole_0(X90,X92),X93)) = k5_xboole_0(k5_xboole_0(X90,X91),k5_xboole_0(X93,X92))
    | ~ spl2_2
    | ~ spl2_78
    | ~ spl2_94 ),
    inference(forward_demodulation,[],[f8693,f44])).

fof(f8693,plain,
    ( ! [X92,X90,X93,X91] : k5_xboole_0(k5_xboole_0(X90,X91),k5_xboole_0(X93,X92)) = k5_xboole_0(k5_xboole_0(X91,k5_xboole_0(X90,X92)),X93)
    | ~ spl2_78
    | ~ spl2_94 ),
    inference(superposition,[],[f3379,f3315])).

fof(f3379,plain,
    ( ! [X21,X22,X20] : k5_xboole_0(X21,k5_xboole_0(X20,X22)) = k5_xboole_0(k5_xboole_0(X21,X22),X20)
    | ~ spl2_94 ),
    inference(avatar_component_clause,[],[f3378])).

fof(f61748,plain,
    ( ! [X213,X214] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k5_xboole_0(X213,k5_xboole_0(k4_xboole_0(X213,X214),X214))))
    | ~ spl2_59
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_77
    | ~ spl2_171
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f61747,f1980])).

fof(f1980,plain,
    ( ! [X30,X33,X31,X32] : k5_xboole_0(X33,k5_xboole_0(X31,k5_xboole_0(X30,X32))) = k5_xboole_0(X30,k5_xboole_0(X33,k5_xboole_0(X31,X32)))
    | ~ spl2_61 ),
    inference(superposition,[],[f1861,f1861])).

fof(f61747,plain,
    ( ! [X213,X214] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k5_xboole_0(k4_xboole_0(X213,X214),k5_xboole_0(X213,X214))))
    | ~ spl2_59
    | ~ spl2_60
    | ~ spl2_77
    | ~ spl2_171
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f61746,f3311])).

fof(f61746,plain,
    ( ! [X213,X214] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(k4_xboole_0(X213,X214),k5_xboole_0(k5_xboole_0(X213,X214),X213)))
    | ~ spl2_59
    | ~ spl2_60
    | ~ spl2_171
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f61449,f1951])).

fof(f1951,plain,
    ( ! [X17,X15,X16] : k5_xboole_0(X17,k4_xboole_0(X15,k4_xboole_0(X15,X16))) = k5_xboole_0(k4_xboole_0(X15,X16),k5_xboole_0(X17,X15))
    | ~ spl2_59
    | ~ spl2_60 ),
    inference(superposition,[],[f1853,f1857])).

fof(f1857,plain,
    ( ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5)) = X4
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f1856])).

fof(f1853,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f1852])).

fof(f61449,plain,
    ( ! [X213,X214] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X213,k4_xboole_0(X213,X214))))
    | ~ spl2_171
    | ~ spl2_203 ),
    inference(superposition,[],[f58365,f39773])).

fof(f58365,plain,
    ( ! [X158,X156,X157] : k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(X156,k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157)))))
    | ~ spl2_203 ),
    inference(avatar_component_clause,[],[f58364])).

fof(f58374,plain,
    ( spl2_205
    | ~ spl2_28
    | ~ spl2_51
    | ~ spl2_198 ),
    inference(avatar_split_clause,[],[f55240,f54844,f1205,f684,f58372])).

fof(f684,plain,
    ( spl2_28
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1205,plain,
    ( spl2_51
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f54844,plain,
    ( spl2_198
  <=> ! [X27,X29,X28] : k1_xboole_0 = k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X29,X28))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_198])])).

fof(f55240,plain,
    ( ! [X125,X126,X124] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(X124,k4_xboole_0(X126,k4_xboole_0(X124,X125))))
    | ~ spl2_28
    | ~ spl2_51
    | ~ spl2_198 ),
    inference(forward_demodulation,[],[f54881,f685])).

fof(f685,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f684])).

fof(f54881,plain,
    ( ! [X125,X126,X124] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(k5_xboole_0(X124,k1_xboole_0),k4_xboole_0(X126,k4_xboole_0(X124,X125))))
    | ~ spl2_51
    | ~ spl2_198 ),
    inference(superposition,[],[f54845,f1206])).

fof(f1206,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f54845,plain,
    ( ! [X28,X29,X27] : k1_xboole_0 = k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X29,X28)))
    | ~ spl2_198 ),
    inference(avatar_component_clause,[],[f54844])).

fof(f58366,plain,
    ( spl2_203
    | ~ spl2_46
    | ~ spl2_58
    | ~ spl2_188 ),
    inference(avatar_split_clause,[],[f50807,f50353,f1605,f1076,f58364])).

fof(f1605,plain,
    ( spl2_58
  <=> ! [X25,X26] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X26,X25),k5_xboole_0(X25,k4_xboole_0(X26,X25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f50353,plain,
    ( spl2_188
  <=> ! [X18,X17,X19] : k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18)))) = X17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).

fof(f50807,plain,
    ( ! [X158,X156,X157] : k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(X156,k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157)))))
    | ~ spl2_46
    | ~ spl2_58
    | ~ spl2_188 ),
    inference(forward_demodulation,[],[f50549,f1077])).

fof(f50549,plain,
    ( ! [X158,X156,X157] : k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157))),X156))
    | ~ spl2_58
    | ~ spl2_188 ),
    inference(superposition,[],[f1606,f50354])).

fof(f50354,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18)))) = X17
    | ~ spl2_188 ),
    inference(avatar_component_clause,[],[f50353])).

fof(f1606,plain,
    ( ! [X26,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X26,X25),k5_xboole_0(X25,k4_xboole_0(X26,X25)))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f1605])).

fof(f54846,plain,
    ( spl2_198
    | ~ spl2_164
    | ~ spl2_187 ),
    inference(avatar_split_clause,[],[f49770,f49611,f36127,f54844])).

fof(f36127,plain,
    ( spl2_164
  <=> ! [X44,X46,X45] : k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_164])])).

fof(f49611,plain,
    ( spl2_187
  <=> ! [X131,X130,X132] : k1_xboole_0 = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_187])])).

fof(f49770,plain,
    ( ! [X28,X29,X27] : k1_xboole_0 = k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X29,X28)))
    | ~ spl2_164
    | ~ spl2_187 ),
    inference(superposition,[],[f49612,f36128])).

fof(f36128,plain,
    ( ! [X45,X46,X44] : k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46)))
    | ~ spl2_164 ),
    inference(avatar_component_clause,[],[f36127])).

fof(f49612,plain,
    ( ! [X132,X130,X131] : k1_xboole_0 = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131)))))
    | ~ spl2_187 ),
    inference(avatar_component_clause,[],[f49611])).

fof(f50355,plain,
    ( spl2_188
    | ~ spl2_3
    | ~ spl2_28
    | ~ spl2_187 ),
    inference(avatar_split_clause,[],[f50101,f49611,f684,f47,f50353])).

fof(f47,plain,
    ( spl2_3
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f50101,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18)))) = X17
    | ~ spl2_3
    | ~ spl2_28
    | ~ spl2_187 ),
    inference(forward_demodulation,[],[f49777,f685])).

fof(f49777,plain,
    ( ! [X19,X17,X18] : k5_xboole_0(X17,k1_xboole_0) = k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18))))
    | ~ spl2_3
    | ~ spl2_187 ),
    inference(superposition,[],[f48,f49612])).

fof(f48,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49613,plain,
    ( spl2_187
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_28
    | ~ spl2_30
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81
    | ~ spl2_117
    | ~ spl2_135
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f41370,f32392,f22102,f18279,f3326,f3322,f3302,f1538,f1205,f1155,f1151,f1147,f720,f684,f51,f39,f49611])).

fof(f720,plain,
    ( spl2_30
  <=> ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1147,plain,
    ( spl2_48
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1155,plain,
    ( spl2_50
  <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f3302,plain,
    ( spl2_75
  <=> ! [X9,X8] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(k4_xboole_0(X8,X9),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f3322,plain,
    ( spl2_80
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f3326,plain,
    ( spl2_81
  <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f18279,plain,
    ( spl2_117
  <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).

fof(f22102,plain,
    ( spl2_135
  <=> ! [X16,X15,X17] : k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X15,X16)))) = X15 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f32392,plain,
    ( spl2_151
  <=> ! [X5,X7,X6] : k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,k4_xboole_0(X5,X7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).

fof(f41370,plain,
    ( ! [X132,X130,X131] : k1_xboole_0 = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131)))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_28
    | ~ spl2_30
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81
    | ~ spl2_117
    | ~ spl2_135
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41369,f721])).

fof(f721,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f720])).

fof(f41369,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131))))) = k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X130,k4_xboole_0(X130,X131)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_28
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81
    | ~ spl2_117
    | ~ spl2_135
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41368,f25045])).

fof(f25045,plain,
    ( ! [X88,X87,X89] : k4_xboole_0(X87,k4_xboole_0(X87,X88)) = k4_xboole_0(k4_xboole_0(X87,k4_xboole_0(X87,X88)),k4_xboole_0(X89,k4_xboole_0(X88,k4_xboole_0(X88,X87))))
    | ~ spl2_28
    | ~ spl2_117
    | ~ spl2_135 ),
    inference(forward_demodulation,[],[f24894,f685])).

fof(f24894,plain,
    ( ! [X88,X87,X89] : k4_xboole_0(X87,k4_xboole_0(X87,X88)) = k4_xboole_0(k4_xboole_0(X87,k4_xboole_0(X87,X88)),k4_xboole_0(X89,k5_xboole_0(k4_xboole_0(X88,k4_xboole_0(X88,X87)),k1_xboole_0)))
    | ~ spl2_117
    | ~ spl2_135 ),
    inference(superposition,[],[f22103,f18280])).

fof(f18280,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))
    | ~ spl2_117 ),
    inference(avatar_component_clause,[],[f18279])).

fof(f22103,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X15,X16)))) = X15
    | ~ spl2_135 ),
    inference(avatar_component_clause,[],[f22102])).

fof(f41368,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131)))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41367,f5566])).

fof(f5566,plain,
    ( ! [X80,X78,X81,X79] : k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(X78,k4_xboole_0(X80,X81)))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81 ),
    inference(backward_demodulation,[],[f4110,f5565])).

fof(f5565,plain,
    ( ! [X54,X55,X53] : k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X55,k4_xboole_0(X53,X54)))) = k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X55,X54))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81 ),
    inference(forward_demodulation,[],[f5564,f3323])).

fof(f3323,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f3322])).

fof(f5564,plain,
    ( ! [X54,X55,X53] : k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(X53,k4_xboole_0(X53,X54)))) = k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X55,k4_xboole_0(X53,X54))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81 ),
    inference(forward_demodulation,[],[f5435,f4215])).

fof(f4215,plain,
    ( ! [X50,X48,X49] : k5_xboole_0(k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50))),k4_xboole_0(X48,k4_xboole_0(X48,X49))) = k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X50,k4_xboole_0(X48,X49))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4167,f4082])).

fof(f4082,plain,
    ( ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X37)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X38)))) = k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X38,k4_xboole_0(X36,X37))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4081,f1539])).

fof(f4081,plain,
    ( ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X37)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X38)))) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X38)),k4_xboole_0(X36,X37))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f3874,f2267])).

fof(f2267,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X30))) = k4_xboole_0(k4_xboole_0(X28,X29),X30)
    | ~ spl2_1
    | ~ spl2_51
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f2177,f40])).

fof(f2177,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X30))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X28,X29),k1_xboole_0),X30)
    | ~ spl2_51
    | ~ spl2_54 ),
    inference(superposition,[],[f1539,f1206])).

fof(f3874,plain,
    ( ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X37)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X38)))) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X38)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X38)),k4_xboole_0(X36,k4_xboole_0(X36,X37))))
    | ~ spl2_4
    | ~ spl2_80 ),
    inference(superposition,[],[f52,f3323])).

fof(f4167,plain,
    ( ! [X50,X48,X49] : k4_xboole_0(k4_xboole_0(X48,k4_xboole_0(X48,X49)),k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50)))) = k5_xboole_0(k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50))),k4_xboole_0(X48,k4_xboole_0(X48,X49)))
    | ~ spl2_54
    | ~ spl2_75 ),
    inference(superposition,[],[f3303,f1539])).

fof(f3303,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(k4_xboole_0(X8,X9),X8)
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f3302])).

fof(f5435,plain,
    ( ! [X54,X55,X53] : k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(X53,k4_xboole_0(X53,X54)))) = k5_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X54,X55))),k4_xboole_0(X53,k4_xboole_0(X53,X54)))
    | ~ spl2_80
    | ~ spl2_81 ),
    inference(superposition,[],[f3327,f3323])).

fof(f3327,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f3326])).

fof(f4110,plain,
    ( ! [X80,X78,X81,X79] : k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(X80,X81)))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4109,f3855])).

fof(f3855,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,k4_xboole_0(X5,X7)))))
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(superposition,[],[f3323,f1539])).

fof(f4109,plain,
    ( ! [X80,X78,X81,X79] : k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X80,X81)))))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4108,f1539])).

fof(f4108,plain,
    ( ! [X80,X78,X81,X79] : k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81)))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4107,f1539])).

fof(f4107,plain,
    ( ! [X80,X78,X81,X79] : k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81))) = k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4106,f1539])).

fof(f4106,plain,
    ( ! [X80,X78,X81,X79] : k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X80,k4_xboole_0(X78,X79)))),X81)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f3888,f4082])).

fof(f3888,plain,
    ( ! [X80,X78,X81,X79] : k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,X80)))),X81)
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(superposition,[],[f1539,f3323])).

fof(f41367,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X132,k4_xboole_0(X130,X131)),X131)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41366,f4095])).

fof(f4095,plain,
    ( ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X57,X59)) = k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X59,X58)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4094,f3323])).

fof(f4094,plain,
    ( ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X57,X59))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4093,f2254])).

fof(f2254,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)))
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f2253,f1148])).

fof(f1148,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f2253,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f2168,f1152])).

fof(f2168,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2))),X4)
    | ~ spl2_50
    | ~ spl2_54 ),
    inference(superposition,[],[f1539,f1156])).

fof(f1156,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f1155])).

fof(f4093,plain,
    ( ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X57,X59))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f4092,f4082])).

fof(f4092,plain,
    ( ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X59,k4_xboole_0(X57,X58)))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f3881,f4082])).

fof(f3881,plain,
    ( ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X58)),k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X58,X59)))))
    | ~ spl2_48
    | ~ spl2_80 ),
    inference(superposition,[],[f1148,f3323])).

fof(f41366,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(k4_xboole_0(X130,X131),k4_xboole_0(X130,k4_xboole_0(X132,k4_xboole_0(X130,X131))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41365,f2254])).

fof(f41365,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X130,X131),k4_xboole_0(X130,k4_xboole_0(X132,k4_xboole_0(X130,X131))))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_75
    | ~ spl2_80
    | ~ spl2_81
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41364,f5566])).

fof(f41364,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X132,k4_xboole_0(X130,k4_xboole_0(X130,X131))),k4_xboole_0(X130,X131))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41363,f40])).

fof(f41363,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X132,k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k1_xboole_0)),k4_xboole_0(X130,X131))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_80
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41362,f4082])).

fof(f41362,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X132,k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k1_xboole_0))))))
    | ~ spl2_54
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f41075,f1539])).

fof(f41075,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k1_xboole_0))))
    | ~ spl2_117
    | ~ spl2_151 ),
    inference(superposition,[],[f32393,f18280])).

fof(f32393,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,k4_xboole_0(X5,X7)))))
    | ~ spl2_151 ),
    inference(avatar_component_clause,[],[f32392])).

fof(f39774,plain,
    ( spl2_171
    | ~ spl2_41
    | ~ spl2_132
    | ~ spl2_138
    | ~ spl2_139
    | ~ spl2_159 ),
    inference(avatar_split_clause,[],[f36950,f36107,f25158,f25154,f22090,f993,f39772])).

fof(f22090,plain,
    ( spl2_132
  <=> ! [X27,X26] : k5_xboole_0(X26,X27) = k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).

fof(f25158,plain,
    ( spl2_139
  <=> ! [X32,X31] : k4_xboole_0(X31,X32) = k5_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X32,X31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f36107,plain,
    ( spl2_159
  <=> ! [X69,X68,X70] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).

fof(f36950,plain,
    ( ! [X213,X214] : k4_xboole_0(X213,X214) = k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213))
    | ~ spl2_41
    | ~ spl2_132
    | ~ spl2_138
    | ~ spl2_139
    | ~ spl2_159 ),
    inference(forward_demodulation,[],[f36946,f994])).

fof(f36946,plain,
    ( ! [X213,X214] : k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X213,X214))
    | ~ spl2_132
    | ~ spl2_138
    | ~ spl2_139
    | ~ spl2_159 ),
    inference(backward_demodulation,[],[f27375,f36765])).

fof(f36765,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5))
    | ~ spl2_132
    | ~ spl2_159 ),
    inference(superposition,[],[f36108,f22091])).

fof(f22091,plain,
    ( ! [X26,X27] : k5_xboole_0(X26,X27) = k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))
    | ~ spl2_132 ),
    inference(avatar_component_clause,[],[f22090])).

fof(f36108,plain,
    ( ! [X70,X68,X69] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))
    | ~ spl2_159 ),
    inference(avatar_component_clause,[],[f36107])).

fof(f27375,plain,
    ( ! [X213,X214] : k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X214,X213),k5_xboole_0(X213,X214)),k4_xboole_0(X213,X214))
    | ~ spl2_138
    | ~ spl2_139 ),
    inference(superposition,[],[f25155,f25159])).

fof(f25159,plain,
    ( ! [X31,X32] : k4_xboole_0(X31,X32) = k5_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X32,X31))
    | ~ spl2_139 ),
    inference(avatar_component_clause,[],[f25158])).

fof(f37581,plain,
    ( spl2_166
    | ~ spl2_136
    | ~ spl2_159 ),
    inference(avatar_split_clause,[],[f36764,f36107,f25146,f37579])).

fof(f25146,plain,
    ( spl2_136
  <=> ! [X32,X33] : k5_xboole_0(X33,X32) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).

fof(f36764,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4))
    | ~ spl2_136
    | ~ spl2_159 ),
    inference(superposition,[],[f36108,f25147])).

fof(f25147,plain,
    ( ! [X33,X32] : k5_xboole_0(X33,X32) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))
    | ~ spl2_136 ),
    inference(avatar_component_clause,[],[f25146])).

fof(f36129,plain,
    ( spl2_164
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_54
    | ~ spl2_55
    | ~ spl2_123 ),
    inference(avatar_split_clause,[],[f20970,f20053,f1542,f1538,f1076,f59,f51,f39,f36127])).

fof(f1542,plain,
    ( spl2_55
  <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f20970,plain,
    ( ! [X45,X46,X44] : k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_54
    | ~ spl2_55
    | ~ spl2_123 ),
    inference(backward_demodulation,[],[f2182,f20963])).

fof(f20963,plain,
    ( ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X3
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_55
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f20940,f40])).

fof(f20940,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_55
    | ~ spl2_123 ),
    inference(backward_demodulation,[],[f378,f20939])).

fof(f20939,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X8,k4_xboole_0(X7,X8)))
    | ~ spl2_46
    | ~ spl2_55
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f20672,f1077])).

fof(f20672,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),X8))
    | ~ spl2_55
    | ~ spl2_123 ),
    inference(superposition,[],[f1543,f20054])).

fof(f1543,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9)))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f378,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,X2)))) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f52,f60])).

fof(f2182,plain,
    ( ! [X45,X46,X44] : k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X44,X45)),X46)
    | ~ spl2_6
    | ~ spl2_54 ),
    inference(superposition,[],[f1539,f60])).

fof(f36109,plain,
    ( spl2_159
    | ~ spl2_55
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f2678,f2601,f1542,f36107])).

fof(f2601,plain,
    ( spl2_70
  <=> ! [X16,X15,X14] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f2678,plain,
    ( ! [X70,X68,X69] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))
    | ~ spl2_55
    | ~ spl2_70 ),
    inference(superposition,[],[f1543,f2602])).

fof(f2602,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f2601])).

fof(f32394,plain,
    ( spl2_151
    | ~ spl2_54
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f3855,f3322,f1538,f32392])).

fof(f25160,plain,
    ( spl2_139
    | ~ spl2_101
    | ~ spl2_129 ),
    inference(avatar_split_clause,[],[f23218,f22078,f9538,f25158])).

fof(f9538,plain,
    ( spl2_101
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f22078,plain,
    ( spl2_129
  <=> ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X23,k5_xboole_0(X22,k4_xboole_0(X23,X22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).

fof(f23218,plain,
    ( ! [X31,X32] : k4_xboole_0(X31,X32) = k5_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X32,X31))
    | ~ spl2_101
    | ~ spl2_129 ),
    inference(superposition,[],[f9539,f22079])).

fof(f22079,plain,
    ( ! [X23,X22] : k4_xboole_0(X22,X23) = k5_xboole_0(X23,k5_xboole_0(X22,k4_xboole_0(X23,X22)))
    | ~ spl2_129 ),
    inference(avatar_component_clause,[],[f22078])).

fof(f9539,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f9538])).

fof(f25156,plain,
    ( spl2_138
    | ~ spl2_66
    | ~ spl2_129 ),
    inference(avatar_split_clause,[],[f23207,f22078,f2164,f25154])).

fof(f2164,plain,
    ( spl2_66
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f23207,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X7,X8))
    | ~ spl2_66
    | ~ spl2_129 ),
    inference(superposition,[],[f2165,f22079])).

fof(f2165,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f2164])).

fof(f25148,plain,
    ( spl2_136
    | ~ spl2_103
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f19658,f19572,f9546,f25146])).

fof(f9546,plain,
    ( spl2_103
  <=> ! [X25,X27,X26] : k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f19572,plain,
    ( spl2_121
  <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).

fof(f19658,plain,
    ( ! [X33,X32] : k5_xboole_0(X33,X32) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))
    | ~ spl2_103
    | ~ spl2_121 ),
    inference(superposition,[],[f9547,f19573])).

fof(f19573,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3
    | ~ spl2_121 ),
    inference(avatar_component_clause,[],[f19572])).

fof(f9547,plain,
    ( ! [X26,X27,X25] : k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X25)
    | ~ spl2_103 ),
    inference(avatar_component_clause,[],[f9546])).

fof(f22104,plain,
    ( spl2_135
    | ~ spl2_46
    | ~ spl2_74
    | ~ spl2_123 ),
    inference(avatar_split_clause,[],[f21000,f20053,f3161,f1076,f22102])).

fof(f3161,plain,
    ( spl2_74
  <=> ! [X75,X77,X76] : k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X75,k4_xboole_0(X76,X75)))) = X75 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f21000,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X15,X16)))) = X15
    | ~ spl2_46
    | ~ spl2_74
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f20676,f1077])).

fof(f20676,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(k4_xboole_0(X15,X16),X16))) = X15
    | ~ spl2_74
    | ~ spl2_123 ),
    inference(superposition,[],[f3162,f20054])).

fof(f3162,plain,
    ( ! [X76,X77,X75] : k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X75,k4_xboole_0(X76,X75)))) = X75
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f3161])).

fof(f22092,plain,
    ( spl2_132
    | ~ spl2_95
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f19655,f19572,f3382,f22090])).

fof(f3382,plain,
    ( spl2_95
  <=> ! [X13,X12,X14] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f19655,plain,
    ( ! [X26,X27] : k5_xboole_0(X26,X27) = k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))
    | ~ spl2_95
    | ~ spl2_121 ),
    inference(superposition,[],[f3383,f19573])).

fof(f3383,plain,
    ( ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f3382])).

fof(f22080,plain,
    ( spl2_129
    | ~ spl2_92
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f19653,f19572,f3370,f22078])).

fof(f3370,plain,
    ( spl2_92
  <=> ! [X16,X15,X14] : k5_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X16)),k5_xboole_0(X15,X16)) = X14 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f19653,plain,
    ( ! [X23,X22] : k4_xboole_0(X22,X23) = k5_xboole_0(X23,k5_xboole_0(X22,k4_xboole_0(X23,X22)))
    | ~ spl2_92
    | ~ spl2_121 ),
    inference(superposition,[],[f3371,f19573])).

fof(f3371,plain,
    ( ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X16)),k5_xboole_0(X15,X16)) = X14
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f3370])).

fof(f21370,plain,
    ( spl2_125
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_55
    | ~ spl2_123 ),
    inference(avatar_split_clause,[],[f20963,f20053,f1542,f1076,f59,f51,f39,f21368])).

fof(f20055,plain,
    ( spl2_123
    | ~ spl2_61
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f19647,f19572,f1860,f20053])).

fof(f19647,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k4_xboole_0(X2,X3),X3)
    | ~ spl2_61
    | ~ spl2_121 ),
    inference(superposition,[],[f1861,f19573])).

fof(f19574,plain,
    ( spl2_121
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_47
    | ~ spl2_49
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f19496,f18291,f1151,f1143,f724,f51,f43,f39,f19572])).

fof(f724,plain,
    ( spl2_31
  <=> ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1143,plain,
    ( spl2_47
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f18291,plain,
    ( spl2_120
  <=> ! [X27,X26] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f19496,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_47
    | ~ spl2_49
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f19494,f40])).

fof(f19494,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_47
    | ~ spl2_49
    | ~ spl2_120 ),
    inference(backward_demodulation,[],[f19488,f19493])).

fof(f19493,plain,
    ( ! [X14,X15] : k1_xboole_0 = k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_31
    | ~ spl2_47
    | ~ spl2_49
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f19492,f725])).

fof(f725,plain,
    ( ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f724])).

fof(f19492,plain,
    ( ! [X14,X15] : k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X15,X14)) = k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_49
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f19491,f1376])).

fof(f1376,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(k4_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X1),X3)))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_49 ),
    inference(backward_demodulation,[],[f1174,f1358])).

fof(f1358,plain,
    ( ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X5),X6)) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6)
    | ~ spl2_2
    | ~ spl2_49 ),
    inference(superposition,[],[f44,f1152])).

fof(f1174,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ spl2_2
    | ~ spl2_47 ),
    inference(superposition,[],[f44,f1144])).

fof(f1144,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f1143])).

fof(f19491,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)))) = k5_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))
    | ~ spl2_1
    | ~ spl2_47
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f19216,f40])).

fof(f19216,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)))) = k5_xboole_0(X15,k4_xboole_0(k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))),k1_xboole_0))
    | ~ spl2_47
    | ~ spl2_120 ),
    inference(superposition,[],[f1144,f18292])).

fof(f18292,plain,
    ( ! [X26,X27] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26)
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f18291])).

fof(f19488,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f19210,f40])).

fof(f19210,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_120 ),
    inference(superposition,[],[f52,f18292])).

fof(f18293,plain,
    ( spl2_120
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_50
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f1451,f1205,f1155,f1076,f59,f43,f18291])).

fof(f1451,plain,
    ( ! [X26,X27] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26)
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_50
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f1450,f1206])).

fof(f1450,plain,
    ( ! [X26,X27] : k4_xboole_0(k4_xboole_0(X26,X27),X26) = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26)
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_46
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f1406,f1112])).

fof(f1112,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_46 ),
    inference(superposition,[],[f1077,f44])).

fof(f1406,plain,
    ( ! [X26,X27] : k4_xboole_0(k4_xboole_0(X26,X27),X26) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X26,X27),k5_xboole_0(X27,k4_xboole_0(X27,X26))),X26)
    | ~ spl2_6
    | ~ spl2_50 ),
    inference(superposition,[],[f60,f1156])).

fof(f18281,plain,
    ( spl2_117
    | ~ spl2_1
    | ~ spl2_30
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f1324,f1147,f720,f39,f18279])).

fof(f1324,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))
    | ~ spl2_1
    | ~ spl2_30
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1323,f721])).

fof(f1323,plain,
    ( ! [X10,X9] : k4_xboole_0(X10,X10) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))
    | ~ spl2_1
    | ~ spl2_30
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1322,f40])).

fof(f1322,plain,
    ( ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))
    | ~ spl2_30
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1321,f721])).

fof(f1321,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X9)))
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1289,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1289,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))
    | ~ spl2_48 ),
    inference(superposition,[],[f1148,f1148])).

fof(f16643,plain,
    ( spl2_115
    | ~ spl2_28
    | ~ spl2_63
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f4629,f4452,f2152,f684,f16641])).

fof(f2152,plain,
    ( spl2_63
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f4452,plain,
    ( spl2_98
  <=> ! [X11,X12] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X12,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f4629,plain,
    ( ! [X37,X35,X36] : k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(X37,k5_xboole_0(X36,X35))
    | ~ spl2_28
    | ~ spl2_63
    | ~ spl2_98 ),
    inference(forward_demodulation,[],[f4534,f685])).

fof(f4534,plain,
    ( ! [X37,X35,X36] : k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(k5_xboole_0(X37,k1_xboole_0),k5_xboole_0(X36,X35))
    | ~ spl2_63
    | ~ spl2_98 ),
    inference(superposition,[],[f2153,f4453])).

fof(f4453,plain,
    ( ! [X12,X11] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X12,X11))
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f4452])).

fof(f2153,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2)
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f2152])).

fof(f9548,plain,
    ( spl2_103
    | ~ spl2_2
    | ~ spl2_45
    | ~ spl2_63 ),
    inference(avatar_split_clause,[],[f3446,f2152,f1072,f43,f9546])).

fof(f1072,plain,
    ( spl2_45
  <=> ! [X9,X8] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f3446,plain,
    ( ! [X26,X27,X25] : k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X25)
    | ~ spl2_2
    | ~ spl2_45
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f3418,f44])).

fof(f3418,plain,
    ( ! [X26,X27,X25] : k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X25,X26),X27),X25)
    | ~ spl2_45
    | ~ spl2_63 ),
    inference(superposition,[],[f2153,f1073])).

fof(f1073,plain,
    ( ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f9540,plain,
    ( spl2_101
    | ~ spl2_2
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f969,f875,f724,f684,f43,f9538])).

fof(f875,plain,
    ( spl2_39
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f969,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2
    | ~ spl2_2
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_39 ),
    inference(backward_demodulation,[],[f935,f959])).

fof(f959,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f937,f685])).

fof(f937,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(X4,k1_xboole_0)
    | ~ spl2_31
    | ~ spl2_39 ),
    inference(superposition,[],[f876,f725])).

fof(f876,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f875])).

fof(f935,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_2
    | ~ spl2_39 ),
    inference(superposition,[],[f876,f44])).

fof(f4454,plain,
    ( spl2_98
    | ~ spl2_42
    | ~ spl2_97 ),
    inference(avatar_split_clause,[],[f4402,f4361,f1012,f4452])).

fof(f1012,plain,
    ( spl2_42
  <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f4361,plain,
    ( spl2_97
  <=> ! [X1,X0] : k5_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).

fof(f4402,plain,
    ( ! [X12,X11] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X12,X11))
    | ~ spl2_42
    | ~ spl2_97 ),
    inference(superposition,[],[f1013,f4362])).

fof(f4362,plain,
    ( ! [X0,X1] : k5_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl2_97 ),
    inference(avatar_component_clause,[],[f4361])).

fof(f1013,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f4363,plain,
    ( spl2_97
    | ~ spl2_31
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f4254,f3306,f724,f4361])).

fof(f3306,plain,
    ( spl2_76
  <=> ! [X9,X11,X10] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f4254,plain,
    ( ! [X0,X1] : k5_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl2_31
    | ~ spl2_76 ),
    inference(superposition,[],[f3307,f725])).

fof(f3307,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f3306])).

fof(f3384,plain,
    ( spl2_95
    | ~ spl2_2
    | ~ spl2_46
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f2015,f1860,f1076,f43,f3382])).

fof(f2015,plain,
    ( ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))
    | ~ spl2_2
    | ~ spl2_46
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f1992,f44])).

fof(f1992,plain,
    ( ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12))
    | ~ spl2_46
    | ~ spl2_61 ),
    inference(superposition,[],[f1861,f1077])).

fof(f3380,plain,
    ( spl2_94
    | ~ spl2_45
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f2005,f1860,f1072,f3378])).

fof(f2005,plain,
    ( ! [X21,X22,X20] : k5_xboole_0(X21,k5_xboole_0(X20,X22)) = k5_xboole_0(k5_xboole_0(X21,X22),X20)
    | ~ spl2_45
    | ~ spl2_61 ),
    inference(superposition,[],[f1073,f1861])).

fof(f3372,plain,
    ( spl2_92
    | ~ spl2_43
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f2003,f1860,f1040,f3370])).

fof(f1040,plain,
    ( spl2_43
  <=> ! [X7,X6] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f2003,plain,
    ( ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X16)),k5_xboole_0(X15,X16)) = X14
    | ~ spl2_43
    | ~ spl2_61 ),
    inference(superposition,[],[f1041,f1861])).

fof(f1041,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f3328,plain,
    ( spl2_81
    | ~ spl2_45
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f1178,f1143,f1072,f3326])).

fof(f1178,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_45
    | ~ spl2_47 ),
    inference(superposition,[],[f1073,f1144])).

fof(f3324,plain,(
    spl2_80 ),
    inference(avatar_split_clause,[],[f36,f3322])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f28,f22,f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f3316,plain,
    ( spl2_78
    | ~ spl2_2
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f1122,f1076,f43,f3314])).

fof(f1122,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)
    | ~ spl2_2
    | ~ spl2_46 ),
    inference(superposition,[],[f44,f1077])).

fof(f3312,plain,
    ( spl2_77
    | ~ spl2_2
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f1112,f1076,f43,f3310])).

fof(f3308,plain,
    ( spl2_76
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1110,f1072,f43,f3306])).

fof(f1110,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(superposition,[],[f44,f1073])).

fof(f3304,plain,
    ( spl2_75
    | ~ spl2_3
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1100,f1072,f47,f3302])).

fof(f1100,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(k4_xboole_0(X8,X9),X8)
    | ~ spl2_3
    | ~ spl2_45 ),
    inference(superposition,[],[f1073,f48])).

fof(f3163,plain,
    ( spl2_74
    | ~ spl2_56
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f3041,f2859,f1597,f3161])).

fof(f1597,plain,
    ( spl2_56
  <=> ! [X9,X8] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f3041,plain,
    ( ! [X76,X77,X75] : k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X75,k4_xboole_0(X76,X75)))) = X75
    | ~ spl2_56
    | ~ spl2_73 ),
    inference(superposition,[],[f2860,f1598])).

fof(f1598,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f1597])).

fof(f2861,plain,
    ( spl2_73
    | ~ spl2_32
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f2667,f2601,f738,f2859])).

fof(f738,plain,
    ( spl2_32
  <=> ! [X5,X6] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f2667,plain,
    ( ! [X35,X36,X34] : k4_xboole_0(X35,X36) = k4_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35))
    | ~ spl2_32
    | ~ spl2_70 ),
    inference(superposition,[],[f739,f2602])).

fof(f739,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f738])).

fof(f2603,plain,
    ( spl2_70
    | ~ spl2_32
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f2503,f2495,f738,f2601])).

fof(f2495,plain,
    ( spl2_69
  <=> ! [X20,X22,X21] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f2503,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))
    | ~ spl2_32
    | ~ spl2_69 ),
    inference(superposition,[],[f2496,f739])).

fof(f2496,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f2497,plain,
    ( spl2_69
    | ~ spl2_1
    | ~ spl2_51
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f2449,f2344,f1205,f39,f2495])).

fof(f2344,plain,
    ( spl2_67
  <=> ! [X27,X29,X28] : k4_xboole_0(X29,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X28,X29)))) = X29 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f2449,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21
    | ~ spl2_1
    | ~ spl2_51
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f2380,f40])).

fof(f2380,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21
    | ~ spl2_51
    | ~ spl2_67 ),
    inference(superposition,[],[f2345,f1206])).

fof(f2345,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(X29,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X28,X29)))) = X29
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f2344])).

fof(f2346,plain,
    ( spl2_67
    | ~ spl2_32
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f2219,f1538,f738,f2344])).

fof(f2219,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(X29,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X28,X29)))) = X29
    | ~ spl2_32
    | ~ spl2_54 ),
    inference(superposition,[],[f739,f1539])).

fof(f2166,plain,
    ( spl2_66
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1096,f1072,f43,f2164])).

fof(f1096,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(superposition,[],[f1073,f44])).

fof(f2154,plain,
    ( spl2_63
    | ~ spl2_2
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f1079,f1068,f43,f2152])).

fof(f1068,plain,
    ( spl2_44
  <=> ! [X7,X6] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1079,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2)
    | ~ spl2_2
    | ~ spl2_44 ),
    inference(superposition,[],[f1069,f44])).

fof(f1069,plain,
    ( ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f1068])).

fof(f1862,plain,
    ( spl2_61
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1064,f1040,f43,f1860])).

fof(f1064,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f1054,f44])).

fof(f1054,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(superposition,[],[f44,f1041])).

fof(f1858,plain,
    ( spl2_60
    | ~ spl2_3
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1045,f1040,f47,f1856])).

fof(f1045,plain,
    ( ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5)) = X4
    | ~ spl2_3
    | ~ spl2_43 ),
    inference(superposition,[],[f1041,f48])).

fof(f1854,plain,
    ( spl2_59
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1043,f1040,f43,f1852])).

fof(f1043,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(superposition,[],[f1041,f44])).

fof(f1607,plain,
    ( spl2_58
    | ~ spl2_51
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f1503,f1469,f1205,f1605])).

fof(f1469,plain,
    ( spl2_53
  <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f1503,plain,
    ( ! [X26,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X26,X25),k5_xboole_0(X25,k4_xboole_0(X26,X25)))
    | ~ spl2_51
    | ~ spl2_53 ),
    inference(superposition,[],[f1206,f1470])).

fof(f1470,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X4)
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f1469])).

fof(f1599,plain,
    ( spl2_56
    | ~ spl2_6
    | ~ spl2_32
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f811,f787,f738,f59,f1597])).

fof(f811,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9
    | ~ spl2_6
    | ~ spl2_32
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f804,f739])).

fof(f804,plain,
    ( ! [X8,X9] : k4_xboole_0(X9,k4_xboole_0(X8,X9)) = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))
    | ~ spl2_6
    | ~ spl2_35 ),
    inference(superposition,[],[f60,f788])).

fof(f1544,plain,
    ( spl2_55
    | ~ spl2_6
    | ~ spl2_30
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f1525,f1469,f720,f59,f1542])).

fof(f1525,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9)))
    | ~ spl2_6
    | ~ spl2_30
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f1495,f721])).

fof(f1495,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9))) = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),k5_xboole_0(X9,k4_xboole_0(X10,X9)))
    | ~ spl2_6
    | ~ spl2_53 ),
    inference(superposition,[],[f60,f1470])).

fof(f1540,plain,(
    spl2_54 ),
    inference(avatar_split_clause,[],[f35,f1538])).

fof(f1471,plain,
    ( spl2_53
    | ~ spl2_6
    | ~ spl2_32
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1063,f1040,f1012,f738,f59,f1469])).

fof(f1063,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X4)
    | ~ spl2_6
    | ~ spl2_32
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(backward_demodulation,[],[f765,f1053])).

fof(f1053,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(superposition,[],[f1013,f1041])).

fof(f765,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X5,X4),X4),X4)
    | ~ spl2_6
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f759,f754])).

fof(f754,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)
    | ~ spl2_32 ),
    inference(superposition,[],[f739,f739])).

fof(f759,plain,
    ( ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X5,X4),X4),X4)
    | ~ spl2_6
    | ~ spl2_32 ),
    inference(superposition,[],[f60,f739])).

fof(f1207,plain,
    ( spl2_51
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_47
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f1184,f1147,f1143,f724,f51,f1205])).

fof(f1184,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_47
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1183,f725])).

fof(f1183,plain,
    ( ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))
    | ~ spl2_4
    | ~ spl2_47
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1159,f1148])).

fof(f1159,plain,
    ( ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))
    | ~ spl2_4
    | ~ spl2_47 ),
    inference(superposition,[],[f1144,f52])).

fof(f1157,plain,
    ( spl2_50
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f162,f55,f51,f47,f1155])).

fof(f55,plain,
    ( spl2_5
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f162,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f122,f152])).

fof(f152,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f56,f52])).

fof(f56,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f122,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f52])).

fof(f1153,plain,
    ( spl2_49
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f156,f55,f47,f1151])).

fof(f156,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f56])).

fof(f1149,plain,
    ( spl2_48
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f152,f55,f51,f1147])).

fof(f1145,plain,
    ( spl2_47
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f121,f51,f47,f1143])).

fof(f121,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f52])).

fof(f1078,plain,
    ( spl2_46
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1053,f1040,f1012,f1076])).

fof(f1074,plain,
    ( spl2_45
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1047,f1040,f1072])).

fof(f1047,plain,
    ( ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8
    | ~ spl2_43 ),
    inference(superposition,[],[f1041,f1041])).

fof(f1070,plain,
    ( spl2_44
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1046,f1040,f1012,f1068])).

fof(f1046,plain,
    ( ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(superposition,[],[f1041,f1013])).

fof(f1042,plain,
    ( spl2_43
    | ~ spl2_28
    | ~ spl2_36
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1031,f1012,f813,f684,f1040])).

fof(f813,plain,
    ( spl2_36
  <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f1031,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6
    | ~ spl2_28
    | ~ spl2_36
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f1018,f685])).

fof(f1018,plain,
    ( ! [X6,X7] : k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X7,k5_xboole_0(X6,X7))
    | ~ spl2_36
    | ~ spl2_42 ),
    inference(superposition,[],[f1013,f814])).

fof(f814,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f813])).

fof(f1014,plain,
    ( spl2_42
    | ~ spl2_2
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_37
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f971,f875,f842,f724,f684,f43,f1012])).

fof(f842,plain,
    ( spl2_37
  <=> ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f971,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3
    | ~ spl2_2
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_37
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f965,f959])).

fof(f965,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) = X3
    | ~ spl2_2
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_37
    | ~ spl2_39 ),
    inference(backward_demodulation,[],[f868,f959])).

fof(f868,plain,
    ( ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)))
    | ~ spl2_2
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f856,f44])).

fof(f856,plain,
    ( ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3))
    | ~ spl2_2
    | ~ spl2_37 ),
    inference(superposition,[],[f44,f843])).

fof(f843,plain,
    ( ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f842])).

fof(f995,plain,
    ( spl2_41
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f959,f875,f724,f684,f993])).

fof(f877,plain,
    ( spl2_39
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f612,f465,f214,f144,f109,f63,f43,f39,f875])).

fof(f63,plain,
    ( spl2_7
  <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f109,plain,
    ( spl2_12
  <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f144,plain,
    ( spl2_13
  <=> ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f214,plain,
    ( spl2_18
  <=> ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f465,plain,
    ( spl2_27
  <=> ! [X10] : k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f612,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f257,f584])).

fof(f584,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f145,f581])).

fof(f581,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f466,f580])).

fof(f580,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f546,f110])).

fof(f110,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f546,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f64,f40])).

fof(f64,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f466,plain,
    ( ! [X10] : k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f465])).

fof(f145,plain,
    ( ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f257,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(superposition,[],[f44,f215])).

fof(f215,plain,
    ( ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f844,plain,
    ( spl2_37
    | ~ spl2_28
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f820,f813,f684,f842])).

fof(f820,plain,
    ( ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))
    | ~ spl2_28
    | ~ spl2_36 ),
    inference(superposition,[],[f814,f685])).

fof(f815,plain,
    ( spl2_36
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f621,f465,f176,f144,f109,f63,f51,f43,f39,f813])).

fof(f176,plain,
    ( spl2_15
  <=> ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f621,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f186,f584])).

fof(f186,plain,
    ( ! [X0,X1] : k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f185,f110])).

fof(f185,plain,
    ( ! [X0,X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f179,f117])).

fof(f117,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f52,f40])).

fof(f179,plain,
    ( ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(superposition,[],[f177,f44])).

fof(f177,plain,
    ( ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f789,plain,
    ( spl2_35
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f754,f738,f787])).

fof(f749,plain,(
    ~ spl2_34 ),
    inference(avatar_split_clause,[],[f30,f746])).

fof(f30,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f21,f22])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f740,plain,
    ( spl2_32
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f573,f63,f47,f738])).

fof(f573,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f64,f48])).

fof(f726,plain,
    ( spl2_31
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f609,f465,f214,f144,f109,f63,f39,f724])).

fof(f609,plain,
    ( ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f215,f584])).

fof(f722,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f581,f465,f109,f63,f39,f720])).

fof(f686,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f583,f465,f109,f74,f63,f39,f684])).

fof(f74,plain,
    ( spl2_8
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f583,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f75,f581])).

fof(f75,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f467,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f354,f333,f300,f47,f465])).

fof(f300,plain,
    ( spl2_20
  <=> ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f333,plain,
    ( spl2_22
  <=> ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f354,plain,
    ( ! [X10] : k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10))
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f352,f301])).

fof(f301,plain,
    ( ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f300])).

fof(f352,plain,
    ( ! [X10] : k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X10,X10)))
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(superposition,[],[f48,f334])).

fof(f334,plain,
    ( ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f136,f109,f51,f39,f333])).

fof(f136,plain,
    ( ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f124,f40])).

fof(f124,plain,
    ( ! [X5] : k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f110,f52])).

fof(f302,plain,
    ( spl2_20
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f286,f263,f55,f300])).

fof(f263,plain,
    ( spl2_19
  <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f286,plain,
    ( ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(superposition,[],[f56,f264])).

fof(f264,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f117,f51,f39,f263])).

fof(f216,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f204,f164,f144,f47,f214])).

fof(f164,plain,
    ( spl2_14
  <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f204,plain,
    ( ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f198,f195])).

fof(f195,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f165,f145])).

fof(f165,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f198,plain,
    ( ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,X5)))
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(superposition,[],[f48,f145])).

fof(f178,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f169,f164,f47,f176])).

fof(f169,plain,
    ( ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(superposition,[],[f48,f165])).

fof(f166,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f147,f55,f39,f164])).

fof(f147,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f56,f40])).

fof(f146,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f133,f109,f51,f39,f144])).

fof(f133,plain,
    ( ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f118,f40])).

fof(f118,plain,
    ( ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f52,f110])).

fof(f111,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f102,f98,f47,f109])).

fof(f98,plain,
    ( spl2_11
  <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f102,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(superposition,[],[f99,f48])).

fof(f99,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f93,f88,f47,f98])).

fof(f88,plain,
    ( spl2_10
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f89,f48])).

fof(f89,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f86,f82,f43,f88])).

fof(f82,plain,
    ( spl2_9
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f86,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f44,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f77,f74,f39,f82])).

fof(f77,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f75,f40])).

fof(f76,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f69,f47,f39,f74])).

fof(f69,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f48,f40])).

fof(f65,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f37,f63])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f32,f35])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f21,f22])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f61,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f57,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f31,f51])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f22,f22])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f47])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f43])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (1163)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (1169)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (1161)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (1159)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (1154)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (1157)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (1162)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (1168)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (1158)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (1155)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (1164)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (1166)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (1173)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (1166)Refutation not found, incomplete strategy% (1166)------------------------------
% 0.20/0.49  % (1166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1166)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1166)Memory used [KB]: 10490
% 0.20/0.49  % (1166)Time elapsed: 0.085 s
% 0.20/0.49  % (1166)------------------------------
% 0.20/0.49  % (1166)------------------------------
% 0.20/0.49  % (1167)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (1156)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (1165)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (1171)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (1170)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.20/1.05  % (1158)Time limit reached!
% 5.20/1.05  % (1158)------------------------------
% 5.20/1.05  % (1158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.20/1.05  % (1158)Termination reason: Time limit
% 5.20/1.05  % (1158)Termination phase: Saturation
% 5.20/1.05  
% 5.20/1.05  % (1158)Memory used [KB]: 15607
% 5.20/1.05  % (1158)Time elapsed: 0.600 s
% 5.20/1.05  % (1158)------------------------------
% 5.20/1.05  % (1158)------------------------------
% 12.44/1.92  % (1159)Time limit reached!
% 12.44/1.92  % (1159)------------------------------
% 12.44/1.92  % (1159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.44/1.92  % (1159)Termination reason: Time limit
% 12.44/1.92  % (1159)Termination phase: Saturation
% 12.44/1.92  
% 12.44/1.92  % (1159)Memory used [KB]: 51683
% 12.44/1.92  % (1159)Time elapsed: 1.500 s
% 12.44/1.92  % (1159)------------------------------
% 12.44/1.92  % (1159)------------------------------
% 13.01/2.01  % (1161)Time limit reached!
% 13.01/2.01  % (1161)------------------------------
% 13.01/2.01  % (1161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.01/2.01  % (1161)Termination reason: Time limit
% 13.01/2.01  
% 13.01/2.01  % (1161)Memory used [KB]: 36587
% 13.01/2.01  % (1161)Time elapsed: 1.549 s
% 13.01/2.01  % (1161)------------------------------
% 13.01/2.01  % (1161)------------------------------
% 14.85/2.22  % (1156)Time limit reached!
% 14.85/2.22  % (1156)------------------------------
% 14.85/2.22  % (1156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.85/2.22  % (1156)Termination reason: Time limit
% 14.85/2.22  % (1156)Termination phase: Saturation
% 14.85/2.22  
% 14.85/2.22  % (1156)Memory used [KB]: 41321
% 14.85/2.22  % (1156)Time elapsed: 1.800 s
% 14.85/2.22  % (1156)------------------------------
% 14.85/2.22  % (1156)------------------------------
% 17.77/2.64  % (1167)Time limit reached!
% 17.77/2.64  % (1167)------------------------------
% 17.77/2.64  % (1167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.77/2.64  % (1167)Termination reason: Time limit
% 17.77/2.64  
% 17.77/2.64  % (1167)Memory used [KB]: 64732
% 17.77/2.64  % (1167)Time elapsed: 2.234 s
% 17.77/2.64  % (1167)------------------------------
% 17.77/2.64  % (1167)------------------------------
% 25.79/3.62  % (1162)Refutation found. Thanks to Tanya!
% 25.79/3.62  % SZS status Theorem for theBenchmark
% 25.79/3.62  % SZS output start Proof for theBenchmark
% 25.79/3.62  fof(f70049,plain,(
% 25.79/3.62    $false),
% 25.79/3.62    inference(avatar_sat_refutation,[],[f41,f45,f49,f53,f57,f61,f65,f76,f85,f90,f100,f111,f146,f166,f178,f216,f265,f302,f335,f467,f686,f722,f726,f740,f749,f789,f815,f844,f877,f995,f1014,f1042,f1070,f1074,f1078,f1145,f1149,f1153,f1157,f1207,f1471,f1540,f1544,f1599,f1607,f1854,f1858,f1862,f2154,f2166,f2346,f2497,f2603,f2861,f3163,f3304,f3308,f3312,f3316,f3324,f3328,f3372,f3380,f3384,f4363,f4454,f9540,f9548,f16643,f18281,f18293,f19574,f20055,f21370,f22080,f22092,f22104,f25148,f25156,f25160,f32394,f36109,f36129,f37581,f39774,f49613,f50355,f54846,f58366,f58374,f61961,f66385,f67254,f68399,f69393,f69978])).
% 25.79/3.62  fof(f69978,plain,(
% 25.79/3.62    ~spl2_6 | spl2_34 | ~spl2_41 | ~spl2_49 | ~spl2_61 | ~spl2_77 | ~spl2_115 | ~spl2_123 | ~spl2_125 | ~spl2_138 | ~spl2_207 | ~spl2_215),
% 25.79/3.62    inference(avatar_contradiction_clause,[],[f69977])).
% 25.79/3.62  fof(f69977,plain,(
% 25.79/3.62    $false | (~spl2_6 | spl2_34 | ~spl2_41 | ~spl2_49 | ~spl2_61 | ~spl2_77 | ~spl2_115 | ~spl2_123 | ~spl2_125 | ~spl2_138 | ~spl2_207 | ~spl2_215)),
% 25.79/3.62    inference(subsumption_resolution,[],[f748,f69976])).
% 25.79/3.62  fof(f69976,plain,(
% 25.79/3.62    ( ! [X134,X133] : (k5_xboole_0(X133,X134) = k4_xboole_0(k5_xboole_0(X133,k4_xboole_0(X134,X133)),k4_xboole_0(X133,k4_xboole_0(X133,X134)))) ) | (~spl2_6 | ~spl2_41 | ~spl2_49 | ~spl2_61 | ~spl2_77 | ~spl2_115 | ~spl2_123 | ~spl2_125 | ~spl2_138 | ~spl2_207 | ~spl2_215)),
% 25.79/3.62    inference(forward_demodulation,[],[f69548,f69718])).
% 25.79/3.62  fof(f69718,plain,(
% 25.79/3.62    ( ! [X23,X22] : (k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k4_xboole_0(X22,k5_xboole_0(X22,X23))) ) | (~spl2_6 | ~spl2_41 | ~spl2_49 | ~spl2_61 | ~spl2_77 | ~spl2_115 | ~spl2_123 | ~spl2_138 | ~spl2_207 | ~spl2_215)),
% 25.79/3.62    inference(forward_demodulation,[],[f69501,f62729])).
% 25.79/3.62  fof(f62729,plain,(
% 25.79/3.62    ( ! [X177,X176] : (k4_xboole_0(X176,k4_xboole_0(X176,X177)) = k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177))) ) | (~spl2_41 | ~spl2_49 | ~spl2_61 | ~spl2_77 | ~spl2_115 | ~spl2_123 | ~spl2_138 | ~spl2_207)),
% 25.79/3.62    inference(forward_demodulation,[],[f62728,f1152])).
% 25.79/3.62  fof(f1152,plain,(
% 25.79/3.62    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl2_49),
% 25.79/3.62    inference(avatar_component_clause,[],[f1151])).
% 25.79/3.62  fof(f1151,plain,(
% 25.79/3.62    spl2_49 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 25.79/3.62  fof(f62728,plain,(
% 25.79/3.62    ( ! [X177,X176] : (k5_xboole_0(X176,k4_xboole_0(X176,X177)) = k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177))) ) | (~spl2_41 | ~spl2_61 | ~spl2_77 | ~spl2_115 | ~spl2_123 | ~spl2_138 | ~spl2_207)),
% 25.79/3.62    inference(forward_demodulation,[],[f62727,f994])).
% 25.79/3.62  fof(f994,plain,(
% 25.79/3.62    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = X4) ) | ~spl2_41),
% 25.79/3.62    inference(avatar_component_clause,[],[f993])).
% 25.79/3.62  fof(f993,plain,(
% 25.79/3.62    spl2_41 <=> ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 25.79/3.62  fof(f62727,plain,(
% 25.79/3.62    ( ! [X177,X176] : (k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X176,k4_xboole_0(X176,X177)))) ) | (~spl2_61 | ~spl2_77 | ~spl2_115 | ~spl2_123 | ~spl2_138 | ~spl2_207)),
% 25.79/3.62    inference(forward_demodulation,[],[f62726,f21007])).
% 25.79/3.62  fof(f21007,plain,(
% 25.79/3.62    ( ! [X39,X38,X40] : (k5_xboole_0(X40,k4_xboole_0(X39,X38)) = k5_xboole_0(X38,k5_xboole_0(X40,k5_xboole_0(X39,k4_xboole_0(X38,X39))))) ) | (~spl2_61 | ~spl2_115 | ~spl2_123)),
% 25.79/3.62    inference(forward_demodulation,[],[f20683,f16642])).
% 25.79/3.62  fof(f16642,plain,(
% 25.79/3.62    ( ! [X37,X35,X36] : (k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(X37,k5_xboole_0(X36,X35))) ) | ~spl2_115),
% 25.79/3.62    inference(avatar_component_clause,[],[f16641])).
% 25.79/3.62  fof(f16641,plain,(
% 25.79/3.62    spl2_115 <=> ! [X36,X35,X37] : k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(X37,k5_xboole_0(X36,X35))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).
% 25.79/3.62  fof(f20683,plain,(
% 25.79/3.62    ( ! [X39,X38,X40] : (k5_xboole_0(X40,k4_xboole_0(X39,X38)) = k5_xboole_0(X38,k5_xboole_0(X40,k5_xboole_0(k4_xboole_0(X38,X39),X39)))) ) | (~spl2_61 | ~spl2_123)),
% 25.79/3.62    inference(superposition,[],[f1861,f20054])).
% 25.79/3.62  fof(f20054,plain,(
% 25.79/3.62    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k4_xboole_0(X2,X3),X3)) ) | ~spl2_123),
% 25.79/3.62    inference(avatar_component_clause,[],[f20053])).
% 25.79/3.62  fof(f20053,plain,(
% 25.79/3.62    spl2_123 <=> ! [X3,X2] : k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k4_xboole_0(X2,X3),X3)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).
% 25.79/3.62  fof(f1861,plain,(
% 25.79/3.62    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) ) | ~spl2_61),
% 25.79/3.62    inference(avatar_component_clause,[],[f1860])).
% 25.79/3.62  fof(f1860,plain,(
% 25.79/3.62    spl2_61 <=> ! [X3,X5,X4] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 25.79/3.62  fof(f62726,plain,(
% 25.79/3.62    ( ! [X177,X176] : (k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X177,k5_xboole_0(X176,k5_xboole_0(X176,k4_xboole_0(X177,X176)))))) ) | (~spl2_77 | ~spl2_115 | ~spl2_138 | ~spl2_207)),
% 25.79/3.62    inference(forward_demodulation,[],[f62725,f16642])).
% 25.79/3.62  fof(f62725,plain,(
% 25.79/3.62    ( ! [X177,X176] : (k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X177,k5_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),X176)))) ) | (~spl2_77 | ~spl2_138 | ~spl2_207)),
% 25.79/3.62    inference(forward_demodulation,[],[f62230,f3311])).
% 25.79/3.62  fof(f3311,plain,(
% 25.79/3.62    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1))) ) | ~spl2_77),
% 25.79/3.62    inference(avatar_component_clause,[],[f3310])).
% 25.79/3.62  fof(f3310,plain,(
% 25.79/3.62    spl2_77 <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 25.79/3.62  fof(f62230,plain,(
% 25.79/3.62    ( ! [X177,X176] : (k4_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X176,k4_xboole_0(X177,X176)),k5_xboole_0(X176,X177)))) ) | (~spl2_138 | ~spl2_207)),
% 25.79/3.62    inference(superposition,[],[f25155,f61960])).
% 25.79/3.62  fof(f61960,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k4_xboole_0(X214,X213)))) ) | ~spl2_207),
% 25.79/3.62    inference(avatar_component_clause,[],[f61959])).
% 25.79/3.62  fof(f61959,plain,(
% 25.79/3.62    spl2_207 <=> ! [X214,X213] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k4_xboole_0(X214,X213)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_207])])).
% 25.79/3.62  fof(f25155,plain,(
% 25.79/3.62    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X7,X8))) ) | ~spl2_138),
% 25.79/3.62    inference(avatar_component_clause,[],[f25154])).
% 25.79/3.62  fof(f25154,plain,(
% 25.79/3.62    spl2_138 <=> ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X7,X8))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).
% 25.79/3.62  fof(f69501,plain,(
% 25.79/3.62    ( ! [X23,X22] : (k4_xboole_0(X22,k5_xboole_0(X22,X23)) = k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X23,X22)),k5_xboole_0(X22,X23))) ) | (~spl2_6 | ~spl2_215)),
% 25.79/3.62    inference(superposition,[],[f60,f69392])).
% 25.79/3.62  fof(f69392,plain,(
% 25.79/3.62    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) ) | ~spl2_215),
% 25.79/3.62    inference(avatar_component_clause,[],[f69391])).
% 25.79/3.62  fof(f69391,plain,(
% 25.79/3.62    spl2_215 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_215])])).
% 25.79/3.62  fof(f60,plain,(
% 25.79/3.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) ) | ~spl2_6),
% 25.79/3.62    inference(avatar_component_clause,[],[f59])).
% 25.79/3.62  fof(f59,plain,(
% 25.79/3.62    spl2_6 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 25.79/3.62  fof(f69548,plain,(
% 25.79/3.62    ( ! [X134,X133] : (k5_xboole_0(X133,X134) = k4_xboole_0(k5_xboole_0(X133,k4_xboole_0(X134,X133)),k4_xboole_0(X133,k5_xboole_0(X133,X134)))) ) | (~spl2_125 | ~spl2_215)),
% 25.79/3.62    inference(superposition,[],[f21369,f69392])).
% 25.79/3.62  fof(f21369,plain,(
% 25.79/3.62    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X3) ) | ~spl2_125),
% 25.79/3.62    inference(avatar_component_clause,[],[f21368])).
% 25.79/3.62  fof(f21368,plain,(
% 25.79/3.62    spl2_125 <=> ! [X3,X2] : k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X3),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).
% 25.79/3.62  fof(f748,plain,(
% 25.79/3.62    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_34),
% 25.79/3.62    inference(avatar_component_clause,[],[f746])).
% 25.79/3.62  fof(f746,plain,(
% 25.79/3.62    spl2_34 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 25.79/3.62  fof(f69393,plain,(
% 25.79/3.62    spl2_215 | ~spl2_46 | ~spl2_213),
% 25.79/3.62    inference(avatar_split_clause,[],[f68401,f68397,f1076,f69391])).
% 25.79/3.62  fof(f1076,plain,(
% 25.79/3.62    spl2_46 <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 25.79/3.62  fof(f68397,plain,(
% 25.79/3.62    spl2_213 <=> ! [X73,X74] : k4_xboole_0(X73,X74) = k4_xboole_0(k5_xboole_0(X73,X74),X74)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).
% 25.79/3.62  fof(f68401,plain,(
% 25.79/3.62    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) ) | (~spl2_46 | ~spl2_213)),
% 25.79/3.62    inference(superposition,[],[f68398,f1077])).
% 25.79/3.62  fof(f1077,plain,(
% 25.79/3.62    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | ~spl2_46),
% 25.79/3.62    inference(avatar_component_clause,[],[f1076])).
% 25.79/3.62  fof(f68398,plain,(
% 25.79/3.62    ( ! [X74,X73] : (k4_xboole_0(X73,X74) = k4_xboole_0(k5_xboole_0(X73,X74),X74)) ) | ~spl2_213),
% 25.79/3.62    inference(avatar_component_clause,[],[f68397])).
% 25.79/3.62  fof(f68399,plain,(
% 25.79/3.62    spl2_213 | ~spl2_1 | ~spl2_4 | ~spl2_35 | ~spl2_54 | ~spl2_166 | ~spl2_212),
% 25.79/3.62    inference(avatar_split_clause,[],[f67943,f67252,f37579,f1538,f787,f51,f39,f68397])).
% 25.79/3.62  fof(f39,plain,(
% 25.79/3.62    spl2_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 25.79/3.62  fof(f51,plain,(
% 25.79/3.62    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 25.79/3.62  fof(f787,plain,(
% 25.79/3.62    spl2_35 <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 25.79/3.62  fof(f1538,plain,(
% 25.79/3.62    spl2_54 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 25.79/3.62  fof(f37579,plain,(
% 25.79/3.62    spl2_166 <=> ! [X3,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_166])])).
% 25.79/3.62  fof(f67252,plain,(
% 25.79/3.62    spl2_212 <=> ! [X223,X222] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X222,X223),X223),k4_xboole_0(X222,X223))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_212])])).
% 25.79/3.62  fof(f67943,plain,(
% 25.79/3.62    ( ! [X74,X73] : (k4_xboole_0(X73,X74) = k4_xboole_0(k5_xboole_0(X73,X74),X74)) ) | (~spl2_1 | ~spl2_4 | ~spl2_35 | ~spl2_54 | ~spl2_166 | ~spl2_212)),
% 25.79/3.62    inference(forward_demodulation,[],[f67942,f788])).
% 25.79/3.62  fof(f788,plain,(
% 25.79/3.62    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)) ) | ~spl2_35),
% 25.79/3.62    inference(avatar_component_clause,[],[f787])).
% 25.79/3.62  fof(f67942,plain,(
% 25.79/3.62    ( ! [X74,X73] : (k4_xboole_0(k5_xboole_0(X73,X74),X74) = k4_xboole_0(k4_xboole_0(X73,X74),X74)) ) | (~spl2_1 | ~spl2_4 | ~spl2_54 | ~spl2_166 | ~spl2_212)),
% 25.79/3.62    inference(forward_demodulation,[],[f67941,f37938])).
% 25.79/3.62  fof(f37938,plain,(
% 25.79/3.62    ( ! [X70,X68,X69] : (k4_xboole_0(k4_xboole_0(X68,X69),X70) = k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k5_xboole_0(X68,X69),X70)))) ) | (~spl2_1 | ~spl2_54 | ~spl2_166)),
% 25.79/3.62    inference(forward_demodulation,[],[f37770,f40])).
% 25.79/3.62  fof(f40,plain,(
% 25.79/3.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 25.79/3.62    inference(avatar_component_clause,[],[f39])).
% 25.79/3.62  fof(f37770,plain,(
% 25.79/3.62    ( ! [X70,X68,X69] : (k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(k5_xboole_0(X68,X69),X70))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X68,X69),k1_xboole_0),X70)) ) | (~spl2_54 | ~spl2_166)),
% 25.79/3.62    inference(superposition,[],[f1539,f37580])).
% 25.79/3.62  fof(f37580,plain,(
% 25.79/3.62    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4))) ) | ~spl2_166),
% 25.79/3.62    inference(avatar_component_clause,[],[f37579])).
% 25.79/3.62  fof(f1539,plain,(
% 25.79/3.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl2_54),
% 25.79/3.62    inference(avatar_component_clause,[],[f1538])).
% 25.79/3.62  fof(f67941,plain,(
% 25.79/3.62    ( ! [X74,X73] : (k4_xboole_0(k5_xboole_0(X73,X74),X74) = k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k5_xboole_0(X73,X74),X74)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_212)),
% 25.79/3.62    inference(forward_demodulation,[],[f67486,f40])).
% 25.79/3.62  fof(f67486,plain,(
% 25.79/3.62    ( ! [X74,X73] : (k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k4_xboole_0(X73,X74),k4_xboole_0(k5_xboole_0(X73,X74),X74))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X73,X74),X74),k1_xboole_0)) ) | (~spl2_4 | ~spl2_212)),
% 25.79/3.62    inference(superposition,[],[f52,f67253])).
% 25.79/3.62  fof(f67253,plain,(
% 25.79/3.62    ( ! [X222,X223] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X222,X223),X223),k4_xboole_0(X222,X223))) ) | ~spl2_212),
% 25.79/3.62    inference(avatar_component_clause,[],[f67252])).
% 25.79/3.62  fof(f52,plain,(
% 25.79/3.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_4),
% 25.79/3.62    inference(avatar_component_clause,[],[f51])).
% 25.79/3.62  fof(f67254,plain,(
% 25.79/3.62    spl2_212 | ~spl2_171 | ~spl2_211),
% 25.79/3.62    inference(avatar_split_clause,[],[f66658,f66383,f39772,f67252])).
% 25.79/3.62  fof(f39772,plain,(
% 25.79/3.62    spl2_171 <=> ! [X214,X213] : k4_xboole_0(X213,X214) = k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).
% 25.79/3.62  fof(f66383,plain,(
% 25.79/3.62    spl2_211 <=> ! [X106,X105,X107] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X107,X105),k4_xboole_0(X107,k4_xboole_0(X105,X106)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_211])])).
% 25.79/3.62  fof(f66658,plain,(
% 25.79/3.62    ( ! [X222,X223] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X222,X223),X223),k4_xboole_0(X222,X223))) ) | (~spl2_171 | ~spl2_211)),
% 25.79/3.62    inference(superposition,[],[f66384,f39773])).
% 25.79/3.62  fof(f39773,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k4_xboole_0(X213,X214) = k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213))) ) | ~spl2_171),
% 25.79/3.62    inference(avatar_component_clause,[],[f39772])).
% 25.79/3.62  fof(f66384,plain,(
% 25.79/3.62    ( ! [X107,X105,X106] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X107,X105),k4_xboole_0(X107,k4_xboole_0(X105,X106)))) ) | ~spl2_211),
% 25.79/3.62    inference(avatar_component_clause,[],[f66383])).
% 25.79/3.62  fof(f66385,plain,(
% 25.79/3.62    spl2_211 | ~spl2_73 | ~spl2_205),
% 25.79/3.62    inference(avatar_split_clause,[],[f65834,f58372,f2859,f66383])).
% 25.79/3.62  fof(f2859,plain,(
% 25.79/3.62    spl2_73 <=> ! [X34,X36,X35] : k4_xboole_0(X35,X36) = k4_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 25.79/3.62  fof(f58372,plain,(
% 25.79/3.62    spl2_205 <=> ! [X124,X126,X125] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(X124,k4_xboole_0(X126,k4_xboole_0(X124,X125))))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).
% 25.79/3.62  fof(f65834,plain,(
% 25.79/3.62    ( ! [X107,X105,X106] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X107,X105),k4_xboole_0(X107,k4_xboole_0(X105,X106)))) ) | (~spl2_73 | ~spl2_205)),
% 25.79/3.62    inference(superposition,[],[f58373,f2860])).
% 25.79/3.62  fof(f2860,plain,(
% 25.79/3.62    ( ! [X35,X36,X34] : (k4_xboole_0(X35,X36) = k4_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35))) ) | ~spl2_73),
% 25.79/3.62    inference(avatar_component_clause,[],[f2859])).
% 25.79/3.62  fof(f58373,plain,(
% 25.79/3.62    ( ! [X125,X126,X124] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(X124,k4_xboole_0(X126,k4_xboole_0(X124,X125))))) ) | ~spl2_205),
% 25.79/3.62    inference(avatar_component_clause,[],[f58372])).
% 25.79/3.62  fof(f61961,plain,(
% 25.79/3.62    spl2_207 | ~spl2_2 | ~spl2_59 | ~spl2_60 | ~spl2_61 | ~spl2_77 | ~spl2_78 | ~spl2_94 | ~spl2_115 | ~spl2_123 | ~spl2_171 | ~spl2_203),
% 25.79/3.62    inference(avatar_split_clause,[],[f61750,f58364,f39772,f20053,f16641,f3378,f3314,f3310,f1860,f1856,f1852,f43,f61959])).
% 25.79/3.62  fof(f43,plain,(
% 25.79/3.62    spl2_2 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 25.79/3.62  fof(f1852,plain,(
% 25.79/3.62    spl2_59 <=> ! [X1,X0,X2] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 25.79/3.62  fof(f1856,plain,(
% 25.79/3.62    spl2_60 <=> ! [X5,X4] : k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5)) = X4),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 25.79/3.62  fof(f3314,plain,(
% 25.79/3.62    spl2_78 <=> ! [X1,X3,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 25.79/3.62  fof(f3378,plain,(
% 25.79/3.62    spl2_94 <=> ! [X20,X22,X21] : k5_xboole_0(X21,k5_xboole_0(X20,X22)) = k5_xboole_0(k5_xboole_0(X21,X22),X20)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).
% 25.79/3.62  fof(f58364,plain,(
% 25.79/3.62    spl2_203 <=> ! [X157,X156,X158] : k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(X156,k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157)))))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).
% 25.79/3.62  fof(f61750,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k4_xboole_0(X214,X213)))) ) | (~spl2_2 | ~spl2_59 | ~spl2_60 | ~spl2_61 | ~spl2_77 | ~spl2_78 | ~spl2_94 | ~spl2_115 | ~spl2_123 | ~spl2_171 | ~spl2_203)),
% 25.79/3.62    inference(forward_demodulation,[],[f61749,f21007])).
% 25.79/3.62  fof(f61749,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k5_xboole_0(X213,k5_xboole_0(X214,k4_xboole_0(X213,X214)))))) ) | (~spl2_2 | ~spl2_59 | ~spl2_60 | ~spl2_61 | ~spl2_77 | ~spl2_78 | ~spl2_94 | ~spl2_171 | ~spl2_203)),
% 25.79/3.62    inference(forward_demodulation,[],[f61748,f8846])).
% 25.79/3.62  fof(f8846,plain,(
% 25.79/3.62    ( ! [X92,X90,X93,X91] : (k5_xboole_0(X91,k5_xboole_0(X90,k5_xboole_0(X93,X92))) = k5_xboole_0(X91,k5_xboole_0(X90,k5_xboole_0(X92,X93)))) ) | (~spl2_2 | ~spl2_78 | ~spl2_94)),
% 25.79/3.62    inference(forward_demodulation,[],[f8845,f44])).
% 25.79/3.62  fof(f44,plain,(
% 25.79/3.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_2),
% 25.79/3.62    inference(avatar_component_clause,[],[f43])).
% 25.79/3.62  fof(f8845,plain,(
% 25.79/3.62    ( ! [X92,X90,X93,X91] : (k5_xboole_0(X91,k5_xboole_0(k5_xboole_0(X90,X92),X93)) = k5_xboole_0(X91,k5_xboole_0(X90,k5_xboole_0(X93,X92)))) ) | (~spl2_2 | ~spl2_78 | ~spl2_94)),
% 25.79/3.62    inference(forward_demodulation,[],[f8844,f3315])).
% 25.79/3.62  fof(f3315,plain,(
% 25.79/3.62    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)) ) | ~spl2_78),
% 25.79/3.62    inference(avatar_component_clause,[],[f3314])).
% 25.79/3.62  fof(f8844,plain,(
% 25.79/3.62    ( ! [X92,X90,X93,X91] : (k5_xboole_0(X91,k5_xboole_0(k5_xboole_0(X90,X92),X93)) = k5_xboole_0(k5_xboole_0(X90,X91),k5_xboole_0(X93,X92))) ) | (~spl2_2 | ~spl2_78 | ~spl2_94)),
% 25.79/3.62    inference(forward_demodulation,[],[f8693,f44])).
% 25.79/3.62  fof(f8693,plain,(
% 25.79/3.62    ( ! [X92,X90,X93,X91] : (k5_xboole_0(k5_xboole_0(X90,X91),k5_xboole_0(X93,X92)) = k5_xboole_0(k5_xboole_0(X91,k5_xboole_0(X90,X92)),X93)) ) | (~spl2_78 | ~spl2_94)),
% 25.79/3.62    inference(superposition,[],[f3379,f3315])).
% 25.79/3.62  fof(f3379,plain,(
% 25.79/3.62    ( ! [X21,X22,X20] : (k5_xboole_0(X21,k5_xboole_0(X20,X22)) = k5_xboole_0(k5_xboole_0(X21,X22),X20)) ) | ~spl2_94),
% 25.79/3.62    inference(avatar_component_clause,[],[f3378])).
% 25.79/3.62  fof(f61748,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k5_xboole_0(X213,k5_xboole_0(k4_xboole_0(X213,X214),X214))))) ) | (~spl2_59 | ~spl2_60 | ~spl2_61 | ~spl2_77 | ~spl2_171 | ~spl2_203)),
% 25.79/3.62    inference(forward_demodulation,[],[f61747,f1980])).
% 25.79/3.62  fof(f1980,plain,(
% 25.79/3.62    ( ! [X30,X33,X31,X32] : (k5_xboole_0(X33,k5_xboole_0(X31,k5_xboole_0(X30,X32))) = k5_xboole_0(X30,k5_xboole_0(X33,k5_xboole_0(X31,X32)))) ) | ~spl2_61),
% 25.79/3.62    inference(superposition,[],[f1861,f1861])).
% 25.79/3.62  fof(f61747,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(X213,k5_xboole_0(k4_xboole_0(X213,X214),k5_xboole_0(X213,X214))))) ) | (~spl2_59 | ~spl2_60 | ~spl2_77 | ~spl2_171 | ~spl2_203)),
% 25.79/3.62    inference(forward_demodulation,[],[f61746,f3311])).
% 25.79/3.62  fof(f61746,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(k4_xboole_0(X213,X214),k5_xboole_0(k5_xboole_0(X213,X214),X213)))) ) | (~spl2_59 | ~spl2_60 | ~spl2_171 | ~spl2_203)),
% 25.79/3.62    inference(forward_demodulation,[],[f61449,f1951])).
% 25.79/3.62  fof(f1951,plain,(
% 25.79/3.62    ( ! [X17,X15,X16] : (k5_xboole_0(X17,k4_xboole_0(X15,k4_xboole_0(X15,X16))) = k5_xboole_0(k4_xboole_0(X15,X16),k5_xboole_0(X17,X15))) ) | (~spl2_59 | ~spl2_60)),
% 25.79/3.62    inference(superposition,[],[f1853,f1857])).
% 25.79/3.62  fof(f1857,plain,(
% 25.79/3.62    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5)) = X4) ) | ~spl2_60),
% 25.79/3.62    inference(avatar_component_clause,[],[f1856])).
% 25.79/3.62  fof(f1853,plain,(
% 25.79/3.62    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | ~spl2_59),
% 25.79/3.62    inference(avatar_component_clause,[],[f1852])).
% 25.79/3.62  fof(f61449,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X213,X214),k5_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X213,k4_xboole_0(X213,X214))))) ) | (~spl2_171 | ~spl2_203)),
% 25.79/3.62    inference(superposition,[],[f58365,f39773])).
% 25.79/3.62  fof(f58365,plain,(
% 25.79/3.62    ( ! [X158,X156,X157] : (k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(X156,k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157)))))) ) | ~spl2_203),
% 25.79/3.62    inference(avatar_component_clause,[],[f58364])).
% 25.79/3.62  fof(f58374,plain,(
% 25.79/3.62    spl2_205 | ~spl2_28 | ~spl2_51 | ~spl2_198),
% 25.79/3.62    inference(avatar_split_clause,[],[f55240,f54844,f1205,f684,f58372])).
% 25.79/3.62  fof(f684,plain,(
% 25.79/3.62    spl2_28 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 25.79/3.62  fof(f1205,plain,(
% 25.79/3.62    spl2_51 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 25.79/3.62  fof(f54844,plain,(
% 25.79/3.62    spl2_198 <=> ! [X27,X29,X28] : k1_xboole_0 = k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X29,X28)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_198])])).
% 25.79/3.62  fof(f55240,plain,(
% 25.79/3.62    ( ! [X125,X126,X124] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(X124,k4_xboole_0(X126,k4_xboole_0(X124,X125))))) ) | (~spl2_28 | ~spl2_51 | ~spl2_198)),
% 25.79/3.62    inference(forward_demodulation,[],[f54881,f685])).
% 25.79/3.62  fof(f685,plain,(
% 25.79/3.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_28),
% 25.79/3.62    inference(avatar_component_clause,[],[f684])).
% 25.79/3.62  fof(f54881,plain,(
% 25.79/3.62    ( ! [X125,X126,X124] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X124,X125),k4_xboole_0(k5_xboole_0(X124,k1_xboole_0),k4_xboole_0(X126,k4_xboole_0(X124,X125))))) ) | (~spl2_51 | ~spl2_198)),
% 25.79/3.62    inference(superposition,[],[f54845,f1206])).
% 25.79/3.62  fof(f1206,plain,(
% 25.79/3.62    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) ) | ~spl2_51),
% 25.79/3.62    inference(avatar_component_clause,[],[f1205])).
% 25.79/3.62  fof(f54845,plain,(
% 25.79/3.62    ( ! [X28,X29,X27] : (k1_xboole_0 = k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X29,X28)))) ) | ~spl2_198),
% 25.79/3.62    inference(avatar_component_clause,[],[f54844])).
% 25.79/3.62  fof(f58366,plain,(
% 25.79/3.62    spl2_203 | ~spl2_46 | ~spl2_58 | ~spl2_188),
% 25.79/3.62    inference(avatar_split_clause,[],[f50807,f50353,f1605,f1076,f58364])).
% 25.79/3.62  fof(f1605,plain,(
% 25.79/3.62    spl2_58 <=> ! [X25,X26] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X26,X25),k5_xboole_0(X25,k4_xboole_0(X26,X25)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 25.79/3.62  fof(f50353,plain,(
% 25.79/3.62    spl2_188 <=> ! [X18,X17,X19] : k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18)))) = X17),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).
% 25.79/3.62  fof(f50807,plain,(
% 25.79/3.62    ( ! [X158,X156,X157] : (k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(X156,k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157)))))) ) | (~spl2_46 | ~spl2_58 | ~spl2_188)),
% 25.79/3.62    inference(forward_demodulation,[],[f50549,f1077])).
% 25.79/3.62  fof(f50549,plain,(
% 25.79/3.62    ( ! [X158,X156,X157] : (k1_xboole_0 = k4_xboole_0(X156,k5_xboole_0(k4_xboole_0(X157,k4_xboole_0(X156,k4_xboole_0(X158,X157))),X156))) ) | (~spl2_58 | ~spl2_188)),
% 25.79/3.62    inference(superposition,[],[f1606,f50354])).
% 25.79/3.62  fof(f50354,plain,(
% 25.79/3.62    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18)))) = X17) ) | ~spl2_188),
% 25.79/3.62    inference(avatar_component_clause,[],[f50353])).
% 25.79/3.62  fof(f1606,plain,(
% 25.79/3.62    ( ! [X26,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X26,X25),k5_xboole_0(X25,k4_xboole_0(X26,X25)))) ) | ~spl2_58),
% 25.79/3.62    inference(avatar_component_clause,[],[f1605])).
% 25.79/3.62  fof(f54846,plain,(
% 25.79/3.62    spl2_198 | ~spl2_164 | ~spl2_187),
% 25.79/3.62    inference(avatar_split_clause,[],[f49770,f49611,f36127,f54844])).
% 25.79/3.62  fof(f36127,plain,(
% 25.79/3.62    spl2_164 <=> ! [X44,X46,X45] : k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_164])])).
% 25.79/3.62  fof(f49611,plain,(
% 25.79/3.62    spl2_187 <=> ! [X131,X130,X132] : k1_xboole_0 = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131)))))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_187])])).
% 25.79/3.62  fof(f49770,plain,(
% 25.79/3.62    ( ! [X28,X29,X27] : (k1_xboole_0 = k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X29,X28)))) ) | (~spl2_164 | ~spl2_187)),
% 25.79/3.62    inference(superposition,[],[f49612,f36128])).
% 25.79/3.62  fof(f36128,plain,(
% 25.79/3.62    ( ! [X45,X46,X44] : (k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46)))) ) | ~spl2_164),
% 25.79/3.62    inference(avatar_component_clause,[],[f36127])).
% 25.79/3.62  fof(f49612,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k1_xboole_0 = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131)))))) ) | ~spl2_187),
% 25.79/3.62    inference(avatar_component_clause,[],[f49611])).
% 25.79/3.62  fof(f50355,plain,(
% 25.79/3.62    spl2_188 | ~spl2_3 | ~spl2_28 | ~spl2_187),
% 25.79/3.62    inference(avatar_split_clause,[],[f50101,f49611,f684,f47,f50353])).
% 25.79/3.62  fof(f47,plain,(
% 25.79/3.62    spl2_3 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 25.79/3.62  fof(f50101,plain,(
% 25.79/3.62    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18)))) = X17) ) | (~spl2_3 | ~spl2_28 | ~spl2_187)),
% 25.79/3.62    inference(forward_demodulation,[],[f49777,f685])).
% 25.79/3.62  fof(f49777,plain,(
% 25.79/3.62    ( ! [X19,X17,X18] : (k5_xboole_0(X17,k1_xboole_0) = k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X19,X18))))) ) | (~spl2_3 | ~spl2_187)),
% 25.79/3.62    inference(superposition,[],[f48,f49612])).
% 25.79/3.62  fof(f48,plain,(
% 25.79/3.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_3),
% 25.79/3.62    inference(avatar_component_clause,[],[f47])).
% 25.79/3.62  fof(f49613,plain,(
% 25.79/3.62    spl2_187 | ~spl2_1 | ~spl2_4 | ~spl2_28 | ~spl2_30 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81 | ~spl2_117 | ~spl2_135 | ~spl2_151),
% 25.79/3.62    inference(avatar_split_clause,[],[f41370,f32392,f22102,f18279,f3326,f3322,f3302,f1538,f1205,f1155,f1151,f1147,f720,f684,f51,f39,f49611])).
% 25.79/3.62  fof(f720,plain,(
% 25.79/3.62    spl2_30 <=> ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 25.79/3.62  fof(f1147,plain,(
% 25.79/3.62    spl2_48 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 25.79/3.62  fof(f1155,plain,(
% 25.79/3.62    spl2_50 <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 25.79/3.62  fof(f3302,plain,(
% 25.79/3.62    spl2_75 <=> ! [X9,X8] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(k4_xboole_0(X8,X9),X8)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 25.79/3.62  fof(f3322,plain,(
% 25.79/3.62    spl2_80 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 25.79/3.62  fof(f3326,plain,(
% 25.79/3.62    spl2_81 <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 25.79/3.62  fof(f18279,plain,(
% 25.79/3.62    spl2_117 <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).
% 25.79/3.62  fof(f22102,plain,(
% 25.79/3.62    spl2_135 <=> ! [X16,X15,X17] : k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X15,X16)))) = X15),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 25.79/3.62  fof(f32392,plain,(
% 25.79/3.62    spl2_151 <=> ! [X5,X7,X6] : k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,k4_xboole_0(X5,X7)))))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).
% 25.79/3.62  fof(f41370,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k1_xboole_0 = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131)))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_28 | ~spl2_30 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81 | ~spl2_117 | ~spl2_135 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41369,f721])).
% 25.79/3.62  fof(f721,plain,(
% 25.79/3.62    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(X10,X10)) ) | ~spl2_30),
% 25.79/3.62    inference(avatar_component_clause,[],[f720])).
% 25.79/3.62  fof(f41369,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131))))) = k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X130,k4_xboole_0(X130,X131)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_28 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81 | ~spl2_117 | ~spl2_135 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41368,f25045])).
% 25.79/3.62  fof(f25045,plain,(
% 25.79/3.62    ( ! [X88,X87,X89] : (k4_xboole_0(X87,k4_xboole_0(X87,X88)) = k4_xboole_0(k4_xboole_0(X87,k4_xboole_0(X87,X88)),k4_xboole_0(X89,k4_xboole_0(X88,k4_xboole_0(X88,X87))))) ) | (~spl2_28 | ~spl2_117 | ~spl2_135)),
% 25.79/3.62    inference(forward_demodulation,[],[f24894,f685])).
% 25.79/3.62  fof(f24894,plain,(
% 25.79/3.62    ( ! [X88,X87,X89] : (k4_xboole_0(X87,k4_xboole_0(X87,X88)) = k4_xboole_0(k4_xboole_0(X87,k4_xboole_0(X87,X88)),k4_xboole_0(X89,k5_xboole_0(k4_xboole_0(X88,k4_xboole_0(X88,X87)),k1_xboole_0)))) ) | (~spl2_117 | ~spl2_135)),
% 25.79/3.62    inference(superposition,[],[f22103,f18280])).
% 25.79/3.62  fof(f18280,plain,(
% 25.79/3.62    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) ) | ~spl2_117),
% 25.79/3.62    inference(avatar_component_clause,[],[f18279])).
% 25.79/3.62  fof(f22103,plain,(
% 25.79/3.62    ( ! [X17,X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X15,X16)))) = X15) ) | ~spl2_135),
% 25.79/3.62    inference(avatar_component_clause,[],[f22102])).
% 25.79/3.62  fof(f41368,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X130,k4_xboole_0(X132,X131)))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81 | ~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41367,f5566])).
% 25.79/3.62  fof(f5566,plain,(
% 25.79/3.62    ( ! [X80,X78,X81,X79] : (k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(X78,k4_xboole_0(X80,X81)))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81)),
% 25.79/3.62    inference(backward_demodulation,[],[f4110,f5565])).
% 25.79/3.62  fof(f5565,plain,(
% 25.79/3.62    ( ! [X54,X55,X53] : (k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X55,k4_xboole_0(X53,X54)))) = k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X55,X54))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81)),
% 25.79/3.62    inference(forward_demodulation,[],[f5564,f3323])).
% 25.79/3.62  fof(f3323,plain,(
% 25.79/3.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl2_80),
% 25.79/3.62    inference(avatar_component_clause,[],[f3322])).
% 25.79/3.62  fof(f5564,plain,(
% 25.79/3.62    ( ! [X54,X55,X53] : (k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(X53,k4_xboole_0(X53,X54)))) = k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X55,k4_xboole_0(X53,X54))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81)),
% 25.79/3.62    inference(forward_demodulation,[],[f5435,f4215])).
% 25.79/3.62  fof(f4215,plain,(
% 25.79/3.62    ( ! [X50,X48,X49] : (k5_xboole_0(k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50))),k4_xboole_0(X48,k4_xboole_0(X48,X49))) = k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X50,k4_xboole_0(X48,X49))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4167,f4082])).
% 25.79/3.62  fof(f4082,plain,(
% 25.79/3.62    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X37)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X38)))) = k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X38,k4_xboole_0(X36,X37))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4081,f1539])).
% 25.79/3.62  fof(f4081,plain,(
% 25.79/3.62    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X37)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X38)))) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X38)),k4_xboole_0(X36,X37))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f3874,f2267])).
% 25.79/3.62  fof(f2267,plain,(
% 25.79/3.62    ( ! [X30,X28,X29] : (k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X30))) = k4_xboole_0(k4_xboole_0(X28,X29),X30)) ) | (~spl2_1 | ~spl2_51 | ~spl2_54)),
% 25.79/3.62    inference(forward_demodulation,[],[f2177,f40])).
% 25.79/3.62  fof(f2177,plain,(
% 25.79/3.62    ( ! [X30,X28,X29] : (k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X30))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X28,X29),k1_xboole_0),X30)) ) | (~spl2_51 | ~spl2_54)),
% 25.79/3.62    inference(superposition,[],[f1539,f1206])).
% 25.79/3.62  fof(f3874,plain,(
% 25.79/3.62    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X37)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X38)))) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X38)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X38)),k4_xboole_0(X36,k4_xboole_0(X36,X37))))) ) | (~spl2_4 | ~spl2_80)),
% 25.79/3.62    inference(superposition,[],[f52,f3323])).
% 25.79/3.62  fof(f4167,plain,(
% 25.79/3.62    ( ! [X50,X48,X49] : (k4_xboole_0(k4_xboole_0(X48,k4_xboole_0(X48,X49)),k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50)))) = k5_xboole_0(k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50))),k4_xboole_0(X48,k4_xboole_0(X48,X49)))) ) | (~spl2_54 | ~spl2_75)),
% 25.79/3.62    inference(superposition,[],[f3303,f1539])).
% 25.79/3.62  fof(f3303,plain,(
% 25.79/3.62    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(k4_xboole_0(X8,X9),X8)) ) | ~spl2_75),
% 25.79/3.62    inference(avatar_component_clause,[],[f3302])).
% 25.79/3.62  fof(f5435,plain,(
% 25.79/3.62    ( ! [X54,X55,X53] : (k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X55)),k4_xboole_0(X53,k4_xboole_0(X53,X54)))) = k5_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,k4_xboole_0(X54,X55))),k4_xboole_0(X53,k4_xboole_0(X53,X54)))) ) | (~spl2_80 | ~spl2_81)),
% 25.79/3.62    inference(superposition,[],[f3327,f3323])).
% 25.79/3.62  fof(f3327,plain,(
% 25.79/3.62    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | ~spl2_81),
% 25.79/3.62    inference(avatar_component_clause,[],[f3326])).
% 25.79/3.62  fof(f4110,plain,(
% 25.79/3.62    ( ! [X80,X78,X81,X79] : (k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(X80,X81)))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4109,f3855])).
% 25.79/3.62  fof(f3855,plain,(
% 25.79/3.62    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,k4_xboole_0(X5,X7)))))) ) | (~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(superposition,[],[f3323,f1539])).
% 25.79/3.62  fof(f4109,plain,(
% 25.79/3.62    ( ! [X80,X78,X81,X79] : (k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X80,X81)))))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4108,f1539])).
% 25.79/3.62  fof(f4108,plain,(
% 25.79/3.62    ( ! [X80,X78,X81,X79] : (k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81)))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4107,f1539])).
% 25.79/3.62  fof(f4107,plain,(
% 25.79/3.62    ( ! [X80,X78,X81,X79] : (k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81))) = k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X78,X79)),X81)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4106,f1539])).
% 25.79/3.62  fof(f4106,plain,(
% 25.79/3.62    ( ! [X80,X78,X81,X79] : (k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81))) = k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X80,k4_xboole_0(X78,X79)))),X81)) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f3888,f4082])).
% 25.79/3.62  fof(f3888,plain,(
% 25.79/3.62    ( ! [X80,X78,X81,X79] : (k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X80)),X81))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X78,k4_xboole_0(X78,X79)),k4_xboole_0(X78,k4_xboole_0(X78,k4_xboole_0(X79,X80)))),X81)) ) | (~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(superposition,[],[f1539,f3323])).
% 25.79/3.62  fof(f41367,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X132,k4_xboole_0(X130,X131)),X131)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81 | ~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41366,f4095])).
% 25.79/3.62  fof(f4095,plain,(
% 25.79/3.62    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X57,X59)) = k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X59,X58)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4094,f3323])).
% 25.79/3.62  fof(f4094,plain,(
% 25.79/3.62    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X57,X59))) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4093,f2254])).
% 25.79/3.62  fof(f2254,plain,(
% 25.79/3.62    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) ) | (~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_54)),
% 25.79/3.62    inference(forward_demodulation,[],[f2253,f1148])).
% 25.79/3.62  fof(f1148,plain,(
% 25.79/3.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_48),
% 25.79/3.62    inference(avatar_component_clause,[],[f1147])).
% 25.79/3.62  fof(f2253,plain,(
% 25.79/3.62    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) ) | (~spl2_49 | ~spl2_50 | ~spl2_54)),
% 25.79/3.62    inference(forward_demodulation,[],[f2168,f1152])).
% 25.79/3.62  fof(f2168,plain,(
% 25.79/3.62    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) ) | (~spl2_50 | ~spl2_54)),
% 25.79/3.62    inference(superposition,[],[f1539,f1156])).
% 25.79/3.62  fof(f1156,plain,(
% 25.79/3.62    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) ) | ~spl2_50),
% 25.79/3.62    inference(avatar_component_clause,[],[f1155])).
% 25.79/3.62  fof(f4093,plain,(
% 25.79/3.62    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X57,X59))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f4092,f4082])).
% 25.79/3.62  fof(f4092,plain,(
% 25.79/3.62    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X59,k4_xboole_0(X57,X58)))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_51 | ~spl2_54 | ~spl2_80)),
% 25.79/3.62    inference(forward_demodulation,[],[f3881,f4082])).
% 25.79/3.62  fof(f3881,plain,(
% 25.79/3.62    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(X57,k4_xboole_0(X57,X58))) = k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X59)),k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X58)),k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X58,X59)))))) ) | (~spl2_48 | ~spl2_80)),
% 25.79/3.62    inference(superposition,[],[f1148,f3323])).
% 25.79/3.62  fof(f41366,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(k4_xboole_0(X130,X131),k4_xboole_0(X130,k4_xboole_0(X132,k4_xboole_0(X130,X131))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_49 | ~spl2_50 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81 | ~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41365,f2254])).
% 25.79/3.62  fof(f41365,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X130,X131),k4_xboole_0(X130,k4_xboole_0(X132,k4_xboole_0(X130,X131))))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_75 | ~spl2_80 | ~spl2_81 | ~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41364,f5566])).
% 25.79/3.62  fof(f41364,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X132,k4_xboole_0(X130,k4_xboole_0(X130,X131))),k4_xboole_0(X130,X131))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80 | ~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41363,f40])).
% 25.79/3.62  fof(f41363,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(k4_xboole_0(X132,k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k1_xboole_0)),k4_xboole_0(X130,X131))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_51 | ~spl2_54 | ~spl2_80 | ~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41362,f4082])).
% 25.79/3.62  fof(f41362,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X131,k4_xboole_0(X132,k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k1_xboole_0))))))) ) | (~spl2_54 | ~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(forward_demodulation,[],[f41075,f1539])).
% 25.79/3.62  fof(f41075,plain,(
% 25.79/3.62    ( ! [X132,X130,X131] : (k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(X131,k4_xboole_0(X131,X130))))) = k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k4_xboole_0(X132,k4_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,X131)),k1_xboole_0))))) ) | (~spl2_117 | ~spl2_151)),
% 25.79/3.62    inference(superposition,[],[f32393,f18280])).
% 25.79/3.62  fof(f32393,plain,(
% 25.79/3.62    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,k4_xboole_0(X5,X7)))))) ) | ~spl2_151),
% 25.79/3.62    inference(avatar_component_clause,[],[f32392])).
% 25.79/3.62  fof(f39774,plain,(
% 25.79/3.62    spl2_171 | ~spl2_41 | ~spl2_132 | ~spl2_138 | ~spl2_139 | ~spl2_159),
% 25.79/3.62    inference(avatar_split_clause,[],[f36950,f36107,f25158,f25154,f22090,f993,f39772])).
% 25.79/3.62  fof(f22090,plain,(
% 25.79/3.62    spl2_132 <=> ! [X27,X26] : k5_xboole_0(X26,X27) = k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).
% 25.79/3.62  fof(f25158,plain,(
% 25.79/3.62    spl2_139 <=> ! [X32,X31] : k4_xboole_0(X31,X32) = k5_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X32,X31))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 25.79/3.62  fof(f36107,plain,(
% 25.79/3.62    spl2_159 <=> ! [X69,X68,X70] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).
% 25.79/3.62  fof(f36950,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k4_xboole_0(X213,X214) = k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213))) ) | (~spl2_41 | ~spl2_132 | ~spl2_138 | ~spl2_139 | ~spl2_159)),
% 25.79/3.62    inference(forward_demodulation,[],[f36946,f994])).
% 25.79/3.62  fof(f36946,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X213,X214))) ) | (~spl2_132 | ~spl2_138 | ~spl2_139 | ~spl2_159)),
% 25.79/3.62    inference(backward_demodulation,[],[f27375,f36765])).
% 25.79/3.62  fof(f36765,plain,(
% 25.79/3.62    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5))) ) | (~spl2_132 | ~spl2_159)),
% 25.79/3.62    inference(superposition,[],[f36108,f22091])).
% 25.79/3.62  fof(f22091,plain,(
% 25.79/3.62    ( ! [X26,X27] : (k5_xboole_0(X26,X27) = k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))) ) | ~spl2_132),
% 25.79/3.62    inference(avatar_component_clause,[],[f22090])).
% 25.79/3.62  fof(f36108,plain,(
% 25.79/3.62    ( ! [X70,X68,X69] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))) ) | ~spl2_159),
% 25.79/3.62    inference(avatar_component_clause,[],[f36107])).
% 25.79/3.62  fof(f27375,plain,(
% 25.79/3.62    ( ! [X213,X214] : (k4_xboole_0(k5_xboole_0(X213,X214),k4_xboole_0(X214,X213)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X214,X213),k5_xboole_0(X213,X214)),k4_xboole_0(X213,X214))) ) | (~spl2_138 | ~spl2_139)),
% 25.79/3.62    inference(superposition,[],[f25155,f25159])).
% 25.79/3.62  fof(f25159,plain,(
% 25.79/3.62    ( ! [X31,X32] : (k4_xboole_0(X31,X32) = k5_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X32,X31))) ) | ~spl2_139),
% 25.79/3.62    inference(avatar_component_clause,[],[f25158])).
% 25.79/3.62  fof(f37581,plain,(
% 25.79/3.62    spl2_166 | ~spl2_136 | ~spl2_159),
% 25.79/3.62    inference(avatar_split_clause,[],[f36764,f36107,f25146,f37579])).
% 25.79/3.62  fof(f25146,plain,(
% 25.79/3.62    spl2_136 <=> ! [X32,X33] : k5_xboole_0(X33,X32) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).
% 25.79/3.62  fof(f36764,plain,(
% 25.79/3.62    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4))) ) | (~spl2_136 | ~spl2_159)),
% 25.79/3.62    inference(superposition,[],[f36108,f25147])).
% 25.79/3.62  fof(f25147,plain,(
% 25.79/3.62    ( ! [X33,X32] : (k5_xboole_0(X33,X32) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))) ) | ~spl2_136),
% 25.79/3.62    inference(avatar_component_clause,[],[f25146])).
% 25.79/3.62  fof(f36129,plain,(
% 25.79/3.62    spl2_164 | ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_46 | ~spl2_54 | ~spl2_55 | ~spl2_123),
% 25.79/3.62    inference(avatar_split_clause,[],[f20970,f20053,f1542,f1538,f1076,f59,f51,f39,f36127])).
% 25.79/3.62  fof(f1542,plain,(
% 25.79/3.62    spl2_55 <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 25.79/3.62  fof(f20970,plain,(
% 25.79/3.62    ( ! [X45,X46,X44] : (k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_46 | ~spl2_54 | ~spl2_55 | ~spl2_123)),
% 25.79/3.62    inference(backward_demodulation,[],[f2182,f20963])).
% 25.79/3.62  fof(f20963,plain,(
% 25.79/3.62    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X3) ) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_46 | ~spl2_55 | ~spl2_123)),
% 25.79/3.62    inference(forward_demodulation,[],[f20940,f40])).
% 25.79/3.62  fof(f20940,plain,(
% 25.79/3.62    ( ! [X2,X3] : (k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3))) ) | (~spl2_4 | ~spl2_6 | ~spl2_46 | ~spl2_55 | ~spl2_123)),
% 25.79/3.62    inference(backward_demodulation,[],[f378,f20939])).
% 25.79/3.62  fof(f20939,plain,(
% 25.79/3.62    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X8,k4_xboole_0(X7,X8)))) ) | (~spl2_46 | ~spl2_55 | ~spl2_123)),
% 25.79/3.62    inference(forward_demodulation,[],[f20672,f1077])).
% 25.79/3.62  fof(f20672,plain,(
% 25.79/3.62    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),X8))) ) | (~spl2_55 | ~spl2_123)),
% 25.79/3.62    inference(superposition,[],[f1543,f20054])).
% 25.79/3.62  fof(f1543,plain,(
% 25.79/3.62    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9)))) ) | ~spl2_55),
% 25.79/3.62    inference(avatar_component_clause,[],[f1542])).
% 25.79/3.62  fof(f378,plain,(
% 25.79/3.62    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,X2)))) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3))) ) | (~spl2_4 | ~spl2_6)),
% 25.79/3.62    inference(superposition,[],[f52,f60])).
% 25.79/3.62  fof(f2182,plain,(
% 25.79/3.62    ( ! [X45,X46,X44] : (k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X45,X46))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),k4_xboole_0(X44,X45)),X46)) ) | (~spl2_6 | ~spl2_54)),
% 25.79/3.62    inference(superposition,[],[f1539,f60])).
% 25.79/3.62  fof(f36109,plain,(
% 25.79/3.62    spl2_159 | ~spl2_55 | ~spl2_70),
% 25.79/3.62    inference(avatar_split_clause,[],[f2678,f2601,f1542,f36107])).
% 25.79/3.62  fof(f2601,plain,(
% 25.79/3.62    spl2_70 <=> ! [X16,X15,X14] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 25.79/3.62  fof(f2678,plain,(
% 25.79/3.62    ( ! [X70,X68,X69] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))) ) | (~spl2_55 | ~spl2_70)),
% 25.79/3.62    inference(superposition,[],[f1543,f2602])).
% 25.79/3.62  fof(f2602,plain,(
% 25.79/3.62    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))) ) | ~spl2_70),
% 25.79/3.62    inference(avatar_component_clause,[],[f2601])).
% 25.79/3.62  fof(f32394,plain,(
% 25.79/3.62    spl2_151 | ~spl2_54 | ~spl2_80),
% 25.79/3.62    inference(avatar_split_clause,[],[f3855,f3322,f1538,f32392])).
% 25.79/3.62  fof(f25160,plain,(
% 25.79/3.62    spl2_139 | ~spl2_101 | ~spl2_129),
% 25.79/3.62    inference(avatar_split_clause,[],[f23218,f22078,f9538,f25158])).
% 25.79/3.62  fof(f9538,plain,(
% 25.79/3.62    spl2_101 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 25.79/3.62  fof(f22078,plain,(
% 25.79/3.62    spl2_129 <=> ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X23,k5_xboole_0(X22,k4_xboole_0(X23,X22)))),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).
% 25.79/3.62  fof(f23218,plain,(
% 25.79/3.62    ( ! [X31,X32] : (k4_xboole_0(X31,X32) = k5_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X32,X31))) ) | (~spl2_101 | ~spl2_129)),
% 25.79/3.62    inference(superposition,[],[f9539,f22079])).
% 25.79/3.62  fof(f22079,plain,(
% 25.79/3.62    ( ! [X23,X22] : (k4_xboole_0(X22,X23) = k5_xboole_0(X23,k5_xboole_0(X22,k4_xboole_0(X23,X22)))) ) | ~spl2_129),
% 25.79/3.62    inference(avatar_component_clause,[],[f22078])).
% 25.79/3.62  fof(f9539,plain,(
% 25.79/3.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) ) | ~spl2_101),
% 25.79/3.62    inference(avatar_component_clause,[],[f9538])).
% 25.79/3.62  fof(f25156,plain,(
% 25.79/3.62    spl2_138 | ~spl2_66 | ~spl2_129),
% 25.79/3.62    inference(avatar_split_clause,[],[f23207,f22078,f2164,f25154])).
% 25.79/3.62  fof(f2164,plain,(
% 25.79/3.62    spl2_66 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 25.79/3.62  fof(f23207,plain,(
% 25.79/3.62    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X7,X8))) ) | (~spl2_66 | ~spl2_129)),
% 25.79/3.62    inference(superposition,[],[f2165,f22079])).
% 25.79/3.62  fof(f2165,plain,(
% 25.79/3.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2) ) | ~spl2_66),
% 25.79/3.62    inference(avatar_component_clause,[],[f2164])).
% 25.79/3.62  fof(f25148,plain,(
% 25.79/3.62    spl2_136 | ~spl2_103 | ~spl2_121),
% 25.79/3.62    inference(avatar_split_clause,[],[f19658,f19572,f9546,f25146])).
% 25.79/3.62  fof(f9546,plain,(
% 25.79/3.62    spl2_103 <=> ! [X25,X27,X26] : k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X25)),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).
% 25.79/3.62  fof(f19572,plain,(
% 25.79/3.62    spl2_121 <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).
% 25.79/3.62  fof(f19658,plain,(
% 25.79/3.62    ( ! [X33,X32] : (k5_xboole_0(X33,X32) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))) ) | (~spl2_103 | ~spl2_121)),
% 25.79/3.62    inference(superposition,[],[f9547,f19573])).
% 25.79/3.62  fof(f19573,plain,(
% 25.79/3.62    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3) ) | ~spl2_121),
% 25.79/3.62    inference(avatar_component_clause,[],[f19572])).
% 25.79/3.62  fof(f9547,plain,(
% 25.79/3.62    ( ! [X26,X27,X25] : (k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X25)) ) | ~spl2_103),
% 25.79/3.62    inference(avatar_component_clause,[],[f9546])).
% 25.79/3.62  fof(f22104,plain,(
% 25.79/3.62    spl2_135 | ~spl2_46 | ~spl2_74 | ~spl2_123),
% 25.79/3.62    inference(avatar_split_clause,[],[f21000,f20053,f3161,f1076,f22102])).
% 25.79/3.62  fof(f3161,plain,(
% 25.79/3.62    spl2_74 <=> ! [X75,X77,X76] : k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X75,k4_xboole_0(X76,X75)))) = X75),
% 25.79/3.62    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 25.79/3.62  fof(f21000,plain,(
% 25.79/3.62    ( ! [X17,X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X15,X16)))) = X15) ) | (~spl2_46 | ~spl2_74 | ~spl2_123)),
% 25.79/3.62    inference(forward_demodulation,[],[f20676,f1077])).
% 25.79/3.62  fof(f20676,plain,(
% 25.79/3.62    ( ! [X17,X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X17,k5_xboole_0(k4_xboole_0(X15,X16),X16))) = X15) ) | (~spl2_74 | ~spl2_123)),
% 25.79/3.62    inference(superposition,[],[f3162,f20054])).
% 25.79/3.63  fof(f3162,plain,(
% 25.79/3.63    ( ! [X76,X77,X75] : (k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X75,k4_xboole_0(X76,X75)))) = X75) ) | ~spl2_74),
% 25.79/3.63    inference(avatar_component_clause,[],[f3161])).
% 25.79/3.63  fof(f22092,plain,(
% 25.79/3.63    spl2_132 | ~spl2_95 | ~spl2_121),
% 25.79/3.63    inference(avatar_split_clause,[],[f19655,f19572,f3382,f22090])).
% 25.79/3.63  fof(f3382,plain,(
% 25.79/3.63    spl2_95 <=> ! [X13,X12,X14] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 25.79/3.63  fof(f19655,plain,(
% 25.79/3.63    ( ! [X26,X27] : (k5_xboole_0(X26,X27) = k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))) ) | (~spl2_95 | ~spl2_121)),
% 25.79/3.63    inference(superposition,[],[f3383,f19573])).
% 25.79/3.63  fof(f3383,plain,(
% 25.79/3.63    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))) ) | ~spl2_95),
% 25.79/3.63    inference(avatar_component_clause,[],[f3382])).
% 25.79/3.63  fof(f22080,plain,(
% 25.79/3.63    spl2_129 | ~spl2_92 | ~spl2_121),
% 25.79/3.63    inference(avatar_split_clause,[],[f19653,f19572,f3370,f22078])).
% 25.79/3.63  fof(f3370,plain,(
% 25.79/3.63    spl2_92 <=> ! [X16,X15,X14] : k5_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X16)),k5_xboole_0(X15,X16)) = X14),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 25.79/3.63  fof(f19653,plain,(
% 25.79/3.63    ( ! [X23,X22] : (k4_xboole_0(X22,X23) = k5_xboole_0(X23,k5_xboole_0(X22,k4_xboole_0(X23,X22)))) ) | (~spl2_92 | ~spl2_121)),
% 25.79/3.63    inference(superposition,[],[f3371,f19573])).
% 25.79/3.63  fof(f3371,plain,(
% 25.79/3.63    ( ! [X14,X15,X16] : (k5_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X16)),k5_xboole_0(X15,X16)) = X14) ) | ~spl2_92),
% 25.79/3.63    inference(avatar_component_clause,[],[f3370])).
% 25.79/3.63  fof(f21370,plain,(
% 25.79/3.63    spl2_125 | ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_46 | ~spl2_55 | ~spl2_123),
% 25.79/3.63    inference(avatar_split_clause,[],[f20963,f20053,f1542,f1076,f59,f51,f39,f21368])).
% 25.79/3.63  fof(f20055,plain,(
% 25.79/3.63    spl2_123 | ~spl2_61 | ~spl2_121),
% 25.79/3.63    inference(avatar_split_clause,[],[f19647,f19572,f1860,f20053])).
% 25.79/3.63  fof(f19647,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k4_xboole_0(X2,X3),X3)) ) | (~spl2_61 | ~spl2_121)),
% 25.79/3.63    inference(superposition,[],[f1861,f19573])).
% 25.79/3.63  fof(f19574,plain,(
% 25.79/3.63    spl2_121 | ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_31 | ~spl2_47 | ~spl2_49 | ~spl2_120),
% 25.79/3.63    inference(avatar_split_clause,[],[f19496,f18291,f1151,f1143,f724,f51,f43,f39,f19572])).
% 25.79/3.63  fof(f724,plain,(
% 25.79/3.63    spl2_31 <=> ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 25.79/3.63  fof(f1143,plain,(
% 25.79/3.63    spl2_47 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 25.79/3.63  fof(f18291,plain,(
% 25.79/3.63    spl2_120 <=> ! [X27,X26] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 25.79/3.63  fof(f19496,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3) ) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_31 | ~spl2_47 | ~spl2_49 | ~spl2_120)),
% 25.79/3.63    inference(forward_demodulation,[],[f19494,f40])).
% 25.79/3.63  fof(f19494,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_31 | ~spl2_47 | ~spl2_49 | ~spl2_120)),
% 25.79/3.63    inference(backward_demodulation,[],[f19488,f19493])).
% 25.79/3.63  fof(f19493,plain,(
% 25.79/3.63    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_31 | ~spl2_47 | ~spl2_49 | ~spl2_120)),
% 25.79/3.63    inference(forward_demodulation,[],[f19492,f725])).
% 25.79/3.63  fof(f725,plain,(
% 25.79/3.63    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) ) | ~spl2_31),
% 25.79/3.63    inference(avatar_component_clause,[],[f724])).
% 25.79/3.63  fof(f19492,plain,(
% 25.79/3.63    ( ! [X14,X15] : (k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X15,X14)) = k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_47 | ~spl2_49 | ~spl2_120)),
% 25.79/3.63    inference(forward_demodulation,[],[f19491,f1376])).
% 25.79/3.63  fof(f1376,plain,(
% 25.79/3.63    ( ! [X2,X3,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X1),X3)))) ) | (~spl2_2 | ~spl2_47 | ~spl2_49)),
% 25.79/3.63    inference(backward_demodulation,[],[f1174,f1358])).
% 25.79/3.63  fof(f1358,plain,(
% 25.79/3.63    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X5),X6)) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6)) ) | (~spl2_2 | ~spl2_49)),
% 25.79/3.63    inference(superposition,[],[f44,f1152])).
% 25.79/3.63  fof(f1174,plain,(
% 25.79/3.63    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)) ) | (~spl2_2 | ~spl2_47)),
% 25.79/3.63    inference(superposition,[],[f44,f1144])).
% 25.79/3.63  fof(f1144,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_47),
% 25.79/3.63    inference(avatar_component_clause,[],[f1143])).
% 25.79/3.63  fof(f19491,plain,(
% 25.79/3.63    ( ! [X14,X15] : (k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)))) = k5_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))) ) | (~spl2_1 | ~spl2_47 | ~spl2_120)),
% 25.79/3.63    inference(forward_demodulation,[],[f19216,f40])).
% 25.79/3.63  fof(f19216,plain,(
% 25.79/3.63    ( ! [X14,X15] : (k4_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)))) = k5_xboole_0(X15,k4_xboole_0(k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))),k1_xboole_0))) ) | (~spl2_47 | ~spl2_120)),
% 25.79/3.63    inference(superposition,[],[f1144,f18292])).
% 25.79/3.63  fof(f18292,plain,(
% 25.79/3.63    ( ! [X26,X27] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26)) ) | ~spl2_120),
% 25.79/3.63    inference(avatar_component_clause,[],[f18291])).
% 25.79/3.63  fof(f19488,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))))) ) | (~spl2_1 | ~spl2_4 | ~spl2_120)),
% 25.79/3.63    inference(forward_demodulation,[],[f19210,f40])).
% 25.79/3.63  fof(f19210,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),k1_xboole_0)) ) | (~spl2_4 | ~spl2_120)),
% 25.79/3.63    inference(superposition,[],[f52,f18292])).
% 25.79/3.63  fof(f18293,plain,(
% 25.79/3.63    spl2_120 | ~spl2_2 | ~spl2_6 | ~spl2_46 | ~spl2_50 | ~spl2_51),
% 25.79/3.63    inference(avatar_split_clause,[],[f1451,f1205,f1155,f1076,f59,f43,f18291])).
% 25.79/3.63  fof(f1451,plain,(
% 25.79/3.63    ( ! [X26,X27] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26)) ) | (~spl2_2 | ~spl2_6 | ~spl2_46 | ~spl2_50 | ~spl2_51)),
% 25.79/3.63    inference(forward_demodulation,[],[f1450,f1206])).
% 25.79/3.63  fof(f1450,plain,(
% 25.79/3.63    ( ! [X26,X27] : (k4_xboole_0(k4_xboole_0(X26,X27),X26) = k4_xboole_0(k5_xboole_0(X27,k5_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X27))),X26)) ) | (~spl2_2 | ~spl2_6 | ~spl2_46 | ~spl2_50)),
% 25.79/3.63    inference(forward_demodulation,[],[f1406,f1112])).
% 25.79/3.63  fof(f1112,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_46)),
% 25.79/3.63    inference(superposition,[],[f1077,f44])).
% 25.79/3.63  fof(f1406,plain,(
% 25.79/3.63    ( ! [X26,X27] : (k4_xboole_0(k4_xboole_0(X26,X27),X26) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X26,X27),k5_xboole_0(X27,k4_xboole_0(X27,X26))),X26)) ) | (~spl2_6 | ~spl2_50)),
% 25.79/3.63    inference(superposition,[],[f60,f1156])).
% 25.79/3.63  fof(f18281,plain,(
% 25.79/3.63    spl2_117 | ~spl2_1 | ~spl2_30 | ~spl2_48),
% 25.79/3.63    inference(avatar_split_clause,[],[f1324,f1147,f720,f39,f18279])).
% 25.79/3.63  fof(f1324,plain,(
% 25.79/3.63    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) ) | (~spl2_1 | ~spl2_30 | ~spl2_48)),
% 25.79/3.63    inference(forward_demodulation,[],[f1323,f721])).
% 25.79/3.63  fof(f1323,plain,(
% 25.79/3.63    ( ! [X10,X9] : (k4_xboole_0(X10,X10) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) ) | (~spl2_1 | ~spl2_30 | ~spl2_48)),
% 25.79/3.63    inference(forward_demodulation,[],[f1322,f40])).
% 25.79/3.63  fof(f1322,plain,(
% 25.79/3.63    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) ) | (~spl2_30 | ~spl2_48)),
% 25.79/3.63    inference(forward_demodulation,[],[f1321,f721])).
% 25.79/3.63  fof(f1321,plain,(
% 25.79/3.63    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X9)))) ) | ~spl2_48),
% 25.79/3.63    inference(forward_demodulation,[],[f1289,f35])).
% 25.79/3.63  fof(f35,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 25.79/3.63    inference(definition_unfolding,[],[f27,f22,f22])).
% 25.79/3.63  fof(f22,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 25.79/3.63    inference(cnf_transformation,[],[f7])).
% 25.79/3.63  fof(f7,axiom,(
% 25.79/3.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 25.79/3.63  fof(f27,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 25.79/3.63    inference(cnf_transformation,[],[f8])).
% 25.79/3.63  fof(f8,axiom,(
% 25.79/3.63    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 25.79/3.63  fof(f1289,plain,(
% 25.79/3.63    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) ) | ~spl2_48),
% 25.79/3.63    inference(superposition,[],[f1148,f1148])).
% 25.79/3.63  fof(f16643,plain,(
% 25.79/3.63    spl2_115 | ~spl2_28 | ~spl2_63 | ~spl2_98),
% 25.79/3.63    inference(avatar_split_clause,[],[f4629,f4452,f2152,f684,f16641])).
% 25.79/3.63  fof(f2152,plain,(
% 25.79/3.63    spl2_63 <=> ! [X1,X0,X2] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 25.79/3.63  fof(f4452,plain,(
% 25.79/3.63    spl2_98 <=> ! [X11,X12] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X12,X11))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 25.79/3.63  fof(f4629,plain,(
% 25.79/3.63    ( ! [X37,X35,X36] : (k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(X37,k5_xboole_0(X36,X35))) ) | (~spl2_28 | ~spl2_63 | ~spl2_98)),
% 25.79/3.63    inference(forward_demodulation,[],[f4534,f685])).
% 25.79/3.63  fof(f4534,plain,(
% 25.79/3.63    ( ! [X37,X35,X36] : (k5_xboole_0(X37,k5_xboole_0(X35,X36)) = k5_xboole_0(k5_xboole_0(X37,k1_xboole_0),k5_xboole_0(X36,X35))) ) | (~spl2_63 | ~spl2_98)),
% 25.79/3.63    inference(superposition,[],[f2153,f4453])).
% 25.79/3.63  fof(f4453,plain,(
% 25.79/3.63    ( ! [X12,X11] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X12,X11))) ) | ~spl2_98),
% 25.79/3.63    inference(avatar_component_clause,[],[f4452])).
% 25.79/3.63  fof(f2153,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2)) ) | ~spl2_63),
% 25.79/3.63    inference(avatar_component_clause,[],[f2152])).
% 25.79/3.63  fof(f9548,plain,(
% 25.79/3.63    spl2_103 | ~spl2_2 | ~spl2_45 | ~spl2_63),
% 25.79/3.63    inference(avatar_split_clause,[],[f3446,f2152,f1072,f43,f9546])).
% 25.79/3.63  fof(f1072,plain,(
% 25.79/3.63    spl2_45 <=> ! [X9,X8] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 25.79/3.63  fof(f3446,plain,(
% 25.79/3.63    ( ! [X26,X27,X25] : (k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X25)) ) | (~spl2_2 | ~spl2_45 | ~spl2_63)),
% 25.79/3.63    inference(forward_demodulation,[],[f3418,f44])).
% 25.79/3.63  fof(f3418,plain,(
% 25.79/3.63    ( ! [X26,X27,X25] : (k5_xboole_0(X27,X26) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X25,X26),X27),X25)) ) | (~spl2_45 | ~spl2_63)),
% 25.79/3.63    inference(superposition,[],[f2153,f1073])).
% 25.79/3.63  fof(f1073,plain,(
% 25.79/3.63    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) ) | ~spl2_45),
% 25.79/3.63    inference(avatar_component_clause,[],[f1072])).
% 25.79/3.63  fof(f9540,plain,(
% 25.79/3.63    spl2_101 | ~spl2_2 | ~spl2_28 | ~spl2_31 | ~spl2_39),
% 25.79/3.63    inference(avatar_split_clause,[],[f969,f875,f724,f684,f43,f9538])).
% 25.79/3.63  fof(f875,plain,(
% 25.79/3.63    spl2_39 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 25.79/3.63  fof(f969,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) ) | (~spl2_2 | ~spl2_28 | ~spl2_31 | ~spl2_39)),
% 25.79/3.63    inference(backward_demodulation,[],[f935,f959])).
% 25.79/3.63  fof(f959,plain,(
% 25.79/3.63    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = X4) ) | (~spl2_28 | ~spl2_31 | ~spl2_39)),
% 25.79/3.63    inference(forward_demodulation,[],[f937,f685])).
% 25.79/3.63  fof(f937,plain,(
% 25.79/3.63    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(X4,k1_xboole_0)) ) | (~spl2_31 | ~spl2_39)),
% 25.79/3.63    inference(superposition,[],[f876,f725])).
% 25.79/3.63  fof(f876,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | ~spl2_39),
% 25.79/3.63    inference(avatar_component_clause,[],[f875])).
% 25.79/3.63  fof(f935,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | (~spl2_2 | ~spl2_39)),
% 25.79/3.63    inference(superposition,[],[f876,f44])).
% 25.79/3.63  fof(f4454,plain,(
% 25.79/3.63    spl2_98 | ~spl2_42 | ~spl2_97),
% 25.79/3.63    inference(avatar_split_clause,[],[f4402,f4361,f1012,f4452])).
% 25.79/3.63  fof(f1012,plain,(
% 25.79/3.63    spl2_42 <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 25.79/3.63  fof(f4361,plain,(
% 25.79/3.63    spl2_97 <=> ! [X1,X0] : k5_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).
% 25.79/3.63  fof(f4402,plain,(
% 25.79/3.63    ( ! [X12,X11] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X12,X11))) ) | (~spl2_42 | ~spl2_97)),
% 25.79/3.63    inference(superposition,[],[f1013,f4362])).
% 25.79/3.63  fof(f4362,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) ) | ~spl2_97),
% 25.79/3.63    inference(avatar_component_clause,[],[f4361])).
% 25.79/3.63  fof(f1013,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) ) | ~spl2_42),
% 25.79/3.63    inference(avatar_component_clause,[],[f1012])).
% 25.79/3.63  fof(f4363,plain,(
% 25.79/3.63    spl2_97 | ~spl2_31 | ~spl2_76),
% 25.79/3.63    inference(avatar_split_clause,[],[f4254,f3306,f724,f4361])).
% 25.79/3.63  fof(f3306,plain,(
% 25.79/3.63    spl2_76 <=> ! [X9,X11,X10] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 25.79/3.63  fof(f4254,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl2_31 | ~spl2_76)),
% 25.79/3.63    inference(superposition,[],[f3307,f725])).
% 25.79/3.63  fof(f3307,plain,(
% 25.79/3.63    ( ! [X10,X11,X9] : (k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))) ) | ~spl2_76),
% 25.79/3.63    inference(avatar_component_clause,[],[f3306])).
% 25.79/3.63  fof(f3384,plain,(
% 25.79/3.63    spl2_95 | ~spl2_2 | ~spl2_46 | ~spl2_61),
% 25.79/3.63    inference(avatar_split_clause,[],[f2015,f1860,f1076,f43,f3382])).
% 25.79/3.63  fof(f2015,plain,(
% 25.79/3.63    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))) ) | (~spl2_2 | ~spl2_46 | ~spl2_61)),
% 25.79/3.63    inference(forward_demodulation,[],[f1992,f44])).
% 25.79/3.63  fof(f1992,plain,(
% 25.79/3.63    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12))) ) | (~spl2_46 | ~spl2_61)),
% 25.79/3.63    inference(superposition,[],[f1861,f1077])).
% 25.79/3.63  fof(f3380,plain,(
% 25.79/3.63    spl2_94 | ~spl2_45 | ~spl2_61),
% 25.79/3.63    inference(avatar_split_clause,[],[f2005,f1860,f1072,f3378])).
% 25.79/3.63  fof(f2005,plain,(
% 25.79/3.63    ( ! [X21,X22,X20] : (k5_xboole_0(X21,k5_xboole_0(X20,X22)) = k5_xboole_0(k5_xboole_0(X21,X22),X20)) ) | (~spl2_45 | ~spl2_61)),
% 25.79/3.63    inference(superposition,[],[f1073,f1861])).
% 25.79/3.63  fof(f3372,plain,(
% 25.79/3.63    spl2_92 | ~spl2_43 | ~spl2_61),
% 25.79/3.63    inference(avatar_split_clause,[],[f2003,f1860,f1040,f3370])).
% 25.79/3.63  fof(f1040,plain,(
% 25.79/3.63    spl2_43 <=> ! [X7,X6] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 25.79/3.63  fof(f2003,plain,(
% 25.79/3.63    ( ! [X14,X15,X16] : (k5_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X16)),k5_xboole_0(X15,X16)) = X14) ) | (~spl2_43 | ~spl2_61)),
% 25.79/3.63    inference(superposition,[],[f1041,f1861])).
% 25.79/3.63  fof(f1041,plain,(
% 25.79/3.63    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) ) | ~spl2_43),
% 25.79/3.63    inference(avatar_component_clause,[],[f1040])).
% 25.79/3.63  fof(f3328,plain,(
% 25.79/3.63    spl2_81 | ~spl2_45 | ~spl2_47),
% 25.79/3.63    inference(avatar_split_clause,[],[f1178,f1143,f1072,f3326])).
% 25.79/3.63  fof(f1178,plain,(
% 25.79/3.63    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | (~spl2_45 | ~spl2_47)),
% 25.79/3.63    inference(superposition,[],[f1073,f1144])).
% 25.79/3.63  fof(f3324,plain,(
% 25.79/3.63    spl2_80),
% 25.79/3.63    inference(avatar_split_clause,[],[f36,f3322])).
% 25.79/3.63  fof(f36,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 25.79/3.63    inference(definition_unfolding,[],[f28,f22,f22,f22])).
% 25.79/3.63  fof(f28,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 25.79/3.63    inference(cnf_transformation,[],[f9])).
% 25.79/3.63  fof(f9,axiom,(
% 25.79/3.63    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 25.79/3.63  fof(f3316,plain,(
% 25.79/3.63    spl2_78 | ~spl2_2 | ~spl2_46),
% 25.79/3.63    inference(avatar_split_clause,[],[f1122,f1076,f43,f3314])).
% 25.79/3.63  fof(f1122,plain,(
% 25.79/3.63    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)) ) | (~spl2_2 | ~spl2_46)),
% 25.79/3.63    inference(superposition,[],[f44,f1077])).
% 25.79/3.63  fof(f3312,plain,(
% 25.79/3.63    spl2_77 | ~spl2_2 | ~spl2_46),
% 25.79/3.63    inference(avatar_split_clause,[],[f1112,f1076,f43,f3310])).
% 25.79/3.63  fof(f3308,plain,(
% 25.79/3.63    spl2_76 | ~spl2_2 | ~spl2_45),
% 25.79/3.63    inference(avatar_split_clause,[],[f1110,f1072,f43,f3306])).
% 25.79/3.63  fof(f1110,plain,(
% 25.79/3.63    ( ! [X10,X11,X9] : (k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))) ) | (~spl2_2 | ~spl2_45)),
% 25.79/3.63    inference(superposition,[],[f44,f1073])).
% 25.79/3.63  fof(f3304,plain,(
% 25.79/3.63    spl2_75 | ~spl2_3 | ~spl2_45),
% 25.79/3.63    inference(avatar_split_clause,[],[f1100,f1072,f47,f3302])).
% 25.79/3.63  fof(f1100,plain,(
% 25.79/3.63    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(k4_xboole_0(X8,X9),X8)) ) | (~spl2_3 | ~spl2_45)),
% 25.79/3.63    inference(superposition,[],[f1073,f48])).
% 25.79/3.63  fof(f3163,plain,(
% 25.79/3.63    spl2_74 | ~spl2_56 | ~spl2_73),
% 25.79/3.63    inference(avatar_split_clause,[],[f3041,f2859,f1597,f3161])).
% 25.79/3.63  fof(f1597,plain,(
% 25.79/3.63    spl2_56 <=> ! [X9,X8] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 25.79/3.63  fof(f3041,plain,(
% 25.79/3.63    ( ! [X76,X77,X75] : (k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X75,k4_xboole_0(X76,X75)))) = X75) ) | (~spl2_56 | ~spl2_73)),
% 25.79/3.63    inference(superposition,[],[f2860,f1598])).
% 25.79/3.63  fof(f1598,plain,(
% 25.79/3.63    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9) ) | ~spl2_56),
% 25.79/3.63    inference(avatar_component_clause,[],[f1597])).
% 25.79/3.63  fof(f2861,plain,(
% 25.79/3.63    spl2_73 | ~spl2_32 | ~spl2_70),
% 25.79/3.63    inference(avatar_split_clause,[],[f2667,f2601,f738,f2859])).
% 25.79/3.63  fof(f738,plain,(
% 25.79/3.63    spl2_32 <=> ! [X5,X6] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 25.79/3.63  fof(f2667,plain,(
% 25.79/3.63    ( ! [X35,X36,X34] : (k4_xboole_0(X35,X36) = k4_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35))) ) | (~spl2_32 | ~spl2_70)),
% 25.79/3.63    inference(superposition,[],[f739,f2602])).
% 25.79/3.63  fof(f739,plain,(
% 25.79/3.63    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5) ) | ~spl2_32),
% 25.79/3.63    inference(avatar_component_clause,[],[f738])).
% 25.79/3.63  fof(f2603,plain,(
% 25.79/3.63    spl2_70 | ~spl2_32 | ~spl2_69),
% 25.79/3.63    inference(avatar_split_clause,[],[f2503,f2495,f738,f2601])).
% 25.79/3.63  fof(f2495,plain,(
% 25.79/3.63    spl2_69 <=> ! [X20,X22,X21] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 25.79/3.63  fof(f2503,plain,(
% 25.79/3.63    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))) ) | (~spl2_32 | ~spl2_69)),
% 25.79/3.63    inference(superposition,[],[f2496,f739])).
% 25.79/3.63  fof(f2496,plain,(
% 25.79/3.63    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21) ) | ~spl2_69),
% 25.79/3.63    inference(avatar_component_clause,[],[f2495])).
% 25.79/3.63  fof(f2497,plain,(
% 25.79/3.63    spl2_69 | ~spl2_1 | ~spl2_51 | ~spl2_67),
% 25.79/3.63    inference(avatar_split_clause,[],[f2449,f2344,f1205,f39,f2495])).
% 25.79/3.63  fof(f2344,plain,(
% 25.79/3.63    spl2_67 <=> ! [X27,X29,X28] : k4_xboole_0(X29,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X28,X29)))) = X29),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 25.79/3.63  fof(f2449,plain,(
% 25.79/3.63    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21) ) | (~spl2_1 | ~spl2_51 | ~spl2_67)),
% 25.79/3.63    inference(forward_demodulation,[],[f2380,f40])).
% 25.79/3.63  fof(f2380,plain,(
% 25.79/3.63    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21) ) | (~spl2_51 | ~spl2_67)),
% 25.79/3.63    inference(superposition,[],[f2345,f1206])).
% 25.79/3.63  fof(f2345,plain,(
% 25.79/3.63    ( ! [X28,X29,X27] : (k4_xboole_0(X29,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X28,X29)))) = X29) ) | ~spl2_67),
% 25.79/3.63    inference(avatar_component_clause,[],[f2344])).
% 25.79/3.63  fof(f2346,plain,(
% 25.79/3.63    spl2_67 | ~spl2_32 | ~spl2_54),
% 25.79/3.63    inference(avatar_split_clause,[],[f2219,f1538,f738,f2344])).
% 25.79/3.63  fof(f2219,plain,(
% 25.79/3.63    ( ! [X28,X29,X27] : (k4_xboole_0(X29,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X28,X29)))) = X29) ) | (~spl2_32 | ~spl2_54)),
% 25.79/3.63    inference(superposition,[],[f739,f1539])).
% 25.79/3.63  fof(f2166,plain,(
% 25.79/3.63    spl2_66 | ~spl2_2 | ~spl2_45),
% 25.79/3.63    inference(avatar_split_clause,[],[f1096,f1072,f43,f2164])).
% 25.79/3.63  fof(f1096,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2) ) | (~spl2_2 | ~spl2_45)),
% 25.79/3.63    inference(superposition,[],[f1073,f44])).
% 25.79/3.63  fof(f2154,plain,(
% 25.79/3.63    spl2_63 | ~spl2_2 | ~spl2_44),
% 25.79/3.63    inference(avatar_split_clause,[],[f1079,f1068,f43,f2152])).
% 25.79/3.63  fof(f1068,plain,(
% 25.79/3.63    spl2_44 <=> ! [X7,X6] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 25.79/3.63  fof(f1079,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2)) ) | (~spl2_2 | ~spl2_44)),
% 25.79/3.63    inference(superposition,[],[f1069,f44])).
% 25.79/3.63  fof(f1069,plain,(
% 25.79/3.63    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) ) | ~spl2_44),
% 25.79/3.63    inference(avatar_component_clause,[],[f1068])).
% 25.79/3.63  fof(f1862,plain,(
% 25.79/3.63    spl2_61 | ~spl2_2 | ~spl2_43),
% 25.79/3.63    inference(avatar_split_clause,[],[f1064,f1040,f43,f1860])).
% 25.79/3.63  fof(f1064,plain,(
% 25.79/3.63    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) ) | (~spl2_2 | ~spl2_43)),
% 25.79/3.63    inference(forward_demodulation,[],[f1054,f44])).
% 25.79/3.63  fof(f1054,plain,(
% 25.79/3.63    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) ) | (~spl2_2 | ~spl2_43)),
% 25.79/3.63    inference(superposition,[],[f44,f1041])).
% 25.79/3.63  fof(f1858,plain,(
% 25.79/3.63    spl2_60 | ~spl2_3 | ~spl2_43),
% 25.79/3.63    inference(avatar_split_clause,[],[f1045,f1040,f47,f1856])).
% 25.79/3.63  fof(f1045,plain,(
% 25.79/3.63    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5)) = X4) ) | (~spl2_3 | ~spl2_43)),
% 25.79/3.63    inference(superposition,[],[f1041,f48])).
% 25.79/3.63  fof(f1854,plain,(
% 25.79/3.63    spl2_59 | ~spl2_2 | ~spl2_43),
% 25.79/3.63    inference(avatar_split_clause,[],[f1043,f1040,f43,f1852])).
% 25.79/3.63  fof(f1043,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | (~spl2_2 | ~spl2_43)),
% 25.79/3.63    inference(superposition,[],[f1041,f44])).
% 25.79/3.63  fof(f1607,plain,(
% 25.79/3.63    spl2_58 | ~spl2_51 | ~spl2_53),
% 25.79/3.63    inference(avatar_split_clause,[],[f1503,f1469,f1205,f1605])).
% 25.79/3.63  fof(f1469,plain,(
% 25.79/3.63    spl2_53 <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X4)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 25.79/3.63  fof(f1503,plain,(
% 25.79/3.63    ( ! [X26,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X26,X25),k5_xboole_0(X25,k4_xboole_0(X26,X25)))) ) | (~spl2_51 | ~spl2_53)),
% 25.79/3.63    inference(superposition,[],[f1206,f1470])).
% 25.79/3.63  fof(f1470,plain,(
% 25.79/3.63    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X4)) ) | ~spl2_53),
% 25.79/3.63    inference(avatar_component_clause,[],[f1469])).
% 25.79/3.63  fof(f1599,plain,(
% 25.79/3.63    spl2_56 | ~spl2_6 | ~spl2_32 | ~spl2_35),
% 25.79/3.63    inference(avatar_split_clause,[],[f811,f787,f738,f59,f1597])).
% 25.79/3.63  fof(f811,plain,(
% 25.79/3.63    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9) ) | (~spl2_6 | ~spl2_32 | ~spl2_35)),
% 25.79/3.63    inference(forward_demodulation,[],[f804,f739])).
% 25.79/3.63  fof(f804,plain,(
% 25.79/3.63    ( ! [X8,X9] : (k4_xboole_0(X9,k4_xboole_0(X8,X9)) = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) ) | (~spl2_6 | ~spl2_35)),
% 25.79/3.63    inference(superposition,[],[f60,f788])).
% 25.79/3.63  fof(f1544,plain,(
% 25.79/3.63    spl2_55 | ~spl2_6 | ~spl2_30 | ~spl2_53),
% 25.79/3.63    inference(avatar_split_clause,[],[f1525,f1469,f720,f59,f1542])).
% 25.79/3.63  fof(f1525,plain,(
% 25.79/3.63    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9)))) ) | (~spl2_6 | ~spl2_30 | ~spl2_53)),
% 25.79/3.63    inference(forward_demodulation,[],[f1495,f721])).
% 25.79/3.63  fof(f1495,plain,(
% 25.79/3.63    ( ! [X10,X9] : (k4_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X10,X9))) = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),k5_xboole_0(X9,k4_xboole_0(X10,X9)))) ) | (~spl2_6 | ~spl2_53)),
% 25.79/3.63    inference(superposition,[],[f60,f1470])).
% 25.79/3.63  fof(f1540,plain,(
% 25.79/3.63    spl2_54),
% 25.79/3.63    inference(avatar_split_clause,[],[f35,f1538])).
% 25.79/3.63  fof(f1471,plain,(
% 25.79/3.63    spl2_53 | ~spl2_6 | ~spl2_32 | ~spl2_42 | ~spl2_43),
% 25.79/3.63    inference(avatar_split_clause,[],[f1063,f1040,f1012,f738,f59,f1469])).
% 25.79/3.63  fof(f1063,plain,(
% 25.79/3.63    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X4)) ) | (~spl2_6 | ~spl2_32 | ~spl2_42 | ~spl2_43)),
% 25.79/3.63    inference(backward_demodulation,[],[f765,f1053])).
% 25.79/3.63  fof(f1053,plain,(
% 25.79/3.63    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | (~spl2_42 | ~spl2_43)),
% 25.79/3.63    inference(superposition,[],[f1013,f1041])).
% 25.79/3.63  fof(f765,plain,(
% 25.79/3.63    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X5,X4),X4),X4)) ) | (~spl2_6 | ~spl2_32)),
% 25.79/3.63    inference(forward_demodulation,[],[f759,f754])).
% 25.79/3.63  fof(f754,plain,(
% 25.79/3.63    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)) ) | ~spl2_32),
% 25.79/3.63    inference(superposition,[],[f739,f739])).
% 25.79/3.63  fof(f759,plain,(
% 25.79/3.63    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X5,X4),X4),X4)) ) | (~spl2_6 | ~spl2_32)),
% 25.79/3.63    inference(superposition,[],[f60,f739])).
% 25.79/3.63  fof(f1207,plain,(
% 25.79/3.63    spl2_51 | ~spl2_4 | ~spl2_31 | ~spl2_47 | ~spl2_48),
% 25.79/3.63    inference(avatar_split_clause,[],[f1184,f1147,f1143,f724,f51,f1205])).
% 25.79/3.63  fof(f1184,plain,(
% 25.79/3.63    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) ) | (~spl2_4 | ~spl2_31 | ~spl2_47 | ~spl2_48)),
% 25.79/3.63    inference(forward_demodulation,[],[f1183,f725])).
% 25.79/3.63  fof(f1183,plain,(
% 25.79/3.63    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) ) | (~spl2_4 | ~spl2_47 | ~spl2_48)),
% 25.79/3.63    inference(forward_demodulation,[],[f1159,f1148])).
% 25.79/3.63  fof(f1159,plain,(
% 25.79/3.63    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) ) | (~spl2_4 | ~spl2_47)),
% 25.79/3.63    inference(superposition,[],[f1144,f52])).
% 25.79/3.63  fof(f1157,plain,(
% 25.79/3.63    spl2_50 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 25.79/3.63    inference(avatar_split_clause,[],[f162,f55,f51,f47,f1155])).
% 25.79/3.63  fof(f55,plain,(
% 25.79/3.63    spl2_5 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 25.79/3.63  fof(f162,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) ) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 25.79/3.63    inference(backward_demodulation,[],[f122,f152])).
% 25.79/3.63  fof(f152,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_4 | ~spl2_5)),
% 25.79/3.63    inference(superposition,[],[f56,f52])).
% 25.79/3.63  fof(f56,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_5),
% 25.79/3.63    inference(avatar_component_clause,[],[f55])).
% 25.79/3.63  fof(f122,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) ) | (~spl2_3 | ~spl2_4)),
% 25.79/3.63    inference(superposition,[],[f48,f52])).
% 25.79/3.63  fof(f1153,plain,(
% 25.79/3.63    spl2_49 | ~spl2_3 | ~spl2_5),
% 25.79/3.63    inference(avatar_split_clause,[],[f156,f55,f47,f1151])).
% 25.79/3.63  fof(f156,plain,(
% 25.79/3.63    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_3 | ~spl2_5)),
% 25.79/3.63    inference(superposition,[],[f48,f56])).
% 25.79/3.63  fof(f1149,plain,(
% 25.79/3.63    spl2_48 | ~spl2_4 | ~spl2_5),
% 25.79/3.63    inference(avatar_split_clause,[],[f152,f55,f51,f1147])).
% 25.79/3.63  fof(f1145,plain,(
% 25.79/3.63    spl2_47 | ~spl2_3 | ~spl2_4),
% 25.79/3.63    inference(avatar_split_clause,[],[f121,f51,f47,f1143])).
% 25.79/3.63  fof(f121,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_3 | ~spl2_4)),
% 25.79/3.63    inference(superposition,[],[f48,f52])).
% 25.79/3.63  fof(f1078,plain,(
% 25.79/3.63    spl2_46 | ~spl2_42 | ~spl2_43),
% 25.79/3.63    inference(avatar_split_clause,[],[f1053,f1040,f1012,f1076])).
% 25.79/3.63  fof(f1074,plain,(
% 25.79/3.63    spl2_45 | ~spl2_43),
% 25.79/3.63    inference(avatar_split_clause,[],[f1047,f1040,f1072])).
% 25.79/3.63  fof(f1047,plain,(
% 25.79/3.63    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) ) | ~spl2_43),
% 25.79/3.63    inference(superposition,[],[f1041,f1041])).
% 25.79/3.63  fof(f1070,plain,(
% 25.79/3.63    spl2_44 | ~spl2_42 | ~spl2_43),
% 25.79/3.63    inference(avatar_split_clause,[],[f1046,f1040,f1012,f1068])).
% 25.79/3.63  fof(f1046,plain,(
% 25.79/3.63    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) ) | (~spl2_42 | ~spl2_43)),
% 25.79/3.63    inference(superposition,[],[f1041,f1013])).
% 25.79/3.63  fof(f1042,plain,(
% 25.79/3.63    spl2_43 | ~spl2_28 | ~spl2_36 | ~spl2_42),
% 25.79/3.63    inference(avatar_split_clause,[],[f1031,f1012,f813,f684,f1040])).
% 25.79/3.63  fof(f813,plain,(
% 25.79/3.63    spl2_36 <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 25.79/3.63  fof(f1031,plain,(
% 25.79/3.63    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) ) | (~spl2_28 | ~spl2_36 | ~spl2_42)),
% 25.79/3.63    inference(forward_demodulation,[],[f1018,f685])).
% 25.79/3.63  fof(f1018,plain,(
% 25.79/3.63    ( ! [X6,X7] : (k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X7,k5_xboole_0(X6,X7))) ) | (~spl2_36 | ~spl2_42)),
% 25.79/3.63    inference(superposition,[],[f1013,f814])).
% 25.79/3.63  fof(f814,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | ~spl2_36),
% 25.79/3.63    inference(avatar_component_clause,[],[f813])).
% 25.79/3.63  fof(f1014,plain,(
% 25.79/3.63    spl2_42 | ~spl2_2 | ~spl2_28 | ~spl2_31 | ~spl2_37 | ~spl2_39),
% 25.79/3.63    inference(avatar_split_clause,[],[f971,f875,f842,f724,f684,f43,f1012])).
% 25.79/3.63  fof(f842,plain,(
% 25.79/3.63    spl2_37 <=> ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 25.79/3.63  fof(f971,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) ) | (~spl2_2 | ~spl2_28 | ~spl2_31 | ~spl2_37 | ~spl2_39)),
% 25.79/3.63    inference(forward_demodulation,[],[f965,f959])).
% 25.79/3.63  fof(f965,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) = X3) ) | (~spl2_2 | ~spl2_28 | ~spl2_31 | ~spl2_37 | ~spl2_39)),
% 25.79/3.63    inference(backward_demodulation,[],[f868,f959])).
% 25.79/3.63  fof(f868,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)))) ) | (~spl2_2 | ~spl2_37)),
% 25.79/3.63    inference(forward_demodulation,[],[f856,f44])).
% 25.79/3.63  fof(f856,plain,(
% 25.79/3.63    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3))) ) | (~spl2_2 | ~spl2_37)),
% 25.79/3.63    inference(superposition,[],[f44,f843])).
% 25.79/3.63  fof(f843,plain,(
% 25.79/3.63    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))) ) | ~spl2_37),
% 25.79/3.63    inference(avatar_component_clause,[],[f842])).
% 25.79/3.63  fof(f995,plain,(
% 25.79/3.63    spl2_41 | ~spl2_28 | ~spl2_31 | ~spl2_39),
% 25.79/3.63    inference(avatar_split_clause,[],[f959,f875,f724,f684,f993])).
% 25.79/3.63  fof(f877,plain,(
% 25.79/3.63    spl2_39 | ~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_18 | ~spl2_27),
% 25.79/3.63    inference(avatar_split_clause,[],[f612,f465,f214,f144,f109,f63,f43,f39,f875])).
% 25.79/3.63  fof(f63,plain,(
% 25.79/3.63    spl2_7 <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 25.79/3.63  fof(f109,plain,(
% 25.79/3.63    spl2_12 <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 25.79/3.63  fof(f144,plain,(
% 25.79/3.63    spl2_13 <=> ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 25.79/3.63  fof(f214,plain,(
% 25.79/3.63    spl2_18 <=> ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 25.79/3.63  fof(f465,plain,(
% 25.79/3.63    spl2_27 <=> ! [X10] : k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 25.79/3.63  fof(f612,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_18 | ~spl2_27)),
% 25.79/3.63    inference(backward_demodulation,[],[f257,f584])).
% 25.79/3.63  fof(f584,plain,(
% 25.79/3.63    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) ) | (~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_27)),
% 25.79/3.63    inference(backward_demodulation,[],[f145,f581])).
% 25.79/3.63  fof(f581,plain,(
% 25.79/3.63    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(X10,X10)) ) | (~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_27)),
% 25.79/3.63    inference(backward_demodulation,[],[f466,f580])).
% 25.79/3.63  fof(f580,plain,(
% 25.79/3.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | (~spl2_1 | ~spl2_7 | ~spl2_12)),
% 25.79/3.63    inference(forward_demodulation,[],[f546,f110])).
% 25.79/3.63  fof(f110,plain,(
% 25.79/3.63    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl2_12),
% 25.79/3.63    inference(avatar_component_clause,[],[f109])).
% 25.79/3.63  fof(f546,plain,(
% 25.79/3.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) ) | (~spl2_1 | ~spl2_7)),
% 25.79/3.63    inference(superposition,[],[f64,f40])).
% 25.79/3.63  fof(f64,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | ~spl2_7),
% 25.79/3.63    inference(avatar_component_clause,[],[f63])).
% 25.79/3.63  fof(f466,plain,(
% 25.79/3.63    ( ! [X10] : (k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10))) ) | ~spl2_27),
% 25.79/3.63    inference(avatar_component_clause,[],[f465])).
% 25.79/3.63  fof(f145,plain,(
% 25.79/3.63    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)) ) | ~spl2_13),
% 25.79/3.63    inference(avatar_component_clause,[],[f144])).
% 25.79/3.63  fof(f257,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_18)),
% 25.79/3.63    inference(superposition,[],[f44,f215])).
% 25.79/3.63  fof(f215,plain,(
% 25.79/3.63    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)) ) | ~spl2_18),
% 25.79/3.63    inference(avatar_component_clause,[],[f214])).
% 25.79/3.63  fof(f844,plain,(
% 25.79/3.63    spl2_37 | ~spl2_28 | ~spl2_36),
% 25.79/3.63    inference(avatar_split_clause,[],[f820,f813,f684,f842])).
% 25.79/3.63  fof(f820,plain,(
% 25.79/3.63    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))) ) | (~spl2_28 | ~spl2_36)),
% 25.79/3.63    inference(superposition,[],[f814,f685])).
% 25.79/3.63  fof(f815,plain,(
% 25.79/3.63    spl2_36 | ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_27),
% 25.79/3.63    inference(avatar_split_clause,[],[f621,f465,f176,f144,f109,f63,f51,f43,f39,f813])).
% 25.79/3.63  fof(f176,plain,(
% 25.79/3.63    spl2_15 <=> ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 25.79/3.63  fof(f621,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_27)),
% 25.79/3.63    inference(backward_demodulation,[],[f186,f584])).
% 25.79/3.63  fof(f186,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_12 | ~spl2_15)),
% 25.79/3.63    inference(forward_demodulation,[],[f185,f110])).
% 25.79/3.63  fof(f185,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_15)),
% 25.79/3.63    inference(forward_demodulation,[],[f179,f117])).
% 25.79/3.63  fof(f117,plain,(
% 25.79/3.63    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | (~spl2_1 | ~spl2_4)),
% 25.79/3.63    inference(superposition,[],[f52,f40])).
% 25.79/3.63  fof(f179,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | (~spl2_2 | ~spl2_15)),
% 25.79/3.63    inference(superposition,[],[f177,f44])).
% 25.79/3.63  fof(f177,plain,(
% 25.79/3.63    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) ) | ~spl2_15),
% 25.79/3.63    inference(avatar_component_clause,[],[f176])).
% 25.79/3.63  fof(f789,plain,(
% 25.79/3.63    spl2_35 | ~spl2_32),
% 25.79/3.63    inference(avatar_split_clause,[],[f754,f738,f787])).
% 25.79/3.63  fof(f749,plain,(
% 25.79/3.63    ~spl2_34),
% 25.79/3.63    inference(avatar_split_clause,[],[f30,f746])).
% 25.79/3.63  fof(f30,plain,(
% 25.79/3.63    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 25.79/3.63    inference(definition_unfolding,[],[f17,f21,f22])).
% 25.79/3.63  fof(f21,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 25.79/3.63    inference(cnf_transformation,[],[f11])).
% 25.79/3.63  fof(f11,axiom,(
% 25.79/3.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 25.79/3.63  fof(f17,plain,(
% 25.79/3.63    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 25.79/3.63    inference(cnf_transformation,[],[f16])).
% 25.79/3.63  fof(f16,plain,(
% 25.79/3.63    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 25.79/3.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 25.79/3.63  fof(f15,plain,(
% 25.79/3.63    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 25.79/3.63    introduced(choice_axiom,[])).
% 25.79/3.63  fof(f14,plain,(
% 25.79/3.63    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 25.79/3.63    inference(ennf_transformation,[],[f13])).
% 25.79/3.63  fof(f13,negated_conjecture,(
% 25.79/3.63    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 25.79/3.63    inference(negated_conjecture,[],[f12])).
% 25.79/3.63  fof(f12,conjecture,(
% 25.79/3.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 25.79/3.63  fof(f740,plain,(
% 25.79/3.63    spl2_32 | ~spl2_3 | ~spl2_7),
% 25.79/3.63    inference(avatar_split_clause,[],[f573,f63,f47,f738])).
% 25.79/3.63  fof(f573,plain,(
% 25.79/3.63    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5) ) | (~spl2_3 | ~spl2_7)),
% 25.79/3.63    inference(superposition,[],[f64,f48])).
% 25.79/3.63  fof(f726,plain,(
% 25.79/3.63    spl2_31 | ~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_18 | ~spl2_27),
% 25.79/3.63    inference(avatar_split_clause,[],[f609,f465,f214,f144,f109,f63,f39,f724])).
% 25.79/3.63  fof(f609,plain,(
% 25.79/3.63    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) ) | (~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_18 | ~spl2_27)),
% 25.79/3.63    inference(backward_demodulation,[],[f215,f584])).
% 25.79/3.63  fof(f722,plain,(
% 25.79/3.63    spl2_30 | ~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_27),
% 25.79/3.63    inference(avatar_split_clause,[],[f581,f465,f109,f63,f39,f720])).
% 25.79/3.63  fof(f686,plain,(
% 25.79/3.63    spl2_28 | ~spl2_1 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_27),
% 25.79/3.63    inference(avatar_split_clause,[],[f583,f465,f109,f74,f63,f39,f684])).
% 25.79/3.63  fof(f74,plain,(
% 25.79/3.63    spl2_8 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 25.79/3.63  fof(f583,plain,(
% 25.79/3.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_1 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_27)),
% 25.79/3.63    inference(backward_demodulation,[],[f75,f581])).
% 25.79/3.63  fof(f75,plain,(
% 25.79/3.63    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_8),
% 25.79/3.63    inference(avatar_component_clause,[],[f74])).
% 25.79/3.63  fof(f467,plain,(
% 25.79/3.63    spl2_27 | ~spl2_3 | ~spl2_20 | ~spl2_22),
% 25.79/3.63    inference(avatar_split_clause,[],[f354,f333,f300,f47,f465])).
% 25.79/3.63  fof(f300,plain,(
% 25.79/3.63    spl2_20 <=> ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 25.79/3.63  fof(f333,plain,(
% 25.79/3.63    spl2_22 <=> ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 25.79/3.63  fof(f354,plain,(
% 25.79/3.63    ( ! [X10] : (k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10))) ) | (~spl2_3 | ~spl2_20 | ~spl2_22)),
% 25.79/3.63    inference(forward_demodulation,[],[f352,f301])).
% 25.79/3.63  fof(f301,plain,(
% 25.79/3.63    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))) ) | ~spl2_20),
% 25.79/3.63    inference(avatar_component_clause,[],[f300])).
% 25.79/3.63  fof(f352,plain,(
% 25.79/3.63    ( ! [X10] : (k4_xboole_0(X10,X10) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X10,X10)))) ) | (~spl2_3 | ~spl2_22)),
% 25.79/3.63    inference(superposition,[],[f48,f334])).
% 25.79/3.63  fof(f334,plain,(
% 25.79/3.63    ( ! [X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))) ) | ~spl2_22),
% 25.79/3.63    inference(avatar_component_clause,[],[f333])).
% 25.79/3.63  fof(f335,plain,(
% 25.79/3.63    spl2_22 | ~spl2_1 | ~spl2_4 | ~spl2_12),
% 25.79/3.63    inference(avatar_split_clause,[],[f136,f109,f51,f39,f333])).
% 25.79/3.63  fof(f136,plain,(
% 25.79/3.63    ( ! [X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_12)),
% 25.79/3.63    inference(forward_demodulation,[],[f124,f40])).
% 25.79/3.63  fof(f124,plain,(
% 25.79/3.63    ( ! [X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)))) ) | (~spl2_4 | ~spl2_12)),
% 25.79/3.63    inference(superposition,[],[f110,f52])).
% 25.79/3.63  fof(f302,plain,(
% 25.79/3.63    spl2_20 | ~spl2_5 | ~spl2_19),
% 25.79/3.63    inference(avatar_split_clause,[],[f286,f263,f55,f300])).
% 25.79/3.63  fof(f263,plain,(
% 25.79/3.63    spl2_19 <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 25.79/3.63  fof(f286,plain,(
% 25.79/3.63    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))) ) | (~spl2_5 | ~spl2_19)),
% 25.79/3.63    inference(superposition,[],[f56,f264])).
% 25.79/3.63  fof(f264,plain,(
% 25.79/3.63    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | ~spl2_19),
% 25.79/3.63    inference(avatar_component_clause,[],[f263])).
% 25.79/3.63  fof(f265,plain,(
% 25.79/3.63    spl2_19 | ~spl2_1 | ~spl2_4),
% 25.79/3.63    inference(avatar_split_clause,[],[f117,f51,f39,f263])).
% 25.79/3.63  fof(f216,plain,(
% 25.79/3.63    spl2_18 | ~spl2_3 | ~spl2_13 | ~spl2_14),
% 25.79/3.63    inference(avatar_split_clause,[],[f204,f164,f144,f47,f214])).
% 25.79/3.63  fof(f164,plain,(
% 25.79/3.63    spl2_14 <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 25.79/3.63  fof(f204,plain,(
% 25.79/3.63    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)) ) | (~spl2_3 | ~spl2_13 | ~spl2_14)),
% 25.79/3.63    inference(forward_demodulation,[],[f198,f195])).
% 25.79/3.63  fof(f195,plain,(
% 25.79/3.63    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) ) | (~spl2_13 | ~spl2_14)),
% 25.79/3.63    inference(superposition,[],[f165,f145])).
% 25.79/3.63  fof(f165,plain,(
% 25.79/3.63    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_14),
% 25.79/3.63    inference(avatar_component_clause,[],[f164])).
% 25.79/3.63  fof(f198,plain,(
% 25.79/3.63    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,X5)))) ) | (~spl2_3 | ~spl2_13)),
% 25.79/3.63    inference(superposition,[],[f48,f145])).
% 25.79/3.63  fof(f178,plain,(
% 25.79/3.63    spl2_15 | ~spl2_3 | ~spl2_14),
% 25.79/3.63    inference(avatar_split_clause,[],[f169,f164,f47,f176])).
% 25.79/3.63  fof(f169,plain,(
% 25.79/3.63    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) ) | (~spl2_3 | ~spl2_14)),
% 25.79/3.63    inference(superposition,[],[f48,f165])).
% 25.79/3.63  fof(f166,plain,(
% 25.79/3.63    spl2_14 | ~spl2_1 | ~spl2_5),
% 25.79/3.63    inference(avatar_split_clause,[],[f147,f55,f39,f164])).
% 25.79/3.63  fof(f147,plain,(
% 25.79/3.63    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_1 | ~spl2_5)),
% 25.79/3.63    inference(superposition,[],[f56,f40])).
% 25.79/3.63  fof(f146,plain,(
% 25.79/3.63    spl2_13 | ~spl2_1 | ~spl2_4 | ~spl2_12),
% 25.79/3.63    inference(avatar_split_clause,[],[f133,f109,f51,f39,f144])).
% 25.79/3.63  fof(f133,plain,(
% 25.79/3.63    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)) ) | (~spl2_1 | ~spl2_4 | ~spl2_12)),
% 25.79/3.63    inference(forward_demodulation,[],[f118,f40])).
% 25.79/3.63  fof(f118,plain,(
% 25.79/3.63    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) ) | (~spl2_4 | ~spl2_12)),
% 25.79/3.63    inference(superposition,[],[f52,f110])).
% 25.79/3.63  fof(f111,plain,(
% 25.79/3.63    spl2_12 | ~spl2_3 | ~spl2_11),
% 25.79/3.63    inference(avatar_split_clause,[],[f102,f98,f47,f109])).
% 25.79/3.63  fof(f98,plain,(
% 25.79/3.63    spl2_11 <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 25.79/3.63  fof(f102,plain,(
% 25.79/3.63    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | (~spl2_3 | ~spl2_11)),
% 25.79/3.63    inference(superposition,[],[f99,f48])).
% 25.79/3.63  fof(f99,plain,(
% 25.79/3.63    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl2_11),
% 25.79/3.63    inference(avatar_component_clause,[],[f98])).
% 25.79/3.63  fof(f100,plain,(
% 25.79/3.63    spl2_11 | ~spl2_3 | ~spl2_10),
% 25.79/3.63    inference(avatar_split_clause,[],[f93,f88,f47,f98])).
% 25.79/3.63  fof(f88,plain,(
% 25.79/3.63    spl2_10 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 25.79/3.63  fof(f93,plain,(
% 25.79/3.63    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | (~spl2_3 | ~spl2_10)),
% 25.79/3.63    inference(superposition,[],[f89,f48])).
% 25.79/3.63  fof(f89,plain,(
% 25.79/3.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | ~spl2_10),
% 25.79/3.63    inference(avatar_component_clause,[],[f88])).
% 25.79/3.63  fof(f90,plain,(
% 25.79/3.63    spl2_10 | ~spl2_2 | ~spl2_9),
% 25.79/3.63    inference(avatar_split_clause,[],[f86,f82,f43,f88])).
% 25.79/3.63  fof(f82,plain,(
% 25.79/3.63    spl2_9 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 25.79/3.63    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 25.79/3.63  fof(f86,plain,(
% 25.79/3.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | (~spl2_2 | ~spl2_9)),
% 25.79/3.63    inference(superposition,[],[f44,f84])).
% 25.79/3.63  fof(f84,plain,(
% 25.79/3.63    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_9),
% 25.79/3.63    inference(avatar_component_clause,[],[f82])).
% 25.79/3.63  fof(f85,plain,(
% 25.79/3.63    spl2_9 | ~spl2_1 | ~spl2_8),
% 25.79/3.63    inference(avatar_split_clause,[],[f77,f74,f39,f82])).
% 25.79/3.63  fof(f77,plain,(
% 25.79/3.63    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl2_1 | ~spl2_8)),
% 25.79/3.63    inference(superposition,[],[f75,f40])).
% 25.79/3.63  fof(f76,plain,(
% 25.79/3.63    spl2_8 | ~spl2_1 | ~spl2_3),
% 25.79/3.63    inference(avatar_split_clause,[],[f69,f47,f39,f74])).
% 25.79/3.63  fof(f69,plain,(
% 25.79/3.63    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_1 | ~spl2_3)),
% 25.79/3.63    inference(superposition,[],[f48,f40])).
% 25.79/3.63  fof(f65,plain,(
% 25.79/3.63    spl2_7),
% 25.79/3.63    inference(avatar_split_clause,[],[f37,f63])).
% 25.79/3.63  fof(f37,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 25.79/3.63    inference(backward_demodulation,[],[f32,f35])).
% 25.79/3.63  fof(f32,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 25.79/3.63    inference(definition_unfolding,[],[f20,f21,f22])).
% 25.79/3.63  fof(f20,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 25.79/3.63    inference(cnf_transformation,[],[f3])).
% 25.79/3.63  fof(f3,axiom,(
% 25.79/3.63    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 25.79/3.63  fof(f61,plain,(
% 25.79/3.63    spl2_6),
% 25.79/3.63    inference(avatar_split_clause,[],[f34,f59])).
% 25.79/3.63  fof(f34,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 25.79/3.63    inference(definition_unfolding,[],[f25,f21])).
% 25.79/3.63  fof(f25,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 25.79/3.63    inference(cnf_transformation,[],[f5])).
% 25.79/3.63  fof(f5,axiom,(
% 25.79/3.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 25.79/3.63  fof(f57,plain,(
% 25.79/3.63    spl2_5),
% 25.79/3.63    inference(avatar_split_clause,[],[f33,f55])).
% 25.79/3.63  fof(f33,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 25.79/3.63    inference(definition_unfolding,[],[f24,f22])).
% 25.79/3.63  fof(f24,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 25.79/3.63    inference(cnf_transformation,[],[f6])).
% 25.79/3.63  fof(f6,axiom,(
% 25.79/3.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 25.79/3.63  fof(f53,plain,(
% 25.79/3.63    spl2_4),
% 25.79/3.63    inference(avatar_split_clause,[],[f31,f51])).
% 25.79/3.63  fof(f31,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 25.79/3.63    inference(definition_unfolding,[],[f19,f22,f22])).
% 25.79/3.63  fof(f19,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 25.79/3.63    inference(cnf_transformation,[],[f1])).
% 25.79/3.63  fof(f1,axiom,(
% 25.79/3.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 25.79/3.63  fof(f49,plain,(
% 25.79/3.63    spl2_3),
% 25.79/3.63    inference(avatar_split_clause,[],[f29,f47])).
% 25.79/3.63  fof(f29,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 25.79/3.63    inference(definition_unfolding,[],[f23,f22])).
% 25.79/3.63  fof(f23,plain,(
% 25.79/3.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 25.79/3.63    inference(cnf_transformation,[],[f2])).
% 25.79/3.63  fof(f2,axiom,(
% 25.79/3.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 25.79/3.63  fof(f45,plain,(
% 25.79/3.63    spl2_2),
% 25.79/3.63    inference(avatar_split_clause,[],[f26,f43])).
% 25.79/3.63  fof(f26,plain,(
% 25.79/3.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 25.79/3.63    inference(cnf_transformation,[],[f10])).
% 25.79/3.63  fof(f10,axiom,(
% 25.79/3.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 25.79/3.63  fof(f41,plain,(
% 25.79/3.63    spl2_1),
% 25.79/3.63    inference(avatar_split_clause,[],[f18,f39])).
% 25.79/3.63  fof(f18,plain,(
% 25.79/3.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 25.79/3.63    inference(cnf_transformation,[],[f4])).
% 25.79/3.63  fof(f4,axiom,(
% 25.79/3.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 25.79/3.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 25.79/3.63  % SZS output end Proof for theBenchmark
% 25.79/3.63  % (1162)------------------------------
% 25.79/3.63  % (1162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.79/3.63  % (1162)Termination reason: Refutation
% 25.79/3.63  
% 25.79/3.63  % (1162)Memory used [KB]: 102855
% 25.79/3.63  % (1162)Time elapsed: 3.207 s
% 25.79/3.63  % (1162)------------------------------
% 25.79/3.63  % (1162)------------------------------
% 25.79/3.64  % (1153)Success in time 3.283 s
%------------------------------------------------------------------------------
