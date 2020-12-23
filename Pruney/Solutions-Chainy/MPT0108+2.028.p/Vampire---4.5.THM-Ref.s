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
% DateTime   : Thu Dec  3 12:32:21 EST 2020

% Result     : Theorem 28.79s
% Output     : Refutation 28.79s
% Verified   : 
% Statistics : Number of formulae       :  385 (1183 expanded)
%              Number of leaves         :   81 ( 581 expanded)
%              Depth                    :   13
%              Number of atoms          : 1246 (2983 expanded)
%              Number of equality atoms :  315 (1113 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53877,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f56,f60,f64,f68,f85,f94,f99,f111,f115,f147,f160,f176,f306,f354,f480,f511,f615,f721,f862,f1366,f1383,f1428,f1436,f1457,f1477,f1482,f1507,f1511,f1588,f1592,f1596,f1600,f1604,f1608,f1612,f2087,f2601,f2605,f2617,f2706,f2710,f3581,f3585,f3902,f3910,f5073,f5231,f5368,f6750,f8691,f10707,f14036,f14060,f26179,f32824,f37425,f45327,f47974,f48562,f50614,f51199,f51893,f52770,f53364,f53758])).

fof(f53758,plain,
    ( ~ spl2_3
    | spl2_55
    | ~ spl2_63
    | ~ spl2_73
    | ~ spl2_80
    | ~ spl2_203 ),
    inference(avatar_contradiction_clause,[],[f53757])).

fof(f53757,plain,
    ( $false
    | ~ spl2_3
    | spl2_55
    | ~ spl2_63
    | ~ spl2_73
    | ~ spl2_80
    | ~ spl2_203 ),
    inference(subsumption_resolution,[],[f1481,f53756])).

fof(f53756,plain,
    ( ! [X80,X79] : k5_xboole_0(X79,X80) = k4_xboole_0(k5_xboole_0(X79,k4_xboole_0(X80,X79)),k5_xboole_0(X79,k4_xboole_0(X79,X80)))
    | ~ spl2_3
    | ~ spl2_63
    | ~ spl2_73
    | ~ spl2_80
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f53512,f53707])).

fof(f53707,plain,
    ( ! [X52,X53] : k5_xboole_0(X52,k4_xboole_0(X52,X53)) = k4_xboole_0(X52,k5_xboole_0(X52,X53))
    | ~ spl2_3
    | ~ spl2_63
    | ~ spl2_73
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f53706,f2785])).

fof(f2785,plain,
    ( ! [X35,X33,X34] : k5_xboole_0(X33,k5_xboole_0(X35,k5_xboole_0(X34,k4_xboole_0(X34,X33)))) = k5_xboole_0(X35,k4_xboole_0(X33,X34))
    | ~ spl2_63
    | ~ spl2_73 ),
    inference(superposition,[],[f2604,f1603])).

fof(f1603,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f1602])).

fof(f1602,plain,
    ( spl2_63
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f2604,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f2603])).

fof(f2603,plain,
    ( spl2_73
  <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f53706,plain,
    ( ! [X52,X53] : k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(X52,k5_xboole_0(X53,k4_xboole_0(X53,X52))))
    | ~ spl2_3
    | ~ spl2_63
    | ~ spl2_203 ),
    inference(forward_demodulation,[],[f53499,f47])).

fof(f47,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_3
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53499,plain,
    ( ! [X52,X53] : k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X53,X52)))
    | ~ spl2_63
    | ~ spl2_203 ),
    inference(superposition,[],[f1603,f53363])).

fof(f53363,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)
    | ~ spl2_203 ),
    inference(avatar_component_clause,[],[f53362])).

fof(f53362,plain,
    ( spl2_203
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).

fof(f53512,plain,
    ( ! [X80,X79] : k5_xboole_0(X79,X80) = k4_xboole_0(k5_xboole_0(X79,k4_xboole_0(X80,X79)),k4_xboole_0(X79,k5_xboole_0(X79,X80)))
    | ~ spl2_80
    | ~ spl2_203 ),
    inference(superposition,[],[f3580,f53363])).

fof(f3580,plain,
    ( ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f3579])).

fof(f3579,plain,
    ( spl2_80
  <=> ! [X1,X0] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f1481,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_55 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1479,plain,
    ( spl2_55
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f53364,plain,
    ( spl2_203
    | ~ spl2_2
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f52772,f52768,f42,f53362])).

fof(f42,plain,
    ( spl2_2
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52768,plain,
    ( spl2_202
  <=> ! [X40,X41] : k4_xboole_0(X40,X41) = k4_xboole_0(k5_xboole_0(X40,X41),X41) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_202])])).

fof(f52772,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)
    | ~ spl2_2
    | ~ spl2_202 ),
    inference(superposition,[],[f52769,f43])).

fof(f43,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f52769,plain,
    ( ! [X41,X40] : k4_xboole_0(X40,X41) = k4_xboole_0(k5_xboole_0(X40,X41),X41)
    | ~ spl2_202 ),
    inference(avatar_component_clause,[],[f52768])).

fof(f52770,plain,
    ( spl2_202
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_63
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_96
    | ~ spl2_149
    | ~ spl2_195
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(avatar_split_clause,[],[f52454,f51891,f50612,f48560,f26177,f5366,f2708,f1610,f1602,f1505,f1475,f1364,f54,f42,f38,f52768])).

fof(f38,plain,
    ( spl2_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f54,plain,
    ( spl2_5
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1364,plain,
    ( spl2_47
  <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f1475,plain,
    ( spl2_54
  <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f1505,plain,
    ( spl2_56
  <=> ! [X7,X8] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f1610,plain,
    ( spl2_65
  <=> ! [X5,X6] : k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X6,k4_xboole_0(X6,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f2708,plain,
    ( spl2_78
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f5366,plain,
    ( spl2_96
  <=> ! [X15,X14] : k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X15,X14),k4_xboole_0(X14,X15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f26177,plain,
    ( spl2_149
  <=> ! [X3,X4] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).

fof(f48560,plain,
    ( spl2_195
  <=> ! [X13,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X13,X12),X12),X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).

fof(f50612,plain,
    ( spl2_199
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).

fof(f51891,plain,
    ( spl2_201
  <=> ! [X16,X17] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_201])])).

fof(f52454,plain,
    ( ! [X41,X40] : k4_xboole_0(X40,X41) = k4_xboole_0(k5_xboole_0(X40,X41),X41)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_63
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_96
    | ~ spl2_149
    | ~ spl2_195
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(forward_demodulation,[],[f52453,f39])).

fof(f39,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f52453,plain,
    ( ! [X41,X40] : k4_xboole_0(k4_xboole_0(X40,X41),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X40,X41),X41)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_63
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_96
    | ~ spl2_149
    | ~ spl2_195
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(forward_demodulation,[],[f52452,f51130])).

fof(f51130,plain,
    ( ! [X194,X195] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X194,X195),k4_xboole_0(k5_xboole_0(X194,X195),X195))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_63
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_96
    | ~ spl2_149
    | ~ spl2_195
    | ~ spl2_199 ),
    inference(forward_demodulation,[],[f51129,f1365])).

fof(f1365,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f1364])).

fof(f51129,plain,
    ( ! [X194,X195] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X194,X195)),k4_xboole_0(k5_xboole_0(X194,X195),X195))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_63
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_96
    | ~ spl2_149
    | ~ spl2_195
    | ~ spl2_199 ),
    inference(forward_demodulation,[],[f51128,f43])).

fof(f51128,plain,
    ( ! [X194,X195] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k4_xboole_0(k5_xboole_0(X194,X195),X195))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_63
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_96
    | ~ spl2_149
    | ~ spl2_195
    | ~ spl2_199 ),
    inference(forward_demodulation,[],[f51127,f6563])).

fof(f6563,plain,
    ( ! [X48,X49] : k4_xboole_0(k5_xboole_0(X48,X49),X49) = k5_xboole_0(X48,k4_xboole_0(X49,k5_xboole_0(X48,X49)))
    | ~ spl2_56
    | ~ spl2_96 ),
    inference(superposition,[],[f5367,f1506])).

fof(f1506,plain,
    ( ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f1505])).

fof(f5367,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X15,X14),k4_xboole_0(X14,X15))
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f5366])).

fof(f51127,plain,
    ( ! [X194,X195] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k5_xboole_0(X194,k4_xboole_0(X195,k5_xboole_0(X194,X195))))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_63
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_96
    | ~ spl2_149
    | ~ spl2_195
    | ~ spl2_199 ),
    inference(forward_demodulation,[],[f51126,f49412])).

fof(f49412,plain,
    ( ! [X54,X53] : k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k4_xboole_0(X54,k5_xboole_0(X53,X54))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_54
    | ~ spl2_63
    | ~ spl2_96
    | ~ spl2_195 ),
    inference(forward_demodulation,[],[f49411,f6547])).

fof(f6547,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,k5_xboole_0(X10,X9)) = k5_xboole_0(X10,k4_xboole_0(k5_xboole_0(X10,X9),X9))
    | ~ spl2_54
    | ~ spl2_96 ),
    inference(superposition,[],[f5367,f1476])).

fof(f1476,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f1475])).

fof(f49411,plain,
    ( ! [X54,X53] : k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k5_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_63
    | ~ spl2_195 ),
    inference(forward_demodulation,[],[f49410,f1365])).

fof(f49410,plain,
    ( ! [X54,X53] : k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k5_xboole_0(X53,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X53,X54),X54)))
    | ~ spl2_2
    | ~ spl2_63
    | ~ spl2_195 ),
    inference(forward_demodulation,[],[f49219,f43])).

fof(f49219,plain,
    ( ! [X54,X53] : k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k5_xboole_0(X53,k5_xboole_0(k4_xboole_0(k5_xboole_0(X53,X54),X54),k1_xboole_0))
    | ~ spl2_63
    | ~ spl2_195 ),
    inference(superposition,[],[f1603,f48561])).

fof(f48561,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X13,X12),X12),X13)
    | ~ spl2_195 ),
    inference(avatar_component_clause,[],[f48560])).

fof(f51126,plain,
    ( ! [X194,X195] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k5_xboole_0(X194,k4_xboole_0(X194,k4_xboole_0(k5_xboole_0(X194,X195),X195))))
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_149
    | ~ spl2_199 ),
    inference(forward_demodulation,[],[f51125,f2709])).

fof(f2709,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f2708])).

fof(f51125,plain,
    ( ! [X194,X195] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k4_xboole_0(k5_xboole_0(X194,k4_xboole_0(X194,k5_xboole_0(X194,X195))),X195))
    | ~ spl2_65
    | ~ spl2_78
    | ~ spl2_149
    | ~ spl2_199 ),
    inference(forward_demodulation,[],[f50860,f4644])).

fof(f4644,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2)
    | ~ spl2_65
    | ~ spl2_78 ),
    inference(superposition,[],[f2709,f1611])).

fof(f1611,plain,
    ( ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X6,k4_xboole_0(X6,X5))
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f1610])).

fof(f50860,plain,
    ( ! [X194,X195] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k5_xboole_0(k5_xboole_0(X194,X195),k4_xboole_0(k5_xboole_0(X194,X195),k4_xboole_0(X194,X195))))
    | ~ spl2_149
    | ~ spl2_199 ),
    inference(superposition,[],[f26178,f50613])).

fof(f50613,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl2_199 ),
    inference(avatar_component_clause,[],[f50612])).

fof(f26178,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))
    | ~ spl2_149 ),
    inference(avatar_component_clause,[],[f26177])).

fof(f52452,plain,
    ( ! [X41,X40] : k4_xboole_0(k5_xboole_0(X40,X41),X41) = k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k5_xboole_0(X40,X41),X41)))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_201 ),
    inference(forward_demodulation,[],[f52085,f39])).

fof(f52085,plain,
    ( ! [X41,X40] : k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k5_xboole_0(X40,X41),X41))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X40,X41),X41),k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_201 ),
    inference(superposition,[],[f55,f51892])).

fof(f51892,plain,
    ( ! [X17,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17))
    | ~ spl2_201 ),
    inference(avatar_component_clause,[],[f51891])).

fof(f55,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f51893,plain,
    ( spl2_201
    | ~ spl2_174
    | ~ spl2_200 ),
    inference(avatar_split_clause,[],[f51374,f51197,f37423,f51891])).

fof(f37423,plain,
    ( spl2_174
  <=> ! [X44,X43,X45] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X43,k4_xboole_0(X44,X45))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).

fof(f51197,plain,
    ( spl2_200
  <=> ! [X65,X64] : k4_xboole_0(X64,X65) = k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_200])])).

fof(f51374,plain,
    ( ! [X17,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17))
    | ~ spl2_174
    | ~ spl2_200 ),
    inference(superposition,[],[f37424,f51198])).

fof(f51198,plain,
    ( ! [X64,X65] : k4_xboole_0(X64,X65) = k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64))
    | ~ spl2_200 ),
    inference(avatar_component_clause,[],[f51197])).

fof(f37424,plain,
    ( ! [X45,X43,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X43,k4_xboole_0(X44,X45)))
    | ~ spl2_174 ),
    inference(avatar_component_clause,[],[f37423])).

fof(f51199,plain,
    ( spl2_200
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_96
    | ~ spl2_111
    | ~ spl2_185 ),
    inference(avatar_split_clause,[],[f47777,f45325,f8689,f5366,f1364,f42,f51197])).

fof(f8689,plain,
    ( spl2_111
  <=> ! [X20,X19] : k5_xboole_0(X19,X20) = k5_xboole_0(k4_xboole_0(X20,X19),k4_xboole_0(X19,X20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).

fof(f45325,plain,
    ( spl2_185
  <=> ! [X69,X68,X70] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_185])])).

fof(f47777,plain,
    ( ! [X64,X65] : k4_xboole_0(X64,X65) = k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_96
    | ~ spl2_111
    | ~ spl2_185 ),
    inference(forward_demodulation,[],[f47776,f1365])).

fof(f47776,plain,
    ( ! [X64,X65] : k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X64,X65))
    | ~ spl2_2
    | ~ spl2_96
    | ~ spl2_111
    | ~ spl2_185 ),
    inference(forward_demodulation,[],[f47773,f43])).

fof(f47773,plain,
    ( ! [X64,X65] : k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64)) = k5_xboole_0(k4_xboole_0(X64,X65),k1_xboole_0)
    | ~ spl2_96
    | ~ spl2_111
    | ~ spl2_185 ),
    inference(backward_demodulation,[],[f6569,f47515])).

fof(f47515,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))
    | ~ spl2_111
    | ~ spl2_185 ),
    inference(superposition,[],[f45326,f8690])).

fof(f8690,plain,
    ( ! [X19,X20] : k5_xboole_0(X19,X20) = k5_xboole_0(k4_xboole_0(X20,X19),k4_xboole_0(X19,X20))
    | ~ spl2_111 ),
    inference(avatar_component_clause,[],[f8689])).

fof(f45326,plain,
    ( ! [X70,X68,X69] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))
    | ~ spl2_185 ),
    inference(avatar_component_clause,[],[f45325])).

fof(f6569,plain,
    ( ! [X64,X65] : k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64)) = k5_xboole_0(k4_xboole_0(X64,X65),k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,X65)))
    | ~ spl2_96 ),
    inference(superposition,[],[f5367,f5367])).

fof(f50614,plain,
    ( spl2_199
    | ~ spl2_143
    | ~ spl2_185 ),
    inference(avatar_split_clause,[],[f47514,f45325,f14058,f50612])).

fof(f14058,plain,
    ( spl2_143
  <=> ! [X25,X26] : k5_xboole_0(X26,X25) = k5_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,X26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).

fof(f47514,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl2_143
    | ~ spl2_185 ),
    inference(superposition,[],[f45326,f14059])).

fof(f14059,plain,
    ( ! [X26,X25] : k5_xboole_0(X26,X25) = k5_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,X26))
    | ~ spl2_143 ),
    inference(avatar_component_clause,[],[f14058])).

fof(f48562,plain,
    ( spl2_195
    | ~ spl2_54
    | ~ spl2_193 ),
    inference(avatar_split_clause,[],[f48047,f47972,f1475,f48560])).

fof(f47972,plain,
    ( spl2_193
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).

fof(f48047,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X13,X12),X12),X13)
    | ~ spl2_54
    | ~ spl2_193 ),
    inference(superposition,[],[f47973,f1476])).

fof(f47973,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))
    | ~ spl2_193 ),
    inference(avatar_component_clause,[],[f47972])).

fof(f47974,plain,
    ( spl2_193
    | ~ spl2_111
    | ~ spl2_185 ),
    inference(avatar_split_clause,[],[f47515,f45325,f8689,f47972])).

fof(f45327,plain,
    ( spl2_185
    | ~ spl2_77
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f6836,f6748,f2704,f45325])).

fof(f2704,plain,
    ( spl2_77
  <=> ! [X7,X8] : k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f6748,plain,
    ( spl2_98
  <=> ! [X32,X31,X30] : k4_xboole_0(X31,X30) = k4_xboole_0(k4_xboole_0(X31,X30),k4_xboole_0(X30,X32)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f6836,plain,
    ( ! [X70,X68,X69] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))
    | ~ spl2_77
    | ~ spl2_98 ),
    inference(superposition,[],[f2705,f6749])).

fof(f6749,plain,
    ( ! [X30,X31,X32] : k4_xboole_0(X31,X30) = k4_xboole_0(k4_xboole_0(X31,X30),k4_xboole_0(X30,X32))
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f6748])).

fof(f2705,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7)))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f2704])).

fof(f37425,plain,
    ( spl2_174
    | ~ spl2_34
    | ~ spl2_61
    | ~ spl2_78
    | ~ spl2_118
    | ~ spl2_137
    | ~ spl2_167 ),
    inference(avatar_split_clause,[],[f37154,f32822,f14034,f10705,f2708,f1594,f613,f37423])).

fof(f613,plain,
    ( spl2_34
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f1594,plain,
    ( spl2_61
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f10705,plain,
    ( spl2_118
  <=> ! [X16,X15,X14] : k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X16))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).

fof(f14034,plain,
    ( spl2_137
  <=> ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X22)),X22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).

fof(f32822,plain,
    ( spl2_167
  <=> ! [X69,X68,X70] : k1_xboole_0 = k4_xboole_0(X70,k5_xboole_0(X70,k5_xboole_0(X68,k4_xboole_0(X68,k4_xboole_0(X69,X70))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).

fof(f37154,plain,
    ( ! [X45,X43,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X43,k4_xboole_0(X44,X45)))
    | ~ spl2_34
    | ~ spl2_61
    | ~ spl2_78
    | ~ spl2_118
    | ~ spl2_137
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f37153,f614])).

fof(f614,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f613])).

fof(f37153,plain,
    ( ! [X45,X43,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(X43,k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X44,X45)))))
    | ~ spl2_61
    | ~ spl2_78
    | ~ spl2_118
    | ~ spl2_137
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f37152,f2709])).

fof(f37152,plain,
    ( ! [X45,X43,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(X43,k4_xboole_0(k5_xboole_0(X43,k4_xboole_0(X43,X44)),X45)))
    | ~ spl2_61
    | ~ spl2_118
    | ~ spl2_137
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f36949,f20673])).

fof(f20673,plain,
    ( ! [X269,X268,X270] : k5_xboole_0(X270,k5_xboole_0(X268,k4_xboole_0(X268,k5_xboole_0(X269,X270)))) = k5_xboole_0(X269,k4_xboole_0(k5_xboole_0(X269,X270),X268))
    | ~ spl2_118
    | ~ spl2_137 ),
    inference(superposition,[],[f10706,f14035])).

fof(f14035,plain,
    ( ! [X23,X22] : k4_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X22)),X22)
    | ~ spl2_137 ),
    inference(avatar_component_clause,[],[f14034])).

fof(f10706,plain,
    ( ! [X14,X15,X16] : k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X16)))
    | ~ spl2_118 ),
    inference(avatar_component_clause,[],[f10705])).

fof(f36949,plain,
    ( ! [X45,X43,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(X45,k4_xboole_0(X45,k5_xboole_0(X43,k4_xboole_0(X43,X44))))))
    | ~ spl2_61
    | ~ spl2_167 ),
    inference(superposition,[],[f32823,f1595])).

fof(f1595,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f1594])).

fof(f32823,plain,
    ( ! [X70,X68,X69] : k1_xboole_0 = k4_xboole_0(X70,k5_xboole_0(X70,k5_xboole_0(X68,k4_xboole_0(X68,k4_xboole_0(X69,X70)))))
    | ~ spl2_167 ),
    inference(avatar_component_clause,[],[f32822])).

fof(f32824,plain,
    ( spl2_167
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f4694,f2708,f2704,f32822])).

fof(f4694,plain,
    ( ! [X70,X68,X69] : k1_xboole_0 = k4_xboole_0(X70,k5_xboole_0(X70,k5_xboole_0(X68,k4_xboole_0(X68,k4_xboole_0(X69,X70)))))
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(superposition,[],[f2705,f2709])).

fof(f26179,plain,
    ( spl2_149
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f2473,f1606,f1426,f1381,f58,f50,f38,f26177])).

fof(f50,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f58,plain,
    ( spl2_6
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1381,plain,
    ( spl2_48
  <=> ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1426,plain,
    ( spl2_51
  <=> ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f1606,plain,
    ( spl2_64
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f2473,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_64 ),
    inference(forward_demodulation,[],[f2472,f1427])).

fof(f1427,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f2472,plain,
    ( ! [X4,X3] : k5_xboole_0(X4,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_48
    | ~ spl2_64 ),
    inference(forward_demodulation,[],[f2471,f39])).

fof(f2471,plain,
    ( ! [X4,X3] : k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_48
    | ~ spl2_64 ),
    inference(forward_demodulation,[],[f2470,f1382])).

fof(f1382,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f1381])).

fof(f2470,plain,
    ( ! [X4,X3] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = k5_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X3)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_64 ),
    inference(forward_demodulation,[],[f2439,f297])).

fof(f297,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f289,f277])).

fof(f277,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f51,f59])).

fof(f59,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f51,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f289,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f35,f277])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f2439,plain,
    ( ! [X4,X3] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))
    | ~ spl2_64 ),
    inference(superposition,[],[f1607,f1607])).

fof(f1607,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f1606])).

fof(f14060,plain,
    ( spl2_143
    | ~ spl2_57
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f3961,f3900,f1509,f14058])).

fof(f1509,plain,
    ( spl2_57
  <=> ! [X9,X10] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f3900,plain,
    ( spl2_82
  <=> ! [X13,X12] : k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13))) = X13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f3961,plain,
    ( ! [X26,X25] : k5_xboole_0(X26,X25) = k5_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,X26))
    | ~ spl2_57
    | ~ spl2_82 ),
    inference(superposition,[],[f1510,f3901])).

fof(f3901,plain,
    ( ! [X12,X13] : k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13))) = X13
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f3900])).

fof(f1510,plain,
    ( ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f1509])).

fof(f14036,plain,
    ( spl2_137
    | ~ spl2_57
    | ~ spl2_61
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f2336,f1598,f1594,f1509,f14034])).

fof(f1598,plain,
    ( spl2_62
  <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f2336,plain,
    ( ! [X23,X22] : k4_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X22)),X22)
    | ~ spl2_57
    | ~ spl2_61
    | ~ spl2_62 ),
    inference(forward_demodulation,[],[f2287,f1595])).

fof(f2287,plain,
    ( ! [X23,X22] : k4_xboole_0(X22,X23) = k5_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X22)),X22)
    | ~ spl2_57
    | ~ spl2_62 ),
    inference(superposition,[],[f1510,f1599])).

fof(f1599,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f1598])).

fof(f10707,plain,
    ( spl2_118
    | ~ spl2_3
    | ~ spl2_54
    | ~ spl2_60 ),
    inference(avatar_split_clause,[],[f1778,f1590,f1475,f46,f10705])).

fof(f1590,plain,
    ( spl2_60
  <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f1778,plain,
    ( ! [X14,X15,X16] : k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X16)))
    | ~ spl2_3
    | ~ spl2_54
    | ~ spl2_60 ),
    inference(forward_demodulation,[],[f1709,f47])).

fof(f1709,plain,
    ( ! [X14,X15,X16] : k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(k5_xboole_0(X15,X14),X16))
    | ~ spl2_54
    | ~ spl2_60 ),
    inference(superposition,[],[f1591,f1476])).

fof(f1591,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f1590])).

fof(f8691,plain,
    ( spl2_111
    | ~ spl2_53
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f3958,f3900,f1455,f8689])).

fof(f1455,plain,
    ( spl2_53
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f3958,plain,
    ( ! [X19,X20] : k5_xboole_0(X19,X20) = k5_xboole_0(k4_xboole_0(X20,X19),k4_xboole_0(X19,X20))
    | ~ spl2_53
    | ~ spl2_82 ),
    inference(superposition,[],[f1456,f3901])).

fof(f1456,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f1455])).

fof(f6750,plain,
    ( spl2_98
    | ~ spl2_52
    | ~ spl2_89 ),
    inference(avatar_split_clause,[],[f5242,f5229,f1434,f6748])).

fof(f1434,plain,
    ( spl2_52
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f5229,plain,
    ( spl2_89
  <=> ! [X34,X33,X35] : k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X34),X35)) = X34 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f5242,plain,
    ( ! [X30,X31,X32] : k4_xboole_0(X31,X30) = k4_xboole_0(k4_xboole_0(X31,X30),k4_xboole_0(X30,X32))
    | ~ spl2_52
    | ~ spl2_89 ),
    inference(superposition,[],[f5230,f1435])).

fof(f1435,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f1434])).

fof(f5230,plain,
    ( ! [X35,X33,X34] : k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X34),X35)) = X34
    | ~ spl2_89 ),
    inference(avatar_component_clause,[],[f5229])).

fof(f5368,plain,
    ( spl2_96
    | ~ spl2_2
    | ~ spl2_84 ),
    inference(avatar_split_clause,[],[f4363,f3908,f42,f5366])).

fof(f3908,plain,
    ( spl2_84
  <=> ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f4363,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X15,X14),k4_xboole_0(X14,X15))
    | ~ spl2_2
    | ~ spl2_84 ),
    inference(superposition,[],[f3909,f43])).

fof(f3909,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6))
    | ~ spl2_84 ),
    inference(avatar_component_clause,[],[f3908])).

fof(f5231,plain,
    ( spl2_89
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_69
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f5194,f5071,f2085,f1364,f42,f5229])).

fof(f2085,plain,
    ( spl2_69
  <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f5071,plain,
    ( spl2_87
  <=> ! [X27,X26,X28] : k4_xboole_0(X28,k5_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))) = X28 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f5194,plain,
    ( ! [X35,X33,X34] : k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X34),X35)) = X34
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_69
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f5193,f1365])).

fof(f5193,plain,
    ( ! [X35,X33,X34] : k4_xboole_0(X34,k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X33,X34),X35))) = X34
    | ~ spl2_2
    | ~ spl2_69
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f5114,f43])).

fof(f5114,plain,
    ( ! [X35,X33,X34] : k4_xboole_0(X34,k5_xboole_0(k4_xboole_0(k4_xboole_0(X33,X34),X35),k1_xboole_0)) = X34
    | ~ spl2_69
    | ~ spl2_87 ),
    inference(superposition,[],[f5072,f2086])).

fof(f2086,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f2085])).

fof(f5072,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X28,k5_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))) = X28
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f5071])).

fof(f5073,plain,
    ( spl2_87
    | ~ spl2_52
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f4680,f2708,f1434,f5071])).

fof(f4680,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X28,k5_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))) = X28
    | ~ spl2_52
    | ~ spl2_78 ),
    inference(superposition,[],[f1435,f2709])).

fof(f3910,plain,
    ( spl2_84
    | ~ spl2_59
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f3792,f3583,f1586,f3908])).

fof(f1586,plain,
    ( spl2_59
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f3583,plain,
    ( spl2_81
  <=> ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f3792,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6))
    | ~ spl2_59
    | ~ spl2_81 ),
    inference(superposition,[],[f3584,f1587])).

fof(f1587,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f1586])).

fof(f3584,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),X12)
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f3583])).

fof(f3902,plain,
    ( spl2_82
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f3475,f2615,f1602,f1594,f1590,f1426,f62,f54,f46,f42,f38,f3900])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f2615,plain,
    ( spl2_76
  <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f3475,plain,
    ( ! [X12,X13] : k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13))) = X13
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(backward_demodulation,[],[f2073,f3474])).

fof(f3474,plain,
    ( ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f3468,f39])).

fof(f3468,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(backward_demodulation,[],[f372,f3466])).

fof(f3466,plain,
    ( ! [X14,X15] : k1_xboole_0 = k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f3465,f1427])).

fof(f3465,plain,
    ( ! [X14,X15] : k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X15)) = k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_60
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(backward_demodulation,[],[f2402,f3464])).

fof(f3464,plain,
    ( ! [X21,X19,X20] : k5_xboole_0(k4_xboole_0(X20,X19),X21) = k5_xboole_0(X19,k5_xboole_0(X20,k5_xboole_0(k4_xboole_0(X19,X20),X21)))
    | ~ spl2_3
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f3402,f47])).

fof(f3402,plain,
    ( ! [X21,X19,X20] : k5_xboole_0(X19,k5_xboole_0(k5_xboole_0(X20,k4_xboole_0(X19,X20)),X21)) = k5_xboole_0(k4_xboole_0(X20,X19),X21)
    | ~ spl2_3
    | ~ spl2_76 ),
    inference(superposition,[],[f47,f2616])).

fof(f2616,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f2615])).

fof(f2402,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14))) = k5_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15))))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_60
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f2401,f1591])).

fof(f2401,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14))) = k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X14,X15),k5_xboole_0(X14,k4_xboole_0(X15,X14))))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f2354,f43])).

fof(f2354,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14))) = k5_xboole_0(X15,k5_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)))
    | ~ spl2_7
    | ~ spl2_63 ),
    inference(superposition,[],[f1603,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f372,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(superposition,[],[f55,f63])).

fof(f2073,plain,
    ( ! [X12,X13] : k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13)) = k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13)))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_60
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f2072,f1591])).

fof(f2072,plain,
    ( ! [X12,X13] : k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13)) = k5_xboole_0(k4_xboole_0(X12,X13),k5_xboole_0(X12,k4_xboole_0(X13,X12)))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f2048,f43])).

fof(f2048,plain,
    ( ! [X12,X13] : k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13))
    | ~ spl2_7
    | ~ spl2_61 ),
    inference(superposition,[],[f1595,f63])).

fof(f3585,plain,
    ( spl2_81
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_34
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f3476,f2615,f1602,f1594,f1590,f1426,f613,f62,f54,f46,f42,f38,f3583])).

fof(f3476,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),X12)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_34
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_61
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(backward_demodulation,[],[f910,f3475])).

fof(f910,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k5_xboole_0(X11,k5_xboole_0(k4_xboole_0(X12,X11),k4_xboole_0(X11,X12))))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f909,f72])).

fof(f72,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f47,f43])).

fof(f909,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k5_xboole_0(k4_xboole_0(X11,X12),k5_xboole_0(X11,k4_xboole_0(X12,X11))))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f872,f43])).

fof(f872,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k4_xboole_0(X11,X12)))
    | ~ spl2_7
    | ~ spl2_34 ),
    inference(superposition,[],[f614,f63])).

fof(f3581,plain,
    ( spl2_80
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_51
    | ~ spl2_60
    | ~ spl2_63
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f3474,f2615,f1602,f1590,f1426,f62,f54,f46,f42,f38,f3579])).

fof(f2710,plain,
    ( spl2_78
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f297,f58,f50,f2708])).

fof(f2706,plain,
    ( spl2_77
    | ~ spl2_7
    | ~ spl2_48
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f2679,f2599,f1381,f62,f2704])).

fof(f2599,plain,
    ( spl2_72
  <=> ! [X7,X6] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f2679,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7)))
    | ~ spl2_7
    | ~ spl2_48
    | ~ spl2_72 ),
    inference(forward_demodulation,[],[f2644,f1382])).

fof(f2644,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7))) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k5_xboole_0(X7,k4_xboole_0(X8,X7)))
    | ~ spl2_7
    | ~ spl2_72 ),
    inference(superposition,[],[f63,f2600])).

fof(f2600,plain,
    ( ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f2599])).

fof(f2617,plain,
    ( spl2_76
    | ~ spl2_2
    | ~ spl2_60
    | ~ spl2_63 ),
    inference(avatar_split_clause,[],[f2418,f1602,f1590,f42,f2615])).

fof(f2418,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))
    | ~ spl2_2
    | ~ spl2_60
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f2364,f43])).

fof(f2364,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),X4))
    | ~ spl2_60
    | ~ spl2_63 ),
    inference(superposition,[],[f1603,f1591])).

fof(f2605,plain,
    ( spl2_73
    | ~ spl2_3
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f1626,f1586,f46,f2603])).

fof(f1626,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl2_3
    | ~ spl2_59 ),
    inference(superposition,[],[f1587,f47])).

fof(f2601,plain,
    ( spl2_72
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f1453,f1434,f62,f42,f2599])).

fof(f1453,plain,
    ( ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_52 ),
    inference(forward_demodulation,[],[f1452,f1441])).

fof(f1441,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)
    | ~ spl2_52 ),
    inference(superposition,[],[f1435,f1435])).

fof(f1452,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_52 ),
    inference(forward_demodulation,[],[f1447,f43])).

fof(f1447,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X7,X6),X6),X6)
    | ~ spl2_7
    | ~ spl2_52 ),
    inference(superposition,[],[f63,f1435])).

fof(f2087,plain,
    ( spl2_69
    | ~ spl2_7
    | ~ spl2_48
    | ~ spl2_54
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f2080,f1594,f1475,f1381,f62,f2085])).

fof(f2080,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9)
    | ~ spl2_7
    | ~ spl2_48
    | ~ spl2_54
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f2079,f1382])).

fof(f2079,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,X9) = k4_xboole_0(k4_xboole_0(X9,X10),X9)
    | ~ spl2_7
    | ~ spl2_54
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f2058,f1476])).

fof(f2058,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X9,k4_xboole_0(X9,X10))),X9)
    | ~ spl2_7
    | ~ spl2_61 ),
    inference(superposition,[],[f63,f1595])).

fof(f1612,plain,
    ( spl2_65
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f905,f613,f58,f54,f50,f1610])).

fof(f905,plain,
    ( ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X6,k4_xboole_0(X6,X5))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f904,f293])).

fof(f293,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f132,f277])).

fof(f132,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f51,f55])).

fof(f904,plain,
    ( ! [X6,X5] : k5_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5))))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f868,f277])).

fof(f868,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))))
    | ~ spl2_5
    | ~ spl2_34 ),
    inference(superposition,[],[f614,f55])).

fof(f1608,plain,
    ( spl2_64
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f294,f58,f54,f50,f1606])).

fof(f294,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f271,f277])).

fof(f271,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f59,f55])).

fof(f1604,plain,
    ( spl2_63
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f293,f58,f54,f50,f1602])).

fof(f1600,plain,
    ( spl2_62
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f287,f58,f54,f50,f1598])).

fof(f287,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f133,f271])).

fof(f133,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f51,f55])).

fof(f1596,plain,
    ( spl2_61
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f277,f58,f50,f1594])).

fof(f1592,plain,
    ( spl2_60
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f72,f46,f42,f1590])).

fof(f1588,plain,
    ( spl2_59
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f69,f46,f42,f1586])).

fof(f69,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f47,f43])).

fof(f1511,plain,
    ( spl2_57
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f1488,f1475,f1509])).

fof(f1488,plain,
    ( ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9
    | ~ spl2_54 ),
    inference(superposition,[],[f1476,f1476])).

fof(f1507,plain,
    ( spl2_56
    | ~ spl2_53
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f1487,f1475,f1455,f1505])).

fof(f1487,plain,
    ( ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7
    | ~ spl2_53
    | ~ spl2_54 ),
    inference(superposition,[],[f1476,f1456])).

fof(f1482,plain,
    ( ~ spl2_55
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f906,f613,f58,f54,f50,f1479])).

fof(f906,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(backward_demodulation,[],[f288,f905])).

fof(f288,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f30,f287])).

fof(f30,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f1477,plain,
    ( spl2_54
    | ~ spl2_2
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f1459,f1455,f42,f1475])).

fof(f1459,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
    | ~ spl2_2
    | ~ spl2_53 ),
    inference(superposition,[],[f1456,f43])).

fof(f1457,plain,
    ( spl2_53
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1266,f860,f719,f352,f158,f113,f109,f46,f38,f1455])).

fof(f109,plain,
    ( spl2_12
  <=> ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f113,plain,
    ( spl2_13
  <=> ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f158,plain,
    ( spl2_15
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f352,plain,
    ( spl2_23
  <=> ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f719,plain,
    ( spl2_39
  <=> ! [X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f860,plain,
    ( spl2_42
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1266,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f1237,f1261])).

fof(f1261,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f110,f1231])).

fof(f1231,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f159,f1201])).

fof(f1201,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f353,f1198])).

fof(f1198,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f720,f1197])).

fof(f1197,plain,
    ( ! [X12] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12))
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f1150,f114])).

fof(f114,plain,
    ( ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f1150,plain,
    ( ! [X12] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12)))
    | ~ spl2_1
    | ~ spl2_42 ),
    inference(superposition,[],[f861,f39])).

fof(f861,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f860])).

fof(f720,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1)
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f719])).

fof(f353,plain,
    ( ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f352])).

fof(f159,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f110,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1237,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f414,f1201])).

fof(f414,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(superposition,[],[f47,f353])).

fof(f1436,plain,
    ( spl2_52
    | ~ spl2_34
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1171,f860,f613,f1434])).

fof(f1171,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_34
    | ~ spl2_42 ),
    inference(superposition,[],[f861,f614])).

fof(f1428,plain,
    ( spl2_51
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1198,f860,f719,f113,f38,f1426])).

fof(f1383,plain,
    ( spl2_48
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1230,f860,f719,f352,f145,f113,f38,f1381])).

fof(f145,plain,
    ( spl2_14
  <=> ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f1230,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4)
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f146,f1201])).

fof(f146,plain,
    ( ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1366,plain,
    ( spl2_47
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_23
    | ~ spl2_39
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1261,f860,f719,f352,f158,f113,f109,f38,f1364])).

fof(f862,plain,
    ( spl2_42
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f295,f66,f58,f50,f860])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f295,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f67,f277])).

fof(f67,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f721,plain,
    ( spl2_39
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f528,f509,f478,f719])).

fof(f478,plain,
    ( spl2_26
  <=> ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f509,plain,
    ( spl2_28
  <=> ! [X7] : k4_xboole_0(X7,X7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f528,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1)
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(superposition,[],[f510,f479])).

fof(f479,plain,
    ( ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f478])).

fof(f510,plain,
    ( ! [X7] : k4_xboole_0(X7,X7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f509])).

fof(f615,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f290,f58,f50,f613])).

fof(f290,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f51,f277])).

fof(f511,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f385,f174,f62,f58,f54,f50,f38,f509])).

fof(f174,plain,
    ( spl2_16
  <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f385,plain,
    ( ! [X7] : k4_xboole_0(X7,X7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f384,f39])).

fof(f384,plain,
    ( ! [X7] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k4_xboole_0(X7,k1_xboole_0),X7)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f383,f293])).

fof(f383,plain,
    ( ! [X7] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k5_xboole_0(X7,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))),X7)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f360,f277])).

fof(f360,plain,
    ( ! [X7] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))),X7)
    | ~ spl2_7
    | ~ spl2_16 ),
    inference(superposition,[],[f63,f175])).

fof(f175,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f480,plain,
    ( spl2_26
    | ~ spl2_14
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f395,f352,f145,f478])).

fof(f395,plain,
    ( ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)
    | ~ spl2_14
    | ~ spl2_23 ),
    inference(superposition,[],[f353,f146])).

fof(f354,plain,
    ( spl2_23
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f322,f304,f174,f145,f113,f58,f50,f352])).

fof(f304,plain,
    ( spl2_21
  <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f322,plain,
    ( ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f153,f320])).

fof(f320,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f319,f114])).

fof(f319,plain,
    ( ! [X0] : k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f308,f277])).

fof(f308,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(superposition,[],[f305,f175])).

fof(f305,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f304])).

fof(f153,plain,
    ( ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k1_xboole_0,X3)))
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f51,f146])).

fof(f306,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f261,f58,f38,f304])).

fof(f261,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f59,f39])).

fof(f176,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f130,f54,f38,f174])).

fof(f130,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f55,f39])).

fof(f160,plain,
    ( spl2_15
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f152,f145,f83,f158])).

fof(f83,plain,
    ( spl2_9
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f152,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f84,f146])).

fof(f84,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f147,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f141,f113,f54,f50,f38,f145])).

fof(f141,plain,
    ( ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f140,f39])).

fof(f140,plain,
    ( ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f134,f132])).

fof(f134,plain,
    ( ! [X4] : k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)))
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(superposition,[],[f114,f55])).

fof(f115,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f104,f97,f50,f113])).

fof(f97,plain,
    ( spl2_11
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f104,plain,
    ( ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(superposition,[],[f98,f51])).

fof(f98,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f111,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f102,f97,f42,f109])).

fof(f102,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f98,f43])).

fof(f99,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f95,f91,f46,f97])).

fof(f91,plain,
    ( spl2_10
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f95,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f47,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f86,f83,f38,f91])).

fof(f86,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(superposition,[],[f84,f39])).

fof(f85,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f78,f50,f38,f83])).

fof(f78,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f51,f39])).

fof(f68,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f32,f35])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f22,f23])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f64,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f54])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f23,f23])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f46])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f44,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f40,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (12496)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.45  % (12494)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (12500)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (12491)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (12497)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (12497)Refutation not found, incomplete strategy% (12497)------------------------------
% 0.22/0.48  % (12497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12497)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (12497)Memory used [KB]: 10490
% 0.22/0.48  % (12497)Time elapsed: 0.072 s
% 0.22/0.48  % (12497)------------------------------
% 0.22/0.48  % (12497)------------------------------
% 0.22/0.48  % (12490)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (12486)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (12489)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (12488)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (12493)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (12501)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (12492)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (12495)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (12503)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (12487)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (12498)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (12499)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (12502)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.82/1.01  % (12490)Time limit reached!
% 4.82/1.01  % (12490)------------------------------
% 4.82/1.01  % (12490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.82/1.01  % (12490)Termination reason: Time limit
% 4.82/1.01  % (12490)Termination phase: Saturation
% 4.82/1.01  
% 4.82/1.01  % (12490)Memory used [KB]: 16502
% 4.82/1.01  % (12490)Time elapsed: 0.600 s
% 4.82/1.01  % (12490)------------------------------
% 4.82/1.01  % (12490)------------------------------
% 11.86/1.92  % (12492)Time limit reached!
% 11.86/1.92  % (12492)------------------------------
% 11.86/1.92  % (12492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.86/1.92  % (12492)Termination reason: Time limit
% 11.86/1.92  % (12492)Termination phase: Saturation
% 11.86/1.92  
% 11.86/1.92  % (12492)Memory used [KB]: 46566
% 11.86/1.92  % (12492)Time elapsed: 1.500 s
% 11.86/1.92  % (12492)------------------------------
% 11.86/1.92  % (12492)------------------------------
% 12.53/1.96  % (12491)Time limit reached!
% 12.53/1.96  % (12491)------------------------------
% 12.53/1.96  % (12491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/1.96  % (12491)Termination reason: Time limit
% 12.53/1.96  % (12491)Termination phase: Saturation
% 12.53/1.96  
% 12.53/1.96  % (12491)Memory used [KB]: 42856
% 12.53/1.96  % (12491)Time elapsed: 1.500 s
% 12.53/1.96  % (12491)------------------------------
% 12.53/1.96  % (12491)------------------------------
% 14.33/2.22  % (12488)Time limit reached!
% 14.33/2.22  % (12488)------------------------------
% 14.33/2.22  % (12488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.33/2.22  % (12488)Termination reason: Time limit
% 14.33/2.22  % (12488)Termination phase: Saturation
% 14.33/2.22  
% 14.33/2.22  % (12488)Memory used [KB]: 29807
% 14.33/2.22  % (12488)Time elapsed: 1.800 s
% 14.33/2.22  % (12488)------------------------------
% 14.33/2.22  % (12488)------------------------------
% 17.79/2.61  % (12498)Time limit reached!
% 17.79/2.61  % (12498)------------------------------
% 17.79/2.61  % (12498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.61  % (12498)Termination reason: Time limit
% 17.79/2.61  % (12498)Termination phase: Saturation
% 17.79/2.61  
% 17.79/2.61  % (12498)Memory used [KB]: 39914
% 17.79/2.61  % (12498)Time elapsed: 2.200 s
% 17.79/2.61  % (12498)------------------------------
% 17.79/2.61  % (12498)------------------------------
% 28.79/4.01  % (12493)Refutation found. Thanks to Tanya!
% 28.79/4.01  % SZS status Theorem for theBenchmark
% 28.79/4.01  % SZS output start Proof for theBenchmark
% 28.79/4.01  fof(f53877,plain,(
% 28.79/4.01    $false),
% 28.79/4.01    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f56,f60,f64,f68,f85,f94,f99,f111,f115,f147,f160,f176,f306,f354,f480,f511,f615,f721,f862,f1366,f1383,f1428,f1436,f1457,f1477,f1482,f1507,f1511,f1588,f1592,f1596,f1600,f1604,f1608,f1612,f2087,f2601,f2605,f2617,f2706,f2710,f3581,f3585,f3902,f3910,f5073,f5231,f5368,f6750,f8691,f10707,f14036,f14060,f26179,f32824,f37425,f45327,f47974,f48562,f50614,f51199,f51893,f52770,f53364,f53758])).
% 28.79/4.01  fof(f53758,plain,(
% 28.79/4.01    ~spl2_3 | spl2_55 | ~spl2_63 | ~spl2_73 | ~spl2_80 | ~spl2_203),
% 28.79/4.01    inference(avatar_contradiction_clause,[],[f53757])).
% 28.79/4.01  fof(f53757,plain,(
% 28.79/4.01    $false | (~spl2_3 | spl2_55 | ~spl2_63 | ~spl2_73 | ~spl2_80 | ~spl2_203)),
% 28.79/4.01    inference(subsumption_resolution,[],[f1481,f53756])).
% 28.79/4.01  fof(f53756,plain,(
% 28.79/4.01    ( ! [X80,X79] : (k5_xboole_0(X79,X80) = k4_xboole_0(k5_xboole_0(X79,k4_xboole_0(X80,X79)),k5_xboole_0(X79,k4_xboole_0(X79,X80)))) ) | (~spl2_3 | ~spl2_63 | ~spl2_73 | ~spl2_80 | ~spl2_203)),
% 28.79/4.01    inference(forward_demodulation,[],[f53512,f53707])).
% 28.79/4.01  fof(f53707,plain,(
% 28.79/4.01    ( ! [X52,X53] : (k5_xboole_0(X52,k4_xboole_0(X52,X53)) = k4_xboole_0(X52,k5_xboole_0(X52,X53))) ) | (~spl2_3 | ~spl2_63 | ~spl2_73 | ~spl2_203)),
% 28.79/4.01    inference(forward_demodulation,[],[f53706,f2785])).
% 28.79/4.01  fof(f2785,plain,(
% 28.79/4.01    ( ! [X35,X33,X34] : (k5_xboole_0(X33,k5_xboole_0(X35,k5_xboole_0(X34,k4_xboole_0(X34,X33)))) = k5_xboole_0(X35,k4_xboole_0(X33,X34))) ) | (~spl2_63 | ~spl2_73)),
% 28.79/4.01    inference(superposition,[],[f2604,f1603])).
% 28.79/4.01  fof(f1603,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_63),
% 28.79/4.01    inference(avatar_component_clause,[],[f1602])).
% 28.79/4.01  fof(f1602,plain,(
% 28.79/4.01    spl2_63 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 28.79/4.01  fof(f2604,plain,(
% 28.79/4.01    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | ~spl2_73),
% 28.79/4.01    inference(avatar_component_clause,[],[f2603])).
% 28.79/4.01  fof(f2603,plain,(
% 28.79/4.01    spl2_73 <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 28.79/4.01  fof(f53706,plain,(
% 28.79/4.01    ( ! [X52,X53] : (k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(X52,k5_xboole_0(X53,k4_xboole_0(X53,X52))))) ) | (~spl2_3 | ~spl2_63 | ~spl2_203)),
% 28.79/4.01    inference(forward_demodulation,[],[f53499,f47])).
% 28.79/4.01  fof(f47,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_3),
% 28.79/4.01    inference(avatar_component_clause,[],[f46])).
% 28.79/4.01  fof(f46,plain,(
% 28.79/4.01    spl2_3 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 28.79/4.01  fof(f53499,plain,(
% 28.79/4.01    ( ! [X52,X53] : (k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X53,X52)))) ) | (~spl2_63 | ~spl2_203)),
% 28.79/4.01    inference(superposition,[],[f1603,f53363])).
% 28.79/4.01  fof(f53363,plain,(
% 28.79/4.01    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) ) | ~spl2_203),
% 28.79/4.01    inference(avatar_component_clause,[],[f53362])).
% 28.79/4.01  fof(f53362,plain,(
% 28.79/4.01    spl2_203 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).
% 28.79/4.01  fof(f53512,plain,(
% 28.79/4.01    ( ! [X80,X79] : (k5_xboole_0(X79,X80) = k4_xboole_0(k5_xboole_0(X79,k4_xboole_0(X80,X79)),k4_xboole_0(X79,k5_xboole_0(X79,X80)))) ) | (~spl2_80 | ~spl2_203)),
% 28.79/4.01    inference(superposition,[],[f3580,f53363])).
% 28.79/4.01  fof(f3580,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1) ) | ~spl2_80),
% 28.79/4.01    inference(avatar_component_clause,[],[f3579])).
% 28.79/4.01  fof(f3579,plain,(
% 28.79/4.01    spl2_80 <=> ! [X1,X0] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 28.79/4.01  fof(f1481,plain,(
% 28.79/4.01    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_55),
% 28.79/4.01    inference(avatar_component_clause,[],[f1479])).
% 28.79/4.01  fof(f1479,plain,(
% 28.79/4.01    spl2_55 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 28.79/4.01  fof(f53364,plain,(
% 28.79/4.01    spl2_203 | ~spl2_2 | ~spl2_202),
% 28.79/4.01    inference(avatar_split_clause,[],[f52772,f52768,f42,f53362])).
% 28.79/4.01  fof(f42,plain,(
% 28.79/4.01    spl2_2 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 28.79/4.01  fof(f52768,plain,(
% 28.79/4.01    spl2_202 <=> ! [X40,X41] : k4_xboole_0(X40,X41) = k4_xboole_0(k5_xboole_0(X40,X41),X41)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_202])])).
% 28.79/4.01  fof(f52772,plain,(
% 28.79/4.01    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) ) | (~spl2_2 | ~spl2_202)),
% 28.79/4.01    inference(superposition,[],[f52769,f43])).
% 28.79/4.01  fof(f43,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_2),
% 28.79/4.01    inference(avatar_component_clause,[],[f42])).
% 28.79/4.01  fof(f52769,plain,(
% 28.79/4.01    ( ! [X41,X40] : (k4_xboole_0(X40,X41) = k4_xboole_0(k5_xboole_0(X40,X41),X41)) ) | ~spl2_202),
% 28.79/4.01    inference(avatar_component_clause,[],[f52768])).
% 28.79/4.01  fof(f52770,plain,(
% 28.79/4.01    spl2_202 | ~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_47 | ~spl2_54 | ~spl2_56 | ~spl2_63 | ~spl2_65 | ~spl2_78 | ~spl2_96 | ~spl2_149 | ~spl2_195 | ~spl2_199 | ~spl2_201),
% 28.79/4.01    inference(avatar_split_clause,[],[f52454,f51891,f50612,f48560,f26177,f5366,f2708,f1610,f1602,f1505,f1475,f1364,f54,f42,f38,f52768])).
% 28.79/4.01  fof(f38,plain,(
% 28.79/4.01    spl2_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 28.79/4.01  fof(f54,plain,(
% 28.79/4.01    spl2_5 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 28.79/4.01  fof(f1364,plain,(
% 28.79/4.01    spl2_47 <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 28.79/4.01  fof(f1475,plain,(
% 28.79/4.01    spl2_54 <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 28.79/4.01  fof(f1505,plain,(
% 28.79/4.01    spl2_56 <=> ! [X7,X8] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 28.79/4.01  fof(f1610,plain,(
% 28.79/4.01    spl2_65 <=> ! [X5,X6] : k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X6,k4_xboole_0(X6,X5))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 28.79/4.01  fof(f2708,plain,(
% 28.79/4.01    spl2_78 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 28.79/4.01  fof(f5366,plain,(
% 28.79/4.01    spl2_96 <=> ! [X15,X14] : k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X15,X14),k4_xboole_0(X14,X15))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 28.79/4.01  fof(f26177,plain,(
% 28.79/4.01    spl2_149 <=> ! [X3,X4] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).
% 28.79/4.01  fof(f48560,plain,(
% 28.79/4.01    spl2_195 <=> ! [X13,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X13,X12),X12),X13)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).
% 28.79/4.01  fof(f50612,plain,(
% 28.79/4.01    spl2_199 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).
% 28.79/4.01  fof(f51891,plain,(
% 28.79/4.01    spl2_201 <=> ! [X16,X17] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_201])])).
% 28.79/4.01  fof(f52454,plain,(
% 28.79/4.01    ( ! [X41,X40] : (k4_xboole_0(X40,X41) = k4_xboole_0(k5_xboole_0(X40,X41),X41)) ) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_47 | ~spl2_54 | ~spl2_56 | ~spl2_63 | ~spl2_65 | ~spl2_78 | ~spl2_96 | ~spl2_149 | ~spl2_195 | ~spl2_199 | ~spl2_201)),
% 28.79/4.01    inference(forward_demodulation,[],[f52453,f39])).
% 28.79/4.01  fof(f39,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 28.79/4.01    inference(avatar_component_clause,[],[f38])).
% 28.79/4.01  fof(f52453,plain,(
% 28.79/4.01    ( ! [X41,X40] : (k4_xboole_0(k4_xboole_0(X40,X41),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X40,X41),X41)) ) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_47 | ~spl2_54 | ~spl2_56 | ~spl2_63 | ~spl2_65 | ~spl2_78 | ~spl2_96 | ~spl2_149 | ~spl2_195 | ~spl2_199 | ~spl2_201)),
% 28.79/4.01    inference(forward_demodulation,[],[f52452,f51130])).
% 28.79/4.01  fof(f51130,plain,(
% 28.79/4.01    ( ! [X194,X195] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X194,X195),k4_xboole_0(k5_xboole_0(X194,X195),X195))) ) | (~spl2_2 | ~spl2_47 | ~spl2_54 | ~spl2_56 | ~spl2_63 | ~spl2_65 | ~spl2_78 | ~spl2_96 | ~spl2_149 | ~spl2_195 | ~spl2_199)),
% 28.79/4.01    inference(forward_demodulation,[],[f51129,f1365])).
% 28.79/4.01  fof(f1365,plain,(
% 28.79/4.01    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl2_47),
% 28.79/4.01    inference(avatar_component_clause,[],[f1364])).
% 28.79/4.01  fof(f51129,plain,(
% 28.79/4.01    ( ! [X194,X195] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X194,X195)),k4_xboole_0(k5_xboole_0(X194,X195),X195))) ) | (~spl2_2 | ~spl2_47 | ~spl2_54 | ~spl2_56 | ~spl2_63 | ~spl2_65 | ~spl2_78 | ~spl2_96 | ~spl2_149 | ~spl2_195 | ~spl2_199)),
% 28.79/4.01    inference(forward_demodulation,[],[f51128,f43])).
% 28.79/4.01  fof(f51128,plain,(
% 28.79/4.01    ( ! [X194,X195] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k4_xboole_0(k5_xboole_0(X194,X195),X195))) ) | (~spl2_2 | ~spl2_47 | ~spl2_54 | ~spl2_56 | ~spl2_63 | ~spl2_65 | ~spl2_78 | ~spl2_96 | ~spl2_149 | ~spl2_195 | ~spl2_199)),
% 28.79/4.01    inference(forward_demodulation,[],[f51127,f6563])).
% 28.79/4.01  fof(f6563,plain,(
% 28.79/4.01    ( ! [X48,X49] : (k4_xboole_0(k5_xboole_0(X48,X49),X49) = k5_xboole_0(X48,k4_xboole_0(X49,k5_xboole_0(X48,X49)))) ) | (~spl2_56 | ~spl2_96)),
% 28.79/4.01    inference(superposition,[],[f5367,f1506])).
% 28.79/4.01  fof(f1506,plain,(
% 28.79/4.01    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7) ) | ~spl2_56),
% 28.79/4.01    inference(avatar_component_clause,[],[f1505])).
% 28.79/4.01  fof(f5367,plain,(
% 28.79/4.01    ( ! [X14,X15] : (k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X15,X14),k4_xboole_0(X14,X15))) ) | ~spl2_96),
% 28.79/4.01    inference(avatar_component_clause,[],[f5366])).
% 28.79/4.01  fof(f51127,plain,(
% 28.79/4.01    ( ! [X194,X195] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k5_xboole_0(X194,k4_xboole_0(X195,k5_xboole_0(X194,X195))))) ) | (~spl2_2 | ~spl2_47 | ~spl2_54 | ~spl2_63 | ~spl2_65 | ~spl2_78 | ~spl2_96 | ~spl2_149 | ~spl2_195 | ~spl2_199)),
% 28.79/4.01    inference(forward_demodulation,[],[f51126,f49412])).
% 28.79/4.01  fof(f49412,plain,(
% 28.79/4.01    ( ! [X54,X53] : (k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k4_xboole_0(X54,k5_xboole_0(X53,X54))) ) | (~spl2_2 | ~spl2_47 | ~spl2_54 | ~spl2_63 | ~spl2_96 | ~spl2_195)),
% 28.79/4.01    inference(forward_demodulation,[],[f49411,f6547])).
% 28.79/4.01  fof(f6547,plain,(
% 28.79/4.01    ( ! [X10,X9] : (k4_xboole_0(X9,k5_xboole_0(X10,X9)) = k5_xboole_0(X10,k4_xboole_0(k5_xboole_0(X10,X9),X9))) ) | (~spl2_54 | ~spl2_96)),
% 28.79/4.01    inference(superposition,[],[f5367,f1476])).
% 28.79/4.01  fof(f1476,plain,(
% 28.79/4.01    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) ) | ~spl2_54),
% 28.79/4.01    inference(avatar_component_clause,[],[f1475])).
% 28.79/4.01  fof(f49411,plain,(
% 28.79/4.01    ( ! [X54,X53] : (k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k5_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54))) ) | (~spl2_2 | ~spl2_47 | ~spl2_63 | ~spl2_195)),
% 28.79/4.01    inference(forward_demodulation,[],[f49410,f1365])).
% 28.79/4.01  fof(f49410,plain,(
% 28.79/4.01    ( ! [X54,X53] : (k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k5_xboole_0(X53,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X53,X54),X54)))) ) | (~spl2_2 | ~spl2_63 | ~spl2_195)),
% 28.79/4.01    inference(forward_demodulation,[],[f49219,f43])).
% 28.79/4.01  fof(f49219,plain,(
% 28.79/4.01    ( ! [X54,X53] : (k4_xboole_0(X53,k4_xboole_0(k5_xboole_0(X53,X54),X54)) = k5_xboole_0(X53,k5_xboole_0(k4_xboole_0(k5_xboole_0(X53,X54),X54),k1_xboole_0))) ) | (~spl2_63 | ~spl2_195)),
% 28.79/4.01    inference(superposition,[],[f1603,f48561])).
% 28.79/4.01  fof(f48561,plain,(
% 28.79/4.01    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X13,X12),X12),X13)) ) | ~spl2_195),
% 28.79/4.01    inference(avatar_component_clause,[],[f48560])).
% 28.79/4.01  fof(f51126,plain,(
% 28.79/4.01    ( ! [X194,X195] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k5_xboole_0(X194,k4_xboole_0(X194,k4_xboole_0(k5_xboole_0(X194,X195),X195))))) ) | (~spl2_65 | ~spl2_78 | ~spl2_149 | ~spl2_199)),
% 28.79/4.01    inference(forward_demodulation,[],[f51125,f2709])).
% 28.79/4.01  fof(f2709,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | ~spl2_78),
% 28.79/4.01    inference(avatar_component_clause,[],[f2708])).
% 28.79/4.01  fof(f51125,plain,(
% 28.79/4.01    ( ! [X194,X195] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k4_xboole_0(k5_xboole_0(X194,k4_xboole_0(X194,k5_xboole_0(X194,X195))),X195))) ) | (~spl2_65 | ~spl2_78 | ~spl2_149 | ~spl2_199)),
% 28.79/4.01    inference(forward_demodulation,[],[f50860,f4644])).
% 28.79/4.01  fof(f4644,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | (~spl2_65 | ~spl2_78)),
% 28.79/4.01    inference(superposition,[],[f2709,f1611])).
% 28.79/4.01  fof(f1611,plain,(
% 28.79/4.01    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X6,k4_xboole_0(X6,X5))) ) | ~spl2_65),
% 28.79/4.01    inference(avatar_component_clause,[],[f1610])).
% 28.79/4.01  fof(f50860,plain,(
% 28.79/4.01    ( ! [X194,X195] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X194,X195),k1_xboole_0),k5_xboole_0(k5_xboole_0(X194,X195),k4_xboole_0(k5_xboole_0(X194,X195),k4_xboole_0(X194,X195))))) ) | (~spl2_149 | ~spl2_199)),
% 28.79/4.01    inference(superposition,[],[f26178,f50613])).
% 28.79/4.01  fof(f50613,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl2_199),
% 28.79/4.01    inference(avatar_component_clause,[],[f50612])).
% 28.79/4.01  fof(f26178,plain,(
% 28.79/4.01    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))) ) | ~spl2_149),
% 28.79/4.01    inference(avatar_component_clause,[],[f26177])).
% 28.79/4.01  fof(f52452,plain,(
% 28.79/4.01    ( ! [X41,X40] : (k4_xboole_0(k5_xboole_0(X40,X41),X41) = k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k5_xboole_0(X40,X41),X41)))) ) | (~spl2_1 | ~spl2_5 | ~spl2_201)),
% 28.79/4.01    inference(forward_demodulation,[],[f52085,f39])).
% 28.79/4.01  fof(f52085,plain,(
% 28.79/4.01    ( ! [X41,X40] : (k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k5_xboole_0(X40,X41),X41))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X40,X41),X41),k1_xboole_0)) ) | (~spl2_5 | ~spl2_201)),
% 28.79/4.01    inference(superposition,[],[f55,f51892])).
% 28.79/4.01  fof(f51892,plain,(
% 28.79/4.01    ( ! [X17,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17))) ) | ~spl2_201),
% 28.79/4.01    inference(avatar_component_clause,[],[f51891])).
% 28.79/4.01  fof(f55,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_5),
% 28.79/4.01    inference(avatar_component_clause,[],[f54])).
% 28.79/4.01  fof(f51893,plain,(
% 28.79/4.01    spl2_201 | ~spl2_174 | ~spl2_200),
% 28.79/4.01    inference(avatar_split_clause,[],[f51374,f51197,f37423,f51891])).
% 28.79/4.01  fof(f37423,plain,(
% 28.79/4.01    spl2_174 <=> ! [X44,X43,X45] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X43,k4_xboole_0(X44,X45)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).
% 28.79/4.01  fof(f51197,plain,(
% 28.79/4.01    spl2_200 <=> ! [X65,X64] : k4_xboole_0(X64,X65) = k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_200])])).
% 28.79/4.01  fof(f51374,plain,(
% 28.79/4.01    ( ! [X17,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17))) ) | (~spl2_174 | ~spl2_200)),
% 28.79/4.01    inference(superposition,[],[f37424,f51198])).
% 28.79/4.01  fof(f51198,plain,(
% 28.79/4.01    ( ! [X64,X65] : (k4_xboole_0(X64,X65) = k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64))) ) | ~spl2_200),
% 28.79/4.01    inference(avatar_component_clause,[],[f51197])).
% 28.79/4.01  fof(f37424,plain,(
% 28.79/4.01    ( ! [X45,X43,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X43,k4_xboole_0(X44,X45)))) ) | ~spl2_174),
% 28.79/4.01    inference(avatar_component_clause,[],[f37423])).
% 28.79/4.01  fof(f51199,plain,(
% 28.79/4.01    spl2_200 | ~spl2_2 | ~spl2_47 | ~spl2_96 | ~spl2_111 | ~spl2_185),
% 28.79/4.01    inference(avatar_split_clause,[],[f47777,f45325,f8689,f5366,f1364,f42,f51197])).
% 28.79/4.01  fof(f8689,plain,(
% 28.79/4.01    spl2_111 <=> ! [X20,X19] : k5_xboole_0(X19,X20) = k5_xboole_0(k4_xboole_0(X20,X19),k4_xboole_0(X19,X20))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).
% 28.79/4.01  fof(f45325,plain,(
% 28.79/4.01    spl2_185 <=> ! [X69,X68,X70] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_185])])).
% 28.79/4.01  fof(f47777,plain,(
% 28.79/4.01    ( ! [X64,X65] : (k4_xboole_0(X64,X65) = k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64))) ) | (~spl2_2 | ~spl2_47 | ~spl2_96 | ~spl2_111 | ~spl2_185)),
% 28.79/4.01    inference(forward_demodulation,[],[f47776,f1365])).
% 28.79/4.01  fof(f47776,plain,(
% 28.79/4.01    ( ! [X64,X65] : (k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X64,X65))) ) | (~spl2_2 | ~spl2_96 | ~spl2_111 | ~spl2_185)),
% 28.79/4.01    inference(forward_demodulation,[],[f47773,f43])).
% 28.79/4.01  fof(f47773,plain,(
% 28.79/4.01    ( ! [X64,X65] : (k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64)) = k5_xboole_0(k4_xboole_0(X64,X65),k1_xboole_0)) ) | (~spl2_96 | ~spl2_111 | ~spl2_185)),
% 28.79/4.01    inference(backward_demodulation,[],[f6569,f47515])).
% 28.79/4.01  fof(f47515,plain,(
% 28.79/4.01    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) ) | (~spl2_111 | ~spl2_185)),
% 28.79/4.01    inference(superposition,[],[f45326,f8690])).
% 28.79/4.01  fof(f8690,plain,(
% 28.79/4.01    ( ! [X19,X20] : (k5_xboole_0(X19,X20) = k5_xboole_0(k4_xboole_0(X20,X19),k4_xboole_0(X19,X20))) ) | ~spl2_111),
% 28.79/4.01    inference(avatar_component_clause,[],[f8689])).
% 28.79/4.01  fof(f45326,plain,(
% 28.79/4.01    ( ! [X70,X68,X69] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))) ) | ~spl2_185),
% 28.79/4.01    inference(avatar_component_clause,[],[f45325])).
% 28.79/4.01  fof(f6569,plain,(
% 28.79/4.01    ( ! [X64,X65] : (k4_xboole_0(k5_xboole_0(X64,X65),k4_xboole_0(X65,X64)) = k5_xboole_0(k4_xboole_0(X64,X65),k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,X65)))) ) | ~spl2_96),
% 28.79/4.01    inference(superposition,[],[f5367,f5367])).
% 28.79/4.01  fof(f50614,plain,(
% 28.79/4.01    spl2_199 | ~spl2_143 | ~spl2_185),
% 28.79/4.01    inference(avatar_split_clause,[],[f47514,f45325,f14058,f50612])).
% 28.79/4.01  fof(f14058,plain,(
% 28.79/4.01    spl2_143 <=> ! [X25,X26] : k5_xboole_0(X26,X25) = k5_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,X26))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).
% 28.79/4.01  fof(f47514,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | (~spl2_143 | ~spl2_185)),
% 28.79/4.01    inference(superposition,[],[f45326,f14059])).
% 28.79/4.01  fof(f14059,plain,(
% 28.79/4.01    ( ! [X26,X25] : (k5_xboole_0(X26,X25) = k5_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,X26))) ) | ~spl2_143),
% 28.79/4.01    inference(avatar_component_clause,[],[f14058])).
% 28.79/4.01  fof(f48562,plain,(
% 28.79/4.01    spl2_195 | ~spl2_54 | ~spl2_193),
% 28.79/4.01    inference(avatar_split_clause,[],[f48047,f47972,f1475,f48560])).
% 28.79/4.01  fof(f47972,plain,(
% 28.79/4.01    spl2_193 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).
% 28.79/4.01  fof(f48047,plain,(
% 28.79/4.01    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X13,X12),X12),X13)) ) | (~spl2_54 | ~spl2_193)),
% 28.79/4.01    inference(superposition,[],[f47973,f1476])).
% 28.79/4.01  fof(f47973,plain,(
% 28.79/4.01    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) ) | ~spl2_193),
% 28.79/4.01    inference(avatar_component_clause,[],[f47972])).
% 28.79/4.01  fof(f47974,plain,(
% 28.79/4.01    spl2_193 | ~spl2_111 | ~spl2_185),
% 28.79/4.01    inference(avatar_split_clause,[],[f47515,f45325,f8689,f47972])).
% 28.79/4.01  fof(f45327,plain,(
% 28.79/4.01    spl2_185 | ~spl2_77 | ~spl2_98),
% 28.79/4.01    inference(avatar_split_clause,[],[f6836,f6748,f2704,f45325])).
% 28.79/4.01  fof(f2704,plain,(
% 28.79/4.01    spl2_77 <=> ! [X7,X8] : k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 28.79/4.01  fof(f6748,plain,(
% 28.79/4.01    spl2_98 <=> ! [X32,X31,X30] : k4_xboole_0(X31,X30) = k4_xboole_0(k4_xboole_0(X31,X30),k4_xboole_0(X30,X32))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 28.79/4.01  fof(f6836,plain,(
% 28.79/4.01    ( ! [X70,X68,X69] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X69,X70),k5_xboole_0(k4_xboole_0(X69,X70),k4_xboole_0(X68,X69)))) ) | (~spl2_77 | ~spl2_98)),
% 28.79/4.01    inference(superposition,[],[f2705,f6749])).
% 28.79/4.01  fof(f6749,plain,(
% 28.79/4.01    ( ! [X30,X31,X32] : (k4_xboole_0(X31,X30) = k4_xboole_0(k4_xboole_0(X31,X30),k4_xboole_0(X30,X32))) ) | ~spl2_98),
% 28.79/4.01    inference(avatar_component_clause,[],[f6748])).
% 28.79/4.01  fof(f2705,plain,(
% 28.79/4.01    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7)))) ) | ~spl2_77),
% 28.79/4.01    inference(avatar_component_clause,[],[f2704])).
% 28.79/4.01  fof(f37425,plain,(
% 28.79/4.01    spl2_174 | ~spl2_34 | ~spl2_61 | ~spl2_78 | ~spl2_118 | ~spl2_137 | ~spl2_167),
% 28.79/4.01    inference(avatar_split_clause,[],[f37154,f32822,f14034,f10705,f2708,f1594,f613,f37423])).
% 28.79/4.01  fof(f613,plain,(
% 28.79/4.01    spl2_34 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 28.79/4.01  fof(f1594,plain,(
% 28.79/4.01    spl2_61 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 28.79/4.01  fof(f10705,plain,(
% 28.79/4.01    spl2_118 <=> ! [X16,X15,X14] : k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X16)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).
% 28.79/4.01  fof(f14034,plain,(
% 28.79/4.01    spl2_137 <=> ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X22)),X22)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).
% 28.79/4.01  fof(f32822,plain,(
% 28.79/4.01    spl2_167 <=> ! [X69,X68,X70] : k1_xboole_0 = k4_xboole_0(X70,k5_xboole_0(X70,k5_xboole_0(X68,k4_xboole_0(X68,k4_xboole_0(X69,X70)))))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).
% 28.79/4.01  fof(f37154,plain,(
% 28.79/4.01    ( ! [X45,X43,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X43,k4_xboole_0(X44,X45)))) ) | (~spl2_34 | ~spl2_61 | ~spl2_78 | ~spl2_118 | ~spl2_137 | ~spl2_167)),
% 28.79/4.01    inference(forward_demodulation,[],[f37153,f614])).
% 28.79/4.01  fof(f614,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_34),
% 28.79/4.01    inference(avatar_component_clause,[],[f613])).
% 28.79/4.01  fof(f37153,plain,(
% 28.79/4.01    ( ! [X45,X43,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(X43,k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X44,X45)))))) ) | (~spl2_61 | ~spl2_78 | ~spl2_118 | ~spl2_137 | ~spl2_167)),
% 28.79/4.01    inference(forward_demodulation,[],[f37152,f2709])).
% 28.79/4.01  fof(f37152,plain,(
% 28.79/4.01    ( ! [X45,X43,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(X43,k4_xboole_0(k5_xboole_0(X43,k4_xboole_0(X43,X44)),X45)))) ) | (~spl2_61 | ~spl2_118 | ~spl2_137 | ~spl2_167)),
% 28.79/4.01    inference(forward_demodulation,[],[f36949,f20673])).
% 28.79/4.01  fof(f20673,plain,(
% 28.79/4.01    ( ! [X269,X268,X270] : (k5_xboole_0(X270,k5_xboole_0(X268,k4_xboole_0(X268,k5_xboole_0(X269,X270)))) = k5_xboole_0(X269,k4_xboole_0(k5_xboole_0(X269,X270),X268))) ) | (~spl2_118 | ~spl2_137)),
% 28.79/4.01    inference(superposition,[],[f10706,f14035])).
% 28.79/4.01  fof(f14035,plain,(
% 28.79/4.01    ( ! [X23,X22] : (k4_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X22)),X22)) ) | ~spl2_137),
% 28.79/4.01    inference(avatar_component_clause,[],[f14034])).
% 28.79/4.01  fof(f10706,plain,(
% 28.79/4.01    ( ! [X14,X15,X16] : (k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X16)))) ) | ~spl2_118),
% 28.79/4.01    inference(avatar_component_clause,[],[f10705])).
% 28.79/4.01  fof(f36949,plain,(
% 28.79/4.01    ( ! [X45,X43,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(k4_xboole_0(X43,X44),k5_xboole_0(X45,k4_xboole_0(X45,k5_xboole_0(X43,k4_xboole_0(X43,X44))))))) ) | (~spl2_61 | ~spl2_167)),
% 28.79/4.01    inference(superposition,[],[f32823,f1595])).
% 28.79/4.01  fof(f1595,plain,(
% 28.79/4.01    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl2_61),
% 28.79/4.01    inference(avatar_component_clause,[],[f1594])).
% 28.79/4.01  fof(f32823,plain,(
% 28.79/4.01    ( ! [X70,X68,X69] : (k1_xboole_0 = k4_xboole_0(X70,k5_xboole_0(X70,k5_xboole_0(X68,k4_xboole_0(X68,k4_xboole_0(X69,X70)))))) ) | ~spl2_167),
% 28.79/4.01    inference(avatar_component_clause,[],[f32822])).
% 28.79/4.01  fof(f32824,plain,(
% 28.79/4.01    spl2_167 | ~spl2_77 | ~spl2_78),
% 28.79/4.01    inference(avatar_split_clause,[],[f4694,f2708,f2704,f32822])).
% 28.79/4.01  fof(f4694,plain,(
% 28.79/4.01    ( ! [X70,X68,X69] : (k1_xboole_0 = k4_xboole_0(X70,k5_xboole_0(X70,k5_xboole_0(X68,k4_xboole_0(X68,k4_xboole_0(X69,X70)))))) ) | (~spl2_77 | ~spl2_78)),
% 28.79/4.01    inference(superposition,[],[f2705,f2709])).
% 28.79/4.01  fof(f26179,plain,(
% 28.79/4.01    spl2_149 | ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_48 | ~spl2_51 | ~spl2_64),
% 28.79/4.01    inference(avatar_split_clause,[],[f2473,f1606,f1426,f1381,f58,f50,f38,f26177])).
% 28.79/4.01  fof(f50,plain,(
% 28.79/4.01    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 28.79/4.01  fof(f58,plain,(
% 28.79/4.01    spl2_6 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 28.79/4.01  fof(f1381,plain,(
% 28.79/4.01    spl2_48 <=> ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 28.79/4.01  fof(f1426,plain,(
% 28.79/4.01    spl2_51 <=> ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 28.79/4.01  fof(f1606,plain,(
% 28.79/4.01    spl2_64 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 28.79/4.01  fof(f2473,plain,(
% 28.79/4.01    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_48 | ~spl2_51 | ~spl2_64)),
% 28.79/4.01    inference(forward_demodulation,[],[f2472,f1427])).
% 28.79/4.01  fof(f1427,plain,(
% 28.79/4.01    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | ~spl2_51),
% 28.79/4.01    inference(avatar_component_clause,[],[f1426])).
% 28.79/4.01  fof(f2472,plain,(
% 28.79/4.01    ( ! [X4,X3] : (k5_xboole_0(X4,X4) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_48 | ~spl2_64)),
% 28.79/4.01    inference(forward_demodulation,[],[f2471,f39])).
% 28.79/4.01  fof(f2471,plain,(
% 28.79/4.01    ( ! [X4,X3] : (k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))) ) | (~spl2_4 | ~spl2_6 | ~spl2_48 | ~spl2_64)),
% 28.79/4.01    inference(forward_demodulation,[],[f2470,f1382])).
% 28.79/4.01  fof(f1382,plain,(
% 28.79/4.01    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) ) | ~spl2_48),
% 28.79/4.01    inference(avatar_component_clause,[],[f1381])).
% 28.79/4.01  fof(f2470,plain,(
% 28.79/4.01    ( ! [X4,X3] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = k5_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X3)))) ) | (~spl2_4 | ~spl2_6 | ~spl2_64)),
% 28.79/4.01    inference(forward_demodulation,[],[f2439,f297])).
% 28.79/4.01  fof(f297,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | (~spl2_4 | ~spl2_6)),
% 28.79/4.01    inference(forward_demodulation,[],[f289,f277])).
% 28.79/4.01  fof(f277,plain,(
% 28.79/4.01    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_4 | ~spl2_6)),
% 28.79/4.01    inference(superposition,[],[f51,f59])).
% 28.79/4.01  fof(f59,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_6),
% 28.79/4.01    inference(avatar_component_clause,[],[f58])).
% 28.79/4.01  fof(f51,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_4),
% 28.79/4.01    inference(avatar_component_clause,[],[f50])).
% 28.79/4.01  fof(f289,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | (~spl2_4 | ~spl2_6)),
% 28.79/4.01    inference(backward_demodulation,[],[f35,f277])).
% 28.79/4.01  fof(f35,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 28.79/4.01    inference(definition_unfolding,[],[f27,f23,f23])).
% 28.79/4.01  fof(f23,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 28.79/4.01    inference(cnf_transformation,[],[f8])).
% 28.79/4.01  fof(f8,axiom,(
% 28.79/4.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 28.79/4.01  fof(f27,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 28.79/4.01    inference(cnf_transformation,[],[f9])).
% 28.79/4.01  fof(f9,axiom,(
% 28.79/4.01    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 28.79/4.01  fof(f2439,plain,(
% 28.79/4.01    ( ! [X4,X3] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X4,X3)),k5_xboole_0(X3,k4_xboole_0(X3,X4)))) ) | ~spl2_64),
% 28.79/4.01    inference(superposition,[],[f1607,f1607])).
% 28.79/4.01  fof(f1607,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_64),
% 28.79/4.01    inference(avatar_component_clause,[],[f1606])).
% 28.79/4.01  fof(f14060,plain,(
% 28.79/4.01    spl2_143 | ~spl2_57 | ~spl2_82),
% 28.79/4.01    inference(avatar_split_clause,[],[f3961,f3900,f1509,f14058])).
% 28.79/4.01  fof(f1509,plain,(
% 28.79/4.01    spl2_57 <=> ! [X9,X10] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 28.79/4.01  fof(f3900,plain,(
% 28.79/4.01    spl2_82 <=> ! [X13,X12] : k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13))) = X13),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 28.79/4.01  fof(f3961,plain,(
% 28.79/4.01    ( ! [X26,X25] : (k5_xboole_0(X26,X25) = k5_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,X26))) ) | (~spl2_57 | ~spl2_82)),
% 28.79/4.01    inference(superposition,[],[f1510,f3901])).
% 28.79/4.01  fof(f3901,plain,(
% 28.79/4.01    ( ! [X12,X13] : (k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13))) = X13) ) | ~spl2_82),
% 28.79/4.01    inference(avatar_component_clause,[],[f3900])).
% 28.79/4.01  fof(f1510,plain,(
% 28.79/4.01    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) ) | ~spl2_57),
% 28.79/4.01    inference(avatar_component_clause,[],[f1509])).
% 28.79/4.01  fof(f14036,plain,(
% 28.79/4.01    spl2_137 | ~spl2_57 | ~spl2_61 | ~spl2_62),
% 28.79/4.01    inference(avatar_split_clause,[],[f2336,f1598,f1594,f1509,f14034])).
% 28.79/4.01  fof(f1598,plain,(
% 28.79/4.01    spl2_62 <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 28.79/4.01  fof(f2336,plain,(
% 28.79/4.01    ( ! [X23,X22] : (k4_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X22)),X22)) ) | (~spl2_57 | ~spl2_61 | ~spl2_62)),
% 28.79/4.01    inference(forward_demodulation,[],[f2287,f1595])).
% 28.79/4.01  fof(f2287,plain,(
% 28.79/4.01    ( ! [X23,X22] : (k4_xboole_0(X22,X23) = k5_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X22)),X22)) ) | (~spl2_57 | ~spl2_62)),
% 28.79/4.01    inference(superposition,[],[f1510,f1599])).
% 28.79/4.01  fof(f1599,plain,(
% 28.79/4.01    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) ) | ~spl2_62),
% 28.79/4.01    inference(avatar_component_clause,[],[f1598])).
% 28.79/4.01  fof(f10707,plain,(
% 28.79/4.01    spl2_118 | ~spl2_3 | ~spl2_54 | ~spl2_60),
% 28.79/4.01    inference(avatar_split_clause,[],[f1778,f1590,f1475,f46,f10705])).
% 28.79/4.01  fof(f1590,plain,(
% 28.79/4.01    spl2_60 <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 28.79/4.01  fof(f1778,plain,(
% 28.79/4.01    ( ! [X14,X15,X16] : (k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X16)))) ) | (~spl2_3 | ~spl2_54 | ~spl2_60)),
% 28.79/4.01    inference(forward_demodulation,[],[f1709,f47])).
% 28.79/4.01  fof(f1709,plain,(
% 28.79/4.01    ( ! [X14,X15,X16] : (k5_xboole_0(X16,X15) = k5_xboole_0(X14,k5_xboole_0(k5_xboole_0(X15,X14),X16))) ) | (~spl2_54 | ~spl2_60)),
% 28.79/4.01    inference(superposition,[],[f1591,f1476])).
% 28.79/4.01  fof(f1591,plain,(
% 28.79/4.01    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) ) | ~spl2_60),
% 28.79/4.01    inference(avatar_component_clause,[],[f1590])).
% 28.79/4.01  fof(f8691,plain,(
% 28.79/4.01    spl2_111 | ~spl2_53 | ~spl2_82),
% 28.79/4.01    inference(avatar_split_clause,[],[f3958,f3900,f1455,f8689])).
% 28.79/4.01  fof(f1455,plain,(
% 28.79/4.01    spl2_53 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 28.79/4.01  fof(f3958,plain,(
% 28.79/4.01    ( ! [X19,X20] : (k5_xboole_0(X19,X20) = k5_xboole_0(k4_xboole_0(X20,X19),k4_xboole_0(X19,X20))) ) | (~spl2_53 | ~spl2_82)),
% 28.79/4.01    inference(superposition,[],[f1456,f3901])).
% 28.79/4.01  fof(f1456,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_53),
% 28.79/4.01    inference(avatar_component_clause,[],[f1455])).
% 28.79/4.01  fof(f6750,plain,(
% 28.79/4.01    spl2_98 | ~spl2_52 | ~spl2_89),
% 28.79/4.01    inference(avatar_split_clause,[],[f5242,f5229,f1434,f6748])).
% 28.79/4.01  fof(f1434,plain,(
% 28.79/4.01    spl2_52 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 28.79/4.01  fof(f5229,plain,(
% 28.79/4.01    spl2_89 <=> ! [X34,X33,X35] : k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X34),X35)) = X34),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 28.79/4.01  fof(f5242,plain,(
% 28.79/4.01    ( ! [X30,X31,X32] : (k4_xboole_0(X31,X30) = k4_xboole_0(k4_xboole_0(X31,X30),k4_xboole_0(X30,X32))) ) | (~spl2_52 | ~spl2_89)),
% 28.79/4.01    inference(superposition,[],[f5230,f1435])).
% 28.79/4.01  fof(f1435,plain,(
% 28.79/4.01    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | ~spl2_52),
% 28.79/4.01    inference(avatar_component_clause,[],[f1434])).
% 28.79/4.01  fof(f5230,plain,(
% 28.79/4.01    ( ! [X35,X33,X34] : (k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X34),X35)) = X34) ) | ~spl2_89),
% 28.79/4.01    inference(avatar_component_clause,[],[f5229])).
% 28.79/4.01  fof(f5368,plain,(
% 28.79/4.01    spl2_96 | ~spl2_2 | ~spl2_84),
% 28.79/4.01    inference(avatar_split_clause,[],[f4363,f3908,f42,f5366])).
% 28.79/4.01  fof(f3908,plain,(
% 28.79/4.01    spl2_84 <=> ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).
% 28.79/4.01  fof(f4363,plain,(
% 28.79/4.01    ( ! [X14,X15] : (k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X15,X14),k4_xboole_0(X14,X15))) ) | (~spl2_2 | ~spl2_84)),
% 28.79/4.01    inference(superposition,[],[f3909,f43])).
% 28.79/4.01  fof(f3909,plain,(
% 28.79/4.01    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6))) ) | ~spl2_84),
% 28.79/4.01    inference(avatar_component_clause,[],[f3908])).
% 28.79/4.01  fof(f5231,plain,(
% 28.79/4.01    spl2_89 | ~spl2_2 | ~spl2_47 | ~spl2_69 | ~spl2_87),
% 28.79/4.01    inference(avatar_split_clause,[],[f5194,f5071,f2085,f1364,f42,f5229])).
% 28.79/4.01  fof(f2085,plain,(
% 28.79/4.01    spl2_69 <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 28.79/4.01  fof(f5071,plain,(
% 28.79/4.01    spl2_87 <=> ! [X27,X26,X28] : k4_xboole_0(X28,k5_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))) = X28),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 28.79/4.01  fof(f5194,plain,(
% 28.79/4.01    ( ! [X35,X33,X34] : (k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X34),X35)) = X34) ) | (~spl2_2 | ~spl2_47 | ~spl2_69 | ~spl2_87)),
% 28.79/4.01    inference(forward_demodulation,[],[f5193,f1365])).
% 28.79/4.01  fof(f5193,plain,(
% 28.79/4.01    ( ! [X35,X33,X34] : (k4_xboole_0(X34,k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X33,X34),X35))) = X34) ) | (~spl2_2 | ~spl2_69 | ~spl2_87)),
% 28.79/4.01    inference(forward_demodulation,[],[f5114,f43])).
% 28.79/4.01  fof(f5114,plain,(
% 28.79/4.01    ( ! [X35,X33,X34] : (k4_xboole_0(X34,k5_xboole_0(k4_xboole_0(k4_xboole_0(X33,X34),X35),k1_xboole_0)) = X34) ) | (~spl2_69 | ~spl2_87)),
% 28.79/4.01    inference(superposition,[],[f5072,f2086])).
% 28.79/4.01  fof(f2086,plain,(
% 28.79/4.01    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9)) ) | ~spl2_69),
% 28.79/4.01    inference(avatar_component_clause,[],[f2085])).
% 28.79/4.01  fof(f5072,plain,(
% 28.79/4.01    ( ! [X28,X26,X27] : (k4_xboole_0(X28,k5_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))) = X28) ) | ~spl2_87),
% 28.79/4.01    inference(avatar_component_clause,[],[f5071])).
% 28.79/4.01  fof(f5073,plain,(
% 28.79/4.01    spl2_87 | ~spl2_52 | ~spl2_78),
% 28.79/4.01    inference(avatar_split_clause,[],[f4680,f2708,f1434,f5071])).
% 28.79/4.01  fof(f4680,plain,(
% 28.79/4.01    ( ! [X28,X26,X27] : (k4_xboole_0(X28,k5_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))) = X28) ) | (~spl2_52 | ~spl2_78)),
% 28.79/4.01    inference(superposition,[],[f1435,f2709])).
% 28.79/4.01  fof(f3910,plain,(
% 28.79/4.01    spl2_84 | ~spl2_59 | ~spl2_81),
% 28.79/4.01    inference(avatar_split_clause,[],[f3792,f3583,f1586,f3908])).
% 28.79/4.01  fof(f1586,plain,(
% 28.79/4.01    spl2_59 <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 28.79/4.01  fof(f3583,plain,(
% 28.79/4.01    spl2_81 <=> ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),X12)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 28.79/4.01  fof(f3792,plain,(
% 28.79/4.01    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6))) ) | (~spl2_59 | ~spl2_81)),
% 28.79/4.01    inference(superposition,[],[f3584,f1587])).
% 28.79/4.01  fof(f1587,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) ) | ~spl2_59),
% 28.79/4.01    inference(avatar_component_clause,[],[f1586])).
% 28.79/4.01  fof(f3584,plain,(
% 28.79/4.01    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),X12)) ) | ~spl2_81),
% 28.79/4.01    inference(avatar_component_clause,[],[f3583])).
% 28.79/4.01  fof(f3902,plain,(
% 28.79/4.01    spl2_82 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_51 | ~spl2_60 | ~spl2_61 | ~spl2_63 | ~spl2_76),
% 28.79/4.01    inference(avatar_split_clause,[],[f3475,f2615,f1602,f1594,f1590,f1426,f62,f54,f46,f42,f38,f3900])).
% 28.79/4.01  fof(f62,plain,(
% 28.79/4.01    spl2_7 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 28.79/4.01  fof(f2615,plain,(
% 28.79/4.01    spl2_76 <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 28.79/4.01  fof(f3475,plain,(
% 28.79/4.01    ( ! [X12,X13] : (k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13))) = X13) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_51 | ~spl2_60 | ~spl2_61 | ~spl2_63 | ~spl2_76)),
% 28.79/4.01    inference(backward_demodulation,[],[f2073,f3474])).
% 28.79/4.01  fof(f3474,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_51 | ~spl2_60 | ~spl2_63 | ~spl2_76)),
% 28.79/4.01    inference(forward_demodulation,[],[f3468,f39])).
% 28.79/4.01  fof(f3468,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_51 | ~spl2_60 | ~spl2_63 | ~spl2_76)),
% 28.79/4.01    inference(backward_demodulation,[],[f372,f3466])).
% 28.79/4.01  fof(f3466,plain,(
% 28.79/4.01    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14)))) ) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_51 | ~spl2_60 | ~spl2_63 | ~spl2_76)),
% 28.79/4.01    inference(forward_demodulation,[],[f3465,f1427])).
% 28.79/4.01  fof(f3465,plain,(
% 28.79/4.01    ( ! [X14,X15] : (k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X15)) = k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14)))) ) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_60 | ~spl2_63 | ~spl2_76)),
% 28.79/4.01    inference(backward_demodulation,[],[f2402,f3464])).
% 28.79/4.01  fof(f3464,plain,(
% 28.79/4.01    ( ! [X21,X19,X20] : (k5_xboole_0(k4_xboole_0(X20,X19),X21) = k5_xboole_0(X19,k5_xboole_0(X20,k5_xboole_0(k4_xboole_0(X19,X20),X21)))) ) | (~spl2_3 | ~spl2_76)),
% 28.79/4.01    inference(forward_demodulation,[],[f3402,f47])).
% 28.79/4.01  fof(f3402,plain,(
% 28.79/4.01    ( ! [X21,X19,X20] : (k5_xboole_0(X19,k5_xboole_0(k5_xboole_0(X20,k4_xboole_0(X19,X20)),X21)) = k5_xboole_0(k4_xboole_0(X20,X19),X21)) ) | (~spl2_3 | ~spl2_76)),
% 28.79/4.01    inference(superposition,[],[f47,f2616])).
% 28.79/4.01  fof(f2616,plain,(
% 28.79/4.01    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) ) | ~spl2_76),
% 28.79/4.01    inference(avatar_component_clause,[],[f2615])).
% 28.79/4.01  fof(f2402,plain,(
% 28.79/4.01    ( ! [X14,X15] : (k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14))) = k5_xboole_0(X15,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15))))) ) | (~spl2_2 | ~spl2_7 | ~spl2_60 | ~spl2_63)),
% 28.79/4.01    inference(forward_demodulation,[],[f2401,f1591])).
% 28.79/4.01  fof(f2401,plain,(
% 28.79/4.01    ( ! [X14,X15] : (k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14))) = k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X14,X15),k5_xboole_0(X14,k4_xboole_0(X15,X14))))) ) | (~spl2_2 | ~spl2_7 | ~spl2_63)),
% 28.79/4.01    inference(forward_demodulation,[],[f2354,f43])).
% 28.79/4.01  fof(f2354,plain,(
% 28.79/4.01    ( ! [X14,X15] : (k4_xboole_0(X15,k5_xboole_0(X14,k4_xboole_0(X15,X14))) = k5_xboole_0(X15,k5_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)))) ) | (~spl2_7 | ~spl2_63)),
% 28.79/4.01    inference(superposition,[],[f1603,f63])).
% 28.79/4.01  fof(f63,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) ) | ~spl2_7),
% 28.79/4.01    inference(avatar_component_clause,[],[f62])).
% 28.79/4.01  fof(f372,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ) | (~spl2_5 | ~spl2_7)),
% 28.79/4.01    inference(superposition,[],[f55,f63])).
% 28.79/4.01  fof(f2073,plain,(
% 28.79/4.01    ( ! [X12,X13] : (k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13)) = k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13)))) ) | (~spl2_2 | ~spl2_7 | ~spl2_60 | ~spl2_61)),
% 28.79/4.01    inference(forward_demodulation,[],[f2072,f1591])).
% 28.79/4.01  fof(f2072,plain,(
% 28.79/4.01    ( ! [X12,X13] : (k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13)) = k5_xboole_0(k4_xboole_0(X12,X13),k5_xboole_0(X12,k4_xboole_0(X13,X12)))) ) | (~spl2_2 | ~spl2_7 | ~spl2_61)),
% 28.79/4.01    inference(forward_demodulation,[],[f2048,f43])).
% 28.79/4.01  fof(f2048,plain,(
% 28.79/4.01    ( ! [X12,X13] : (k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X13))) ) | (~spl2_7 | ~spl2_61)),
% 28.79/4.01    inference(superposition,[],[f1595,f63])).
% 28.79/4.01  fof(f3585,plain,(
% 28.79/4.01    spl2_81 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_34 | ~spl2_51 | ~spl2_60 | ~spl2_61 | ~spl2_63 | ~spl2_76),
% 28.79/4.01    inference(avatar_split_clause,[],[f3476,f2615,f1602,f1594,f1590,f1426,f613,f62,f54,f46,f42,f38,f3583])).
% 28.79/4.01  fof(f3476,plain,(
% 28.79/4.01    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),X12)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_34 | ~spl2_51 | ~spl2_60 | ~spl2_61 | ~spl2_63 | ~spl2_76)),
% 28.79/4.01    inference(backward_demodulation,[],[f910,f3475])).
% 28.79/4.01  fof(f910,plain,(
% 28.79/4.01    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k5_xboole_0(X11,k5_xboole_0(k4_xboole_0(X12,X11),k4_xboole_0(X11,X12))))) ) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_34)),
% 28.79/4.01    inference(forward_demodulation,[],[f909,f72])).
% 28.79/4.01  fof(f72,plain,(
% 28.79/4.01    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) ) | (~spl2_2 | ~spl2_3)),
% 28.79/4.01    inference(superposition,[],[f47,f43])).
% 28.79/4.01  fof(f909,plain,(
% 28.79/4.01    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k5_xboole_0(k4_xboole_0(X11,X12),k5_xboole_0(X11,k4_xboole_0(X12,X11))))) ) | (~spl2_2 | ~spl2_7 | ~spl2_34)),
% 28.79/4.01    inference(forward_demodulation,[],[f872,f43])).
% 28.79/4.01  fof(f872,plain,(
% 28.79/4.01    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k4_xboole_0(X11,X12)))) ) | (~spl2_7 | ~spl2_34)),
% 28.79/4.01    inference(superposition,[],[f614,f63])).
% 28.79/4.01  fof(f3581,plain,(
% 28.79/4.01    spl2_80 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_51 | ~spl2_60 | ~spl2_63 | ~spl2_76),
% 28.79/4.01    inference(avatar_split_clause,[],[f3474,f2615,f1602,f1590,f1426,f62,f54,f46,f42,f38,f3579])).
% 28.79/4.01  fof(f2710,plain,(
% 28.79/4.01    spl2_78 | ~spl2_4 | ~spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f297,f58,f50,f2708])).
% 28.79/4.01  fof(f2706,plain,(
% 28.79/4.01    spl2_77 | ~spl2_7 | ~spl2_48 | ~spl2_72),
% 28.79/4.01    inference(avatar_split_clause,[],[f2679,f2599,f1381,f62,f2704])).
% 28.79/4.01  fof(f2599,plain,(
% 28.79/4.01    spl2_72 <=> ! [X7,X6] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 28.79/4.01  fof(f2679,plain,(
% 28.79/4.01    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7)))) ) | (~spl2_7 | ~spl2_48 | ~spl2_72)),
% 28.79/4.01    inference(forward_demodulation,[],[f2644,f1382])).
% 28.79/4.01  fof(f2644,plain,(
% 28.79/4.01    ( ! [X8,X7] : (k4_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7))) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k5_xboole_0(X7,k4_xboole_0(X8,X7)))) ) | (~spl2_7 | ~spl2_72)),
% 28.79/4.01    inference(superposition,[],[f63,f2600])).
% 28.79/4.01  fof(f2600,plain,(
% 28.79/4.01    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) ) | ~spl2_72),
% 28.79/4.01    inference(avatar_component_clause,[],[f2599])).
% 28.79/4.01  fof(f2617,plain,(
% 28.79/4.01    spl2_76 | ~spl2_2 | ~spl2_60 | ~spl2_63),
% 28.79/4.01    inference(avatar_split_clause,[],[f2418,f1602,f1590,f42,f2615])).
% 28.79/4.01  fof(f2418,plain,(
% 28.79/4.01    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) ) | (~spl2_2 | ~spl2_60 | ~spl2_63)),
% 28.79/4.01    inference(forward_demodulation,[],[f2364,f43])).
% 28.79/4.01  fof(f2364,plain,(
% 28.79/4.01    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),X4))) ) | (~spl2_60 | ~spl2_63)),
% 28.79/4.01    inference(superposition,[],[f1603,f1591])).
% 28.79/4.01  fof(f2605,plain,(
% 28.79/4.01    spl2_73 | ~spl2_3 | ~spl2_59),
% 28.79/4.01    inference(avatar_split_clause,[],[f1626,f1586,f46,f2603])).
% 28.79/4.01  fof(f1626,plain,(
% 28.79/4.01    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | (~spl2_3 | ~spl2_59)),
% 28.79/4.01    inference(superposition,[],[f1587,f47])).
% 28.79/4.01  fof(f2601,plain,(
% 28.79/4.01    spl2_72 | ~spl2_2 | ~spl2_7 | ~spl2_52),
% 28.79/4.01    inference(avatar_split_clause,[],[f1453,f1434,f62,f42,f2599])).
% 28.79/4.01  fof(f1453,plain,(
% 28.79/4.01    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) ) | (~spl2_2 | ~spl2_7 | ~spl2_52)),
% 28.79/4.01    inference(forward_demodulation,[],[f1452,f1441])).
% 28.79/4.01  fof(f1441,plain,(
% 28.79/4.01    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)) ) | ~spl2_52),
% 28.79/4.01    inference(superposition,[],[f1435,f1435])).
% 28.79/4.01  fof(f1452,plain,(
% 28.79/4.01    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) ) | (~spl2_2 | ~spl2_7 | ~spl2_52)),
% 28.79/4.01    inference(forward_demodulation,[],[f1447,f43])).
% 28.79/4.01  fof(f1447,plain,(
% 28.79/4.01    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X7,X6),X6),X6)) ) | (~spl2_7 | ~spl2_52)),
% 28.79/4.01    inference(superposition,[],[f63,f1435])).
% 28.79/4.01  fof(f2087,plain,(
% 28.79/4.01    spl2_69 | ~spl2_7 | ~spl2_48 | ~spl2_54 | ~spl2_61),
% 28.79/4.01    inference(avatar_split_clause,[],[f2080,f1594,f1475,f1381,f62,f2085])).
% 28.79/4.01  fof(f2080,plain,(
% 28.79/4.01    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9)) ) | (~spl2_7 | ~spl2_48 | ~spl2_54 | ~spl2_61)),
% 28.79/4.01    inference(forward_demodulation,[],[f2079,f1382])).
% 28.79/4.01  fof(f2079,plain,(
% 28.79/4.01    ( ! [X10,X9] : (k4_xboole_0(X9,X9) = k4_xboole_0(k4_xboole_0(X9,X10),X9)) ) | (~spl2_7 | ~spl2_54 | ~spl2_61)),
% 28.79/4.01    inference(forward_demodulation,[],[f2058,f1476])).
% 28.79/4.01  fof(f2058,plain,(
% 28.79/4.01    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X9,k4_xboole_0(X9,X10))),X9)) ) | (~spl2_7 | ~spl2_61)),
% 28.79/4.01    inference(superposition,[],[f63,f1595])).
% 28.79/4.01  fof(f1612,plain,(
% 28.79/4.01    spl2_65 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_34),
% 28.79/4.01    inference(avatar_split_clause,[],[f905,f613,f58,f54,f50,f1610])).
% 28.79/4.01  fof(f905,plain,(
% 28.79/4.01    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X6,k4_xboole_0(X6,X5))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_34)),
% 28.79/4.01    inference(forward_demodulation,[],[f904,f293])).
% 28.79/4.01  fof(f293,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 28.79/4.01    inference(backward_demodulation,[],[f132,f277])).
% 28.79/4.01  fof(f132,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_4 | ~spl2_5)),
% 28.79/4.01    inference(superposition,[],[f51,f55])).
% 28.79/4.01  fof(f904,plain,(
% 28.79/4.01    ( ! [X6,X5] : (k5_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5))))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_34)),
% 28.79/4.01    inference(forward_demodulation,[],[f868,f277])).
% 28.79/4.01  fof(f868,plain,(
% 28.79/4.01    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))))) ) | (~spl2_5 | ~spl2_34)),
% 28.79/4.01    inference(superposition,[],[f614,f55])).
% 28.79/4.01  fof(f1608,plain,(
% 28.79/4.01    spl2_64 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f294,f58,f54,f50,f1606])).
% 28.79/4.01  fof(f294,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 28.79/4.01    inference(backward_demodulation,[],[f271,f277])).
% 28.79/4.01  fof(f271,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_5 | ~spl2_6)),
% 28.79/4.01    inference(superposition,[],[f59,f55])).
% 28.79/4.01  fof(f1604,plain,(
% 28.79/4.01    spl2_63 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f293,f58,f54,f50,f1602])).
% 28.79/4.01  fof(f1600,plain,(
% 28.79/4.01    spl2_62 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f287,f58,f54,f50,f1598])).
% 28.79/4.01  fof(f287,plain,(
% 28.79/4.01    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 28.79/4.01    inference(backward_demodulation,[],[f133,f271])).
% 28.79/4.01  fof(f133,plain,(
% 28.79/4.01    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) ) | (~spl2_4 | ~spl2_5)),
% 28.79/4.01    inference(superposition,[],[f51,f55])).
% 28.79/4.01  fof(f1596,plain,(
% 28.79/4.01    spl2_61 | ~spl2_4 | ~spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f277,f58,f50,f1594])).
% 28.79/4.01  fof(f1592,plain,(
% 28.79/4.01    spl2_60 | ~spl2_2 | ~spl2_3),
% 28.79/4.01    inference(avatar_split_clause,[],[f72,f46,f42,f1590])).
% 28.79/4.01  fof(f1588,plain,(
% 28.79/4.01    spl2_59 | ~spl2_2 | ~spl2_3),
% 28.79/4.01    inference(avatar_split_clause,[],[f69,f46,f42,f1586])).
% 28.79/4.01  fof(f69,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) ) | (~spl2_2 | ~spl2_3)),
% 28.79/4.01    inference(superposition,[],[f47,f43])).
% 28.79/4.01  fof(f1511,plain,(
% 28.79/4.01    spl2_57 | ~spl2_54),
% 28.79/4.01    inference(avatar_split_clause,[],[f1488,f1475,f1509])).
% 28.79/4.01  fof(f1488,plain,(
% 28.79/4.01    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) ) | ~spl2_54),
% 28.79/4.01    inference(superposition,[],[f1476,f1476])).
% 28.79/4.01  fof(f1507,plain,(
% 28.79/4.01    spl2_56 | ~spl2_53 | ~spl2_54),
% 28.79/4.01    inference(avatar_split_clause,[],[f1487,f1475,f1455,f1505])).
% 28.79/4.01  fof(f1487,plain,(
% 28.79/4.01    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7) ) | (~spl2_53 | ~spl2_54)),
% 28.79/4.01    inference(superposition,[],[f1476,f1456])).
% 28.79/4.01  fof(f1482,plain,(
% 28.79/4.01    ~spl2_55 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_34),
% 28.79/4.01    inference(avatar_split_clause,[],[f906,f613,f58,f54,f50,f1479])).
% 28.79/4.01  fof(f906,plain,(
% 28.79/4.01    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_34)),
% 28.79/4.01    inference(backward_demodulation,[],[f288,f905])).
% 28.79/4.01  fof(f288,plain,(
% 28.79/4.01    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 28.79/4.01    inference(backward_demodulation,[],[f30,f287])).
% 28.79/4.01  fof(f30,plain,(
% 28.79/4.01    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 28.79/4.01    inference(definition_unfolding,[],[f17,f22,f23])).
% 28.79/4.01  fof(f22,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 28.79/4.01    inference(cnf_transformation,[],[f11])).
% 28.79/4.01  fof(f11,axiom,(
% 28.79/4.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 28.79/4.01  fof(f17,plain,(
% 28.79/4.01    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 28.79/4.01    inference(cnf_transformation,[],[f16])).
% 28.79/4.01  fof(f16,plain,(
% 28.79/4.01    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 28.79/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 28.79/4.01  fof(f15,plain,(
% 28.79/4.01    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 28.79/4.01    introduced(choice_axiom,[])).
% 28.79/4.01  fof(f14,plain,(
% 28.79/4.01    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 28.79/4.01    inference(ennf_transformation,[],[f13])).
% 28.79/4.01  fof(f13,negated_conjecture,(
% 28.79/4.01    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 28.79/4.01    inference(negated_conjecture,[],[f12])).
% 28.79/4.01  fof(f12,conjecture,(
% 28.79/4.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 28.79/4.01  fof(f1477,plain,(
% 28.79/4.01    spl2_54 | ~spl2_2 | ~spl2_53),
% 28.79/4.01    inference(avatar_split_clause,[],[f1459,f1455,f42,f1475])).
% 28.79/4.01  fof(f1459,plain,(
% 28.79/4.01    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) ) | (~spl2_2 | ~spl2_53)),
% 28.79/4.01    inference(superposition,[],[f1456,f43])).
% 28.79/4.01  fof(f1457,plain,(
% 28.79/4.01    spl2_53 | ~spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_23 | ~spl2_39 | ~spl2_42),
% 28.79/4.01    inference(avatar_split_clause,[],[f1266,f860,f719,f352,f158,f113,f109,f46,f38,f1455])).
% 28.79/4.01  fof(f109,plain,(
% 28.79/4.01    spl2_12 <=> ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 28.79/4.01  fof(f113,plain,(
% 28.79/4.01    spl2_13 <=> ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 28.79/4.01  fof(f158,plain,(
% 28.79/4.01    spl2_15 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 28.79/4.01  fof(f352,plain,(
% 28.79/4.01    spl2_23 <=> ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 28.79/4.01  fof(f719,plain,(
% 28.79/4.01    spl2_39 <=> ! [X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 28.79/4.01  fof(f860,plain,(
% 28.79/4.01    spl2_42 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 28.79/4.01  fof(f1266,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_23 | ~spl2_39 | ~spl2_42)),
% 28.79/4.01    inference(forward_demodulation,[],[f1237,f1261])).
% 28.79/4.01  fof(f1261,plain,(
% 28.79/4.01    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl2_1 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_23 | ~spl2_39 | ~spl2_42)),
% 28.79/4.01    inference(backward_demodulation,[],[f110,f1231])).
% 28.79/4.01  fof(f1231,plain,(
% 28.79/4.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_1 | ~spl2_13 | ~spl2_15 | ~spl2_23 | ~spl2_39 | ~spl2_42)),
% 28.79/4.01    inference(backward_demodulation,[],[f159,f1201])).
% 28.79/4.01  fof(f1201,plain,(
% 28.79/4.01    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl2_1 | ~spl2_13 | ~spl2_23 | ~spl2_39 | ~spl2_42)),
% 28.79/4.01    inference(backward_demodulation,[],[f353,f1198])).
% 28.79/4.01  fof(f1198,plain,(
% 28.79/4.01    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | (~spl2_1 | ~spl2_13 | ~spl2_39 | ~spl2_42)),
% 28.79/4.01    inference(backward_demodulation,[],[f720,f1197])).
% 28.79/4.01  fof(f1197,plain,(
% 28.79/4.01    ( ! [X12] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12))) ) | (~spl2_1 | ~spl2_13 | ~spl2_42)),
% 28.79/4.01    inference(forward_demodulation,[],[f1150,f114])).
% 28.79/4.01  fof(f114,plain,(
% 28.79/4.01    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) ) | ~spl2_13),
% 28.79/4.01    inference(avatar_component_clause,[],[f113])).
% 28.79/4.01  fof(f1150,plain,(
% 28.79/4.01    ( ! [X12] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12)))) ) | (~spl2_1 | ~spl2_42)),
% 28.79/4.01    inference(superposition,[],[f861,f39])).
% 28.79/4.01  fof(f861,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | ~spl2_42),
% 28.79/4.01    inference(avatar_component_clause,[],[f860])).
% 28.79/4.01  fof(f720,plain,(
% 28.79/4.01    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1)) ) | ~spl2_39),
% 28.79/4.01    inference(avatar_component_clause,[],[f719])).
% 28.79/4.01  fof(f353,plain,(
% 28.79/4.01    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3)) ) | ~spl2_23),
% 28.79/4.01    inference(avatar_component_clause,[],[f352])).
% 28.79/4.01  fof(f159,plain,(
% 28.79/4.01    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) ) | ~spl2_15),
% 28.79/4.01    inference(avatar_component_clause,[],[f158])).
% 28.79/4.01  fof(f110,plain,(
% 28.79/4.01    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) ) | ~spl2_12),
% 28.79/4.01    inference(avatar_component_clause,[],[f109])).
% 28.79/4.01  fof(f1237,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_1 | ~spl2_3 | ~spl2_13 | ~spl2_23 | ~spl2_39 | ~spl2_42)),
% 28.79/4.01    inference(backward_demodulation,[],[f414,f1201])).
% 28.79/4.01  fof(f414,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_23)),
% 28.79/4.01    inference(superposition,[],[f47,f353])).
% 28.79/4.01  fof(f1436,plain,(
% 28.79/4.01    spl2_52 | ~spl2_34 | ~spl2_42),
% 28.79/4.01    inference(avatar_split_clause,[],[f1171,f860,f613,f1434])).
% 28.79/4.01  fof(f1171,plain,(
% 28.79/4.01    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | (~spl2_34 | ~spl2_42)),
% 28.79/4.01    inference(superposition,[],[f861,f614])).
% 28.79/4.01  fof(f1428,plain,(
% 28.79/4.01    spl2_51 | ~spl2_1 | ~spl2_13 | ~spl2_39 | ~spl2_42),
% 28.79/4.01    inference(avatar_split_clause,[],[f1198,f860,f719,f113,f38,f1426])).
% 28.79/4.01  fof(f1383,plain,(
% 28.79/4.01    spl2_48 | ~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_23 | ~spl2_39 | ~spl2_42),
% 28.79/4.01    inference(avatar_split_clause,[],[f1230,f860,f719,f352,f145,f113,f38,f1381])).
% 28.79/4.01  fof(f145,plain,(
% 28.79/4.01    spl2_14 <=> ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 28.79/4.01  fof(f1230,plain,(
% 28.79/4.01    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) ) | (~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_23 | ~spl2_39 | ~spl2_42)),
% 28.79/4.01    inference(backward_demodulation,[],[f146,f1201])).
% 28.79/4.01  fof(f146,plain,(
% 28.79/4.01    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)) ) | ~spl2_14),
% 28.79/4.01    inference(avatar_component_clause,[],[f145])).
% 28.79/4.01  fof(f1366,plain,(
% 28.79/4.01    spl2_47 | ~spl2_1 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_23 | ~spl2_39 | ~spl2_42),
% 28.79/4.01    inference(avatar_split_clause,[],[f1261,f860,f719,f352,f158,f113,f109,f38,f1364])).
% 28.79/4.01  fof(f862,plain,(
% 28.79/4.01    spl2_42 | ~spl2_4 | ~spl2_6 | ~spl2_8),
% 28.79/4.01    inference(avatar_split_clause,[],[f295,f66,f58,f50,f860])).
% 28.79/4.01  fof(f66,plain,(
% 28.79/4.01    spl2_8 <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 28.79/4.01  fof(f295,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | (~spl2_4 | ~spl2_6 | ~spl2_8)),
% 28.79/4.01    inference(backward_demodulation,[],[f67,f277])).
% 28.79/4.01  fof(f67,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | ~spl2_8),
% 28.79/4.01    inference(avatar_component_clause,[],[f66])).
% 28.79/4.01  fof(f721,plain,(
% 28.79/4.01    spl2_39 | ~spl2_26 | ~spl2_28),
% 28.79/4.01    inference(avatar_split_clause,[],[f528,f509,f478,f719])).
% 28.79/4.01  fof(f478,plain,(
% 28.79/4.01    spl2_26 <=> ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 28.79/4.01  fof(f509,plain,(
% 28.79/4.01    spl2_28 <=> ! [X7] : k4_xboole_0(X7,X7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 28.79/4.01  fof(f528,plain,(
% 28.79/4.01    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1)) ) | (~spl2_26 | ~spl2_28)),
% 28.79/4.01    inference(superposition,[],[f510,f479])).
% 28.79/4.01  fof(f479,plain,(
% 28.79/4.01    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) ) | ~spl2_26),
% 28.79/4.01    inference(avatar_component_clause,[],[f478])).
% 28.79/4.01  fof(f510,plain,(
% 28.79/4.01    ( ! [X7] : (k4_xboole_0(X7,X7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))) ) | ~spl2_28),
% 28.79/4.01    inference(avatar_component_clause,[],[f509])).
% 28.79/4.01  fof(f615,plain,(
% 28.79/4.01    spl2_34 | ~spl2_4 | ~spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f290,f58,f50,f613])).
% 28.79/4.01  fof(f290,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl2_4 | ~spl2_6)),
% 28.79/4.01    inference(backward_demodulation,[],[f51,f277])).
% 28.79/4.01  fof(f511,plain,(
% 28.79/4.01    spl2_28 | ~spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_16),
% 28.79/4.01    inference(avatar_split_clause,[],[f385,f174,f62,f58,f54,f50,f38,f509])).
% 28.79/4.01  fof(f174,plain,(
% 28.79/4.01    spl2_16 <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 28.79/4.01  fof(f385,plain,(
% 28.79/4.01    ( ! [X7] : (k4_xboole_0(X7,X7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))) ) | (~spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_16)),
% 28.79/4.01    inference(forward_demodulation,[],[f384,f39])).
% 28.79/4.01  fof(f384,plain,(
% 28.79/4.01    ( ! [X7] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k4_xboole_0(X7,k1_xboole_0),X7)) ) | (~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_16)),
% 28.79/4.01    inference(forward_demodulation,[],[f383,f293])).
% 28.79/4.01  fof(f383,plain,(
% 28.79/4.01    ( ! [X7] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k5_xboole_0(X7,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))),X7)) ) | (~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_16)),
% 28.79/4.01    inference(forward_demodulation,[],[f360,f277])).
% 28.79/4.01  fof(f360,plain,(
% 28.79/4.01    ( ! [X7] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))),X7)) ) | (~spl2_7 | ~spl2_16)),
% 28.79/4.01    inference(superposition,[],[f63,f175])).
% 28.79/4.01  fof(f175,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | ~spl2_16),
% 28.79/4.01    inference(avatar_component_clause,[],[f174])).
% 28.79/4.01  fof(f480,plain,(
% 28.79/4.01    spl2_26 | ~spl2_14 | ~spl2_23),
% 28.79/4.01    inference(avatar_split_clause,[],[f395,f352,f145,f478])).
% 28.79/4.01  fof(f395,plain,(
% 28.79/4.01    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) ) | (~spl2_14 | ~spl2_23)),
% 28.79/4.01    inference(superposition,[],[f353,f146])).
% 28.79/4.01  fof(f354,plain,(
% 28.79/4.01    spl2_23 | ~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_14 | ~spl2_16 | ~spl2_21),
% 28.79/4.01    inference(avatar_split_clause,[],[f322,f304,f174,f145,f113,f58,f50,f352])).
% 28.79/4.01  fof(f304,plain,(
% 28.79/4.01    spl2_21 <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 28.79/4.01  fof(f322,plain,(
% 28.79/4.01    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3)) ) | (~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_14 | ~spl2_16 | ~spl2_21)),
% 28.79/4.01    inference(backward_demodulation,[],[f153,f320])).
% 28.79/4.01  fof(f320,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) ) | (~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_16 | ~spl2_21)),
% 28.79/4.01    inference(forward_demodulation,[],[f319,f114])).
% 28.79/4.01  fof(f319,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0) ) | (~spl2_4 | ~spl2_6 | ~spl2_16 | ~spl2_21)),
% 28.79/4.01    inference(forward_demodulation,[],[f308,f277])).
% 28.79/4.01  fof(f308,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0) ) | (~spl2_16 | ~spl2_21)),
% 28.79/4.01    inference(superposition,[],[f305,f175])).
% 28.79/4.01  fof(f305,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_21),
% 28.79/4.01    inference(avatar_component_clause,[],[f304])).
% 28.79/4.01  fof(f153,plain,(
% 28.79/4.01    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k1_xboole_0,X3)))) ) | (~spl2_4 | ~spl2_14)),
% 28.79/4.01    inference(superposition,[],[f51,f146])).
% 28.79/4.01  fof(f306,plain,(
% 28.79/4.01    spl2_21 | ~spl2_1 | ~spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f261,f58,f38,f304])).
% 28.79/4.01  fof(f261,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_1 | ~spl2_6)),
% 28.79/4.01    inference(superposition,[],[f59,f39])).
% 28.79/4.01  fof(f176,plain,(
% 28.79/4.01    spl2_16 | ~spl2_1 | ~spl2_5),
% 28.79/4.01    inference(avatar_split_clause,[],[f130,f54,f38,f174])).
% 28.79/4.01  fof(f130,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | (~spl2_1 | ~spl2_5)),
% 28.79/4.01    inference(superposition,[],[f55,f39])).
% 28.79/4.01  fof(f160,plain,(
% 28.79/4.01    spl2_15 | ~spl2_9 | ~spl2_14),
% 28.79/4.01    inference(avatar_split_clause,[],[f152,f145,f83,f158])).
% 28.79/4.01  fof(f83,plain,(
% 28.79/4.01    spl2_9 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 28.79/4.01  fof(f152,plain,(
% 28.79/4.01    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) ) | (~spl2_9 | ~spl2_14)),
% 28.79/4.01    inference(superposition,[],[f84,f146])).
% 28.79/4.01  fof(f84,plain,(
% 28.79/4.01    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_9),
% 28.79/4.01    inference(avatar_component_clause,[],[f83])).
% 28.79/4.01  fof(f147,plain,(
% 28.79/4.01    spl2_14 | ~spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_13),
% 28.79/4.01    inference(avatar_split_clause,[],[f141,f113,f54,f50,f38,f145])).
% 28.79/4.01  fof(f141,plain,(
% 28.79/4.01    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,X4)) ) | (~spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_13)),
% 28.79/4.01    inference(forward_demodulation,[],[f140,f39])).
% 28.79/4.01  fof(f140,plain,(
% 28.79/4.01    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) ) | (~spl2_4 | ~spl2_5 | ~spl2_13)),
% 28.79/4.01    inference(forward_demodulation,[],[f134,f132])).
% 28.79/4.01  fof(f134,plain,(
% 28.79/4.01    ( ! [X4] : (k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)))) ) | (~spl2_5 | ~spl2_13)),
% 28.79/4.01    inference(superposition,[],[f114,f55])).
% 28.79/4.01  fof(f115,plain,(
% 28.79/4.01    spl2_13 | ~spl2_4 | ~spl2_11),
% 28.79/4.01    inference(avatar_split_clause,[],[f104,f97,f50,f113])).
% 28.79/4.01  fof(f97,plain,(
% 28.79/4.01    spl2_11 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 28.79/4.01  fof(f104,plain,(
% 28.79/4.01    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) ) | (~spl2_4 | ~spl2_11)),
% 28.79/4.01    inference(superposition,[],[f98,f51])).
% 28.79/4.01  fof(f98,plain,(
% 28.79/4.01    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | ~spl2_11),
% 28.79/4.01    inference(avatar_component_clause,[],[f97])).
% 28.79/4.01  fof(f111,plain,(
% 28.79/4.01    spl2_12 | ~spl2_2 | ~spl2_11),
% 28.79/4.01    inference(avatar_split_clause,[],[f102,f97,f42,f109])).
% 28.79/4.01  fof(f102,plain,(
% 28.79/4.01    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) ) | (~spl2_2 | ~spl2_11)),
% 28.79/4.01    inference(superposition,[],[f98,f43])).
% 28.79/4.01  fof(f99,plain,(
% 28.79/4.01    spl2_11 | ~spl2_3 | ~spl2_10),
% 28.79/4.01    inference(avatar_split_clause,[],[f95,f91,f46,f97])).
% 28.79/4.01  fof(f91,plain,(
% 28.79/4.01    spl2_10 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 28.79/4.01    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 28.79/4.01  fof(f95,plain,(
% 28.79/4.01    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | (~spl2_3 | ~spl2_10)),
% 28.79/4.01    inference(superposition,[],[f47,f93])).
% 28.79/4.01  fof(f93,plain,(
% 28.79/4.01    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_10),
% 28.79/4.01    inference(avatar_component_clause,[],[f91])).
% 28.79/4.01  fof(f94,plain,(
% 28.79/4.01    spl2_10 | ~spl2_1 | ~spl2_9),
% 28.79/4.01    inference(avatar_split_clause,[],[f86,f83,f38,f91])).
% 28.79/4.01  fof(f86,plain,(
% 28.79/4.01    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl2_1 | ~spl2_9)),
% 28.79/4.01    inference(superposition,[],[f84,f39])).
% 28.79/4.01  fof(f85,plain,(
% 28.79/4.01    spl2_9 | ~spl2_1 | ~spl2_4),
% 28.79/4.01    inference(avatar_split_clause,[],[f78,f50,f38,f83])).
% 28.79/4.01  fof(f78,plain,(
% 28.79/4.01    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_1 | ~spl2_4)),
% 28.79/4.01    inference(superposition,[],[f51,f39])).
% 28.79/4.01  fof(f68,plain,(
% 28.79/4.01    spl2_8),
% 28.79/4.01    inference(avatar_split_clause,[],[f36,f66])).
% 28.79/4.01  fof(f36,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 28.79/4.01    inference(backward_demodulation,[],[f32,f35])).
% 28.79/4.01  fof(f32,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 28.79/4.01    inference(definition_unfolding,[],[f21,f22,f23])).
% 28.79/4.01  fof(f21,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 28.79/4.01    inference(cnf_transformation,[],[f4])).
% 28.79/4.01  fof(f4,axiom,(
% 28.79/4.01    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 28.79/4.01  fof(f64,plain,(
% 28.79/4.01    spl2_7),
% 28.79/4.01    inference(avatar_split_clause,[],[f34,f62])).
% 28.79/4.01  fof(f34,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 28.79/4.01    inference(definition_unfolding,[],[f26,f22])).
% 28.79/4.01  fof(f26,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 28.79/4.01    inference(cnf_transformation,[],[f6])).
% 28.79/4.01  fof(f6,axiom,(
% 28.79/4.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 28.79/4.01  fof(f60,plain,(
% 28.79/4.01    spl2_6),
% 28.79/4.01    inference(avatar_split_clause,[],[f33,f58])).
% 28.79/4.01  fof(f33,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 28.79/4.01    inference(definition_unfolding,[],[f25,f23])).
% 28.79/4.01  fof(f25,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 28.79/4.01    inference(cnf_transformation,[],[f7])).
% 28.79/4.01  fof(f7,axiom,(
% 28.79/4.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 28.79/4.01  fof(f56,plain,(
% 28.79/4.01    spl2_5),
% 28.79/4.01    inference(avatar_split_clause,[],[f31,f54])).
% 28.79/4.01  fof(f31,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 28.79/4.01    inference(definition_unfolding,[],[f19,f23,f23])).
% 28.79/4.01  fof(f19,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 28.79/4.01    inference(cnf_transformation,[],[f1])).
% 28.79/4.01  fof(f1,axiom,(
% 28.79/4.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 28.79/4.01  fof(f52,plain,(
% 28.79/4.01    spl2_4),
% 28.79/4.01    inference(avatar_split_clause,[],[f29,f50])).
% 28.79/4.01  fof(f29,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 28.79/4.01    inference(definition_unfolding,[],[f24,f23])).
% 28.79/4.01  fof(f24,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 28.79/4.01    inference(cnf_transformation,[],[f3])).
% 28.79/4.01  fof(f3,axiom,(
% 28.79/4.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 28.79/4.01  fof(f48,plain,(
% 28.79/4.01    spl2_3),
% 28.79/4.01    inference(avatar_split_clause,[],[f28,f46])).
% 28.79/4.01  fof(f28,plain,(
% 28.79/4.01    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 28.79/4.01    inference(cnf_transformation,[],[f10])).
% 28.79/4.01  fof(f10,axiom,(
% 28.79/4.01    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 28.79/4.01  fof(f44,plain,(
% 28.79/4.01    spl2_2),
% 28.79/4.01    inference(avatar_split_clause,[],[f20,f42])).
% 28.79/4.01  fof(f20,plain,(
% 28.79/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 28.79/4.01    inference(cnf_transformation,[],[f2])).
% 28.79/4.01  fof(f2,axiom,(
% 28.79/4.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 28.79/4.01  fof(f40,plain,(
% 28.79/4.01    spl2_1),
% 28.79/4.01    inference(avatar_split_clause,[],[f18,f38])).
% 28.79/4.01  fof(f18,plain,(
% 28.79/4.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 28.79/4.01    inference(cnf_transformation,[],[f5])).
% 28.79/4.01  fof(f5,axiom,(
% 28.79/4.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 28.79/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 28.79/4.01  % SZS output end Proof for theBenchmark
% 28.79/4.01  % (12493)------------------------------
% 28.79/4.01  % (12493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.79/4.01  % (12493)Termination reason: Refutation
% 28.79/4.01  
% 28.79/4.01  % (12493)Memory used [KB]: 100552
% 28.79/4.01  % (12493)Time elapsed: 3.586 s
% 28.79/4.01  % (12493)------------------------------
% 28.79/4.01  % (12493)------------------------------
% 28.79/4.03  % (12485)Success in time 3.666 s
%------------------------------------------------------------------------------
