%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:00 EST 2020

% Result     : Theorem 38.63s
% Output     : Refutation 38.78s
% Verified   : 
% Statistics : Number of formulae       : 1146 (15221 expanded)
%              Number of leaves         :  191 (6122 expanded)
%              Depth                    :   35
%              Number of atoms          : 7944 (57181 expanded)
%              Number of equality atoms :  960 (15031 expanded)
%              Maximal formula depth    :   60 (   8 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84861,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f51,f57,f61,f65,f69,f77,f91,f96,f102,f115,f122,f127,f135,f154,f159,f170,f176,f207,f226,f269,f273,f303,f312,f329,f333,f337,f373,f386,f391,f395,f460,f481,f548,f558,f577,f582,f587,f592,f642,f679,f683,f695,f699,f805,f809,f813,f817,f947,f951,f955,f1027,f1137,f1141,f1234,f1309,f1429,f1489,f1665,f1669,f1720,f1773,f1777,f1877,f2047,f2051,f2079,f2087,f2091,f2095,f2726,f2730,f2734,f2742,f3186,f3194,f3206,f3414,f3537,f3546,f3690,f3911,f4270,f4449,f4453,f4457,f4461,f4833,f4925,f5019,f5577,f5634,f5638,f5772,f5932,f5940,f5948,f5952,f5960,f5968,f6835,f7173,f7265,f7269,f7282,f7298,f7314,f8727,f8731,f9127,f9139,f9794,f9798,f9802,f9830,f10331,f12103,f12482,f12890,f14380,f14384,f14835,f14839,f15047,f15239,f15979,f15991,f16007,f17160,f17164,f17609,f17613,f17965,f18341,f18345,f18463,f18991,f19205,f19217,f19374,f19507,f19674,f19678,f20229,f20434,f20836,f22193,f22205,f22209,f23463,f27686,f28191,f28195,f28954,f29426,f34668,f34680,f35248,f35498,f36548,f36572,f36588,f40538,f41937,f42805,f46547,f48076,f57540,f57548,f57845,f59430,f59747,f60050,f60295,f60605,f60850,f60854,f82565,f84251,f84588])).

fof(f84588,plain,
    ( ~ spl3_23
    | ~ spl3_69
    | ~ spl3_220
    | spl3_246
    | ~ spl3_350
    | ~ spl3_370
    | ~ spl3_407 ),
    inference(avatar_contradiction_clause,[],[f84587])).

fof(f84587,plain,
    ( $false
    | ~ spl3_23
    | ~ spl3_69
    | ~ spl3_220
    | spl3_246
    | ~ spl3_350
    | ~ spl3_370
    | ~ spl3_407 ),
    inference(subsumption_resolution,[],[f84586,f65193])).

fof(f65193,plain,
    ( ! [X4] : k4_xboole_0(X4,sK2) = k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X4,sK2))))
    | ~ spl3_23
    | ~ spl3_69
    | ~ spl3_220
    | ~ spl3_350 ),
    inference(forward_demodulation,[],[f65192,f1140])).

fof(f1140,plain,
    ( ! [X4] : k4_xboole_0(X4,sK2) = k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4)))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f1139,plain,
    ( spl3_69
  <=> ! [X4] : k4_xboole_0(X4,sK2) = k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f65192,plain,
    ( ! [X4] : k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4))) = k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X4,sK2))))
    | ~ spl3_23
    | ~ spl3_220
    | ~ spl3_350 ),
    inference(forward_demodulation,[],[f64511,f206])).

fof(f206,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f64511,plain,
    ( ! [X4] : k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4))) = k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X4)),sK2))
    | ~ spl3_220
    | ~ spl3_350 ),
    inference(superposition,[],[f57547,f15978])).

fof(f15978,plain,
    ( ! [X22] : k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),sK2))
    | ~ spl3_220 ),
    inference(avatar_component_clause,[],[f15977])).

fof(f15977,plain,
    ( spl3_220
  <=> ! [X22] : k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_220])])).

fof(f57547,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ spl3_350 ),
    inference(avatar_component_clause,[],[f57546])).

fof(f57546,plain,
    ( spl3_350
  <=> ! [X1,X3,X2] : k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_350])])).

fof(f84586,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))))
    | spl3_246
    | ~ spl3_370
    | ~ spl3_407 ),
    inference(backward_demodulation,[],[f19673,f84344])).

fof(f84344,plain,
    ( ! [X41,X40] : k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X40,sK2))) = k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(X41,k4_xboole_0(sK2,k4_xboole_0(X40,X40)))))
    | ~ spl3_370
    | ~ spl3_407 ),
    inference(superposition,[],[f57844,f84250])).

fof(f84250,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(X0,X0)))
    | ~ spl3_407 ),
    inference(avatar_component_clause,[],[f84249])).

fof(f84249,plain,
    ( spl3_407
  <=> ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_407])])).

fof(f57844,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5)))
    | ~ spl3_370 ),
    inference(avatar_component_clause,[],[f57843])).

fof(f57843,plain,
    ( spl3_370
  <=> ! [X3,X5,X4] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_370])])).

fof(f19673,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK0))))))
    | spl3_246 ),
    inference(avatar_component_clause,[],[f19671])).

fof(f19671,plain,
    ( spl3_246
  <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_246])])).

fof(f84251,plain,
    ( spl3_407
    | ~ spl3_265
    | ~ spl3_404 ),
    inference(avatar_split_clause,[],[f82614,f82563,f27684,f84249])).

fof(f27684,plain,
    ( spl3_265
  <=> ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_265])])).

fof(f82563,plain,
    ( spl3_404
  <=> ! [X9] : k4_xboole_0(X9,sK2) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_404])])).

fof(f82614,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(X0,X0)))
    | ~ spl3_265
    | ~ spl3_404 ),
    inference(superposition,[],[f82564,f27685])).

fof(f27685,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))
    | ~ spl3_265 ),
    inference(avatar_component_clause,[],[f27684])).

fof(f82564,plain,
    ( ! [X9] : k4_xboole_0(X9,sK2) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))
    | ~ spl3_404 ),
    inference(avatar_component_clause,[],[f82563])).

fof(f82565,plain,
    ( spl3_404
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_69
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_120
    | ~ spl3_199
    | ~ spl3_234
    | ~ spl3_235
    | ~ spl3_337
    | ~ spl3_373
    | ~ spl3_380
    | ~ spl3_381 ),
    inference(avatar_split_clause,[],[f80324,f60852,f60848,f59428,f48074,f18461,f18343,f10329,f3184,f2728,f1667,f1139,f1025,f205,f67,f63,f82563])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1025,plain,
    ( spl3_67
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f1667,plain,
    ( spl3_88
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f2728,plain,
    ( spl3_113
  <=> ! [X1,X3,X2] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).

fof(f3184,plain,
    ( spl3_120
  <=> ! [X7,X6] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).

fof(f10329,plain,
    ( spl3_199
  <=> ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(X1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_199])])).

fof(f18343,plain,
    ( spl3_234
  <=> ! [X9] : k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_234])])).

fof(f18461,plain,
    ( spl3_235
  <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k5_xboole_0(X1,k4_xboole_0(X1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_235])])).

fof(f48074,plain,
    ( spl3_337
  <=> ! [X1,X0] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_337])])).

fof(f59428,plain,
    ( spl3_373
  <=> ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_373])])).

fof(f60848,plain,
    ( spl3_380
  <=> ! [X1,X3,X2] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_380])])).

fof(f60852,plain,
    ( spl3_381
  <=> ! [X15] : k4_xboole_0(X15,sK2) = k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_381])])).

fof(f80324,plain,
    ( ! [X9] : k4_xboole_0(X9,sK2) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_69
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_120
    | ~ spl3_199
    | ~ spl3_234
    | ~ spl3_235
    | ~ spl3_337
    | ~ spl3_373
    | ~ spl3_380
    | ~ spl3_381 ),
    inference(forward_demodulation,[],[f80323,f59429])).

fof(f59429,plain,
    ( ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),sK2)
    | ~ spl3_373 ),
    inference(avatar_component_clause,[],[f59428])).

fof(f80323,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1))) = k4_xboole_0(k4_xboole_0(X9,sK2),sK2)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_69
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_120
    | ~ spl3_199
    | ~ spl3_234
    | ~ spl3_235
    | ~ spl3_337
    | ~ spl3_380
    | ~ spl3_381 ),
    inference(backward_demodulation,[],[f53898,f80320])).

fof(f80320,plain,
    ( ! [X235,X234] : k4_xboole_0(k4_xboole_0(X234,sK2),k4_xboole_0(X235,k4_xboole_0(sK1,X234))) = k4_xboole_0(k4_xboole_0(X234,sK2),X235)
    | ~ spl3_67
    | ~ spl3_380
    | ~ spl3_381 ),
    inference(forward_demodulation,[],[f79642,f1026])).

fof(f1026,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f79642,plain,
    ( ! [X235,X234] : k4_xboole_0(k4_xboole_0(X234,sK2),k4_xboole_0(X235,k4_xboole_0(sK1,X234))) = k5_xboole_0(k4_xboole_0(X234,sK2),k4_xboole_0(X235,k4_xboole_0(X235,k4_xboole_0(X234,sK2))))
    | ~ spl3_380
    | ~ spl3_381 ),
    inference(superposition,[],[f60849,f60853])).

fof(f60853,plain,
    ( ! [X15] : k4_xboole_0(X15,sK2) = k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15))
    | ~ spl3_381 ),
    inference(avatar_component_clause,[],[f60852])).

fof(f60849,plain,
    ( ! [X2,X3,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))
    | ~ spl3_380 ),
    inference(avatar_component_clause,[],[f60848])).

fof(f53898,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1))) = k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_69
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_120
    | ~ spl3_199
    | ~ spl3_234
    | ~ spl3_235
    | ~ spl3_337 ),
    inference(forward_demodulation,[],[f53897,f10330])).

fof(f10330,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(X1,sK1))
    | ~ spl3_199 ),
    inference(avatar_component_clause,[],[f10329])).

fof(f53897,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9))) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK2)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_69
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_120
    | ~ spl3_234
    | ~ spl3_235
    | ~ spl3_337 ),
    inference(forward_demodulation,[],[f53896,f18569])).

fof(f18569,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k4_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(X7,X8)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_234
    | ~ spl3_235 ),
    inference(backward_demodulation,[],[f18447,f18568])).

fof(f18568,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,sK2))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_235 ),
    inference(forward_demodulation,[],[f18567,f206])).

fof(f18567,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_88
    | ~ spl3_113
    | ~ spl3_235 ),
    inference(forward_demodulation,[],[f18566,f5468])).

fof(f5468,plain,
    ( ! [X2,X3,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(forward_demodulation,[],[f5241,f206])).

fof(f5241,plain,
    ( ! [X2,X3,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3))
    | ~ spl3_7
    | ~ spl3_113 ),
    inference(superposition,[],[f64,f2729])).

fof(f2729,plain,
    ( ! [X2,X3,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)
    | ~ spl3_113 ),
    inference(avatar_component_clause,[],[f2728])).

fof(f64,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f18566,plain,
    ( ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2)) = k5_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X8,k4_xboole_0(X8,X9)))))
    | ~ spl3_8
    | ~ spl3_88
    | ~ spl3_235 ),
    inference(forward_demodulation,[],[f18504,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f18504,plain,
    ( ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2)) = k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2)))
    | ~ spl3_88
    | ~ spl3_235 ),
    inference(superposition,[],[f1668,f18462])).

fof(f18462,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k5_xboole_0(X1,k4_xboole_0(X1,sK2))
    | ~ spl3_235 ),
    inference(avatar_component_clause,[],[f18461])).

fof(f1668,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)
    | ~ spl3_88 ),
    inference(avatar_component_clause,[],[f1667])).

fof(f18447,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,sK2))))
    | ~ spl3_23
    | ~ spl3_88
    | ~ spl3_234 ),
    inference(forward_demodulation,[],[f18381,f206])).

fof(f18381,plain,
    ( ! [X8,X7] : k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),sK2)) = k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8)))))
    | ~ spl3_88
    | ~ spl3_234 ),
    inference(superposition,[],[f1668,f18344])).

fof(f18344,plain,
    ( ! [X9] : k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,sK2))
    | ~ spl3_234 ),
    inference(avatar_component_clause,[],[f18343])).

fof(f53896,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9))) = k5_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X9,k4_xboole_0(X9,sK2)))))
    | ~ spl3_69
    | ~ spl3_120
    | ~ spl3_337 ),
    inference(forward_demodulation,[],[f53731,f3185])).

fof(f3185,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X6,X7)))
    | ~ spl3_120 ),
    inference(avatar_component_clause,[],[f3184])).

fof(f53731,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9))) = k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),k4_xboole_0(X9,sK2)))
    | ~ spl3_69
    | ~ spl3_337 ),
    inference(superposition,[],[f48075,f1140])).

fof(f48075,plain,
    ( ! [X0,X1] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X1,X0)))
    | ~ spl3_337 ),
    inference(avatar_component_clause,[],[f48074])).

fof(f60854,plain,
    ( spl3_381
    | ~ spl3_67
    | ~ spl3_256
    | ~ spl3_375
    | ~ spl3_378 ),
    inference(avatar_split_clause,[],[f60817,f60603,f59745,f22191,f1025,f60852])).

fof(f22191,plain,
    ( spl3_256
  <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_256])])).

fof(f59745,plain,
    ( spl3_375
  <=> ! [X8] : k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_375])])).

fof(f60603,plain,
    ( spl3_378
  <=> ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_378])])).

fof(f60817,plain,
    ( ! [X15] : k4_xboole_0(X15,sK2) = k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15))
    | ~ spl3_67
    | ~ spl3_256
    | ~ spl3_375
    | ~ spl3_378 ),
    inference(forward_demodulation,[],[f60816,f59746])).

fof(f59746,plain,
    ( ! [X8] : k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))
    | ~ spl3_375 ),
    inference(avatar_component_clause,[],[f59745])).

fof(f60816,plain,
    ( ! [X15] : k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15)) = k5_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X15))
    | ~ spl3_67
    | ~ spl3_256
    | ~ spl3_378 ),
    inference(forward_demodulation,[],[f60725,f22192])).

fof(f22192,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8))
    | ~ spl3_256 ),
    inference(avatar_component_clause,[],[f22191])).

fof(f60725,plain,
    ( ! [X15] : k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15)) = k5_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(k4_xboole_0(sK1,X15),k4_xboole_0(sK1,X15)))
    | ~ spl3_67
    | ~ spl3_378 ),
    inference(superposition,[],[f1026,f60604])).

fof(f60604,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))
    | ~ spl3_378 ),
    inference(avatar_component_clause,[],[f60603])).

fof(f60850,plain,
    ( spl3_380
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(avatar_split_clause,[],[f5468,f2728,f205,f63,f60848])).

fof(f60605,plain,
    ( spl3_378
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_202
    | ~ spl3_238
    | ~ spl3_244
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_300
    | ~ spl3_303
    | ~ spl3_307
    | ~ spl3_310
    | ~ spl3_336
    | ~ spl3_377 ),
    inference(avatar_split_clause,[],[f60563,f60293,f46545,f42803,f41935,f40536,f36586,f35496,f20227,f19505,f19203,f12101,f9792,f9125,f7267,f5958,f5950,f5017,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1663,f1231,f1025,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f60603])).

fof(f88,plain,
    ( spl3_10
  <=> sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f93,plain,
    ( spl3_11
  <=> k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f100,plain,
    ( spl3_12
  <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k5_xboole_0(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f384,plain,
    ( spl3_36
  <=> ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f388,plain,
    ( spl3_37
  <=> k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f393,plain,
    ( spl3_38
  <=> ! [X5] : k4_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f478,plain,
    ( spl3_41
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f584,plain,
    ( spl3_50
  <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f681,plain,
    ( spl3_55
  <=> ! [X1] : k4_xboole_0(sK2,X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f693,plain,
    ( spl3_58
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f697,plain,
    ( spl3_59
  <=> ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f807,plain,
    ( spl3_61
  <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f945,plain,
    ( spl3_64
  <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f949,plain,
    ( spl3_65
  <=> ! [X10] : k4_xboole_0(sK2,X10) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1231,plain,
    ( spl3_71
  <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f1663,plain,
    ( spl3_87
  <=> ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f1718,plain,
    ( spl3_89
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f2049,plain,
    ( spl3_96
  <=> ! [X1,X2] : k4_xboole_0(k4_xboole_0(sK2,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X1),X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f2077,plain,
    ( spl3_103
  <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f2085,plain,
    ( spl3_105
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).

fof(f2724,plain,
    ( spl3_112
  <=> ! [X1,X2] : k4_xboole_0(k4_xboole_0(sK1,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X1),X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).

fof(f2740,plain,
    ( spl3_116
  <=> ! [X9,X10] : k4_xboole_0(k4_xboole_0(sK2,X9),X10) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X9),X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).

fof(f3192,plain,
    ( spl3_122
  <=> ! [X3,X4] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X4))) = k4_xboole_0(k4_xboole_0(sK2,X3),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).

fof(f3544,plain,
    ( spl3_128
  <=> ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(k4_xboole_0(sK1,sK1),k5_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).

fof(f3688,plain,
    ( spl3_134
  <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_134])])).

fof(f4268,plain,
    ( spl3_137
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).

fof(f4451,plain,
    ( spl3_139
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).

fof(f4455,plain,
    ( spl3_140
  <=> ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).

fof(f4459,plain,
    ( spl3_141
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).

fof(f5017,plain,
    ( spl3_145
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_145])])).

fof(f5950,plain,
    ( spl3_158
  <=> ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_158])])).

fof(f5958,plain,
    ( spl3_160
  <=> ! [X9] : k4_xboole_0(k4_xboole_0(sK1,X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_160])])).

fof(f7267,plain,
    ( spl3_166
  <=> ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_166])])).

fof(f9125,plain,
    ( spl3_183
  <=> ! [X9] : k4_xboole_0(sK1,X9) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_183])])).

fof(f9792,plain,
    ( spl3_189
  <=> ! [X1,X3,X2] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_189])])).

fof(f12101,plain,
    ( spl3_202
  <=> ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_202])])).

fof(f19203,plain,
    ( spl3_238
  <=> ! [X6] : k4_xboole_0(k4_xboole_0(sK1,sK1),X6) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_238])])).

fof(f19505,plain,
    ( spl3_244
  <=> ! [X8] : k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_244])])).

fof(f20227,plain,
    ( spl3_248
  <=> ! [X66] : k4_xboole_0(sK1,X66) = k4_xboole_0(k4_xboole_0(sK1,X66),X66) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_248])])).

fof(f35496,plain,
    ( spl3_285
  <=> ! [X7,X8,X6] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_285])])).

fof(f36586,plain,
    ( spl3_300
  <=> ! [X17] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X17,sK1))) = k4_xboole_0(k4_xboole_0(X17,sK1),X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_300])])).

fof(f40536,plain,
    ( spl3_303
  <=> ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_303])])).

fof(f41935,plain,
    ( spl3_307
  <=> ! [X9,X11,X8,X10] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X8,X9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_307])])).

fof(f42803,plain,
    ( spl3_310
  <=> ! [X18] : k4_xboole_0(k4_xboole_0(sK1,sK1),X18) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_310])])).

fof(f46545,plain,
    ( spl3_336
  <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_336])])).

fof(f60293,plain,
    ( spl3_377
  <=> ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_377])])).

fof(f60563,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_202
    | ~ spl3_238
    | ~ spl3_244
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_300
    | ~ spl3_303
    | ~ spl3_307
    | ~ spl3_310
    | ~ spl3_336
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60562,f19506])).

fof(f19506,plain,
    ( ! [X8] : k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))
    | ~ spl3_244 ),
    inference(avatar_component_clause,[],[f19505])).

fof(f60562,plain,
    ( ! [X1] : k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_202
    | ~ spl3_238
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_300
    | ~ spl3_303
    | ~ spl3_307
    | ~ spl3_310
    | ~ spl3_336
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60561,f19328])).

fof(f19328,plain,
    ( ! [X64,X65] : k4_xboole_0(k4_xboole_0(sK1,X64),X65) = k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X65,X64))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_238 ),
    inference(forward_demodulation,[],[f19319,f5372])).

fof(f5372,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X4)) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X4,X6)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(forward_demodulation,[],[f5197,f206])).

fof(f5197,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X4))
    | ~ spl3_8
    | ~ spl3_113 ),
    inference(superposition,[],[f2729,f68])).

fof(f19319,plain,
    ( ! [X64,X65] : k4_xboole_0(k4_xboole_0(sK1,X64),X65) = k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),X65)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_238 ),
    inference(backward_demodulation,[],[f13909,f19317])).

fof(f19317,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238 ),
    inference(backward_demodulation,[],[f4805,f19303])).

fof(f19303,plain,
    ( ! [X8] : k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238 ),
    inference(backward_demodulation,[],[f4033,f19302])).

fof(f19302,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238 ),
    inference(backward_demodulation,[],[f9428,f19301])).

fof(f19301,plain,
    ( ! [X18] : k4_xboole_0(k4_xboole_0(sK1,sK1),X18) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_137
    | ~ spl3_158
    | ~ spl3_238 ),
    inference(forward_demodulation,[],[f19300,f5951])).

fof(f5951,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,sK1)))
    | ~ spl3_158 ),
    inference(avatar_component_clause,[],[f5950])).

fof(f19300,plain,
    ( ! [X18] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X18,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_137
    | ~ spl3_238 ),
    inference(forward_demodulation,[],[f19299,f5372])).

fof(f19299,plain,
    ( ! [X18] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X18)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)
    | ~ spl3_113
    | ~ spl3_137
    | ~ spl3_238 ),
    inference(forward_demodulation,[],[f19261,f4269])).

fof(f4269,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))
    | ~ spl3_137 ),
    inference(avatar_component_clause,[],[f4268])).

fof(f19261,plain,
    ( ! [X18] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X18)) = k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(sK1,sK1))),X18)
    | ~ spl3_113
    | ~ spl3_238 ),
    inference(superposition,[],[f2729,f19204])).

fof(f19204,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK1,sK1),X6) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6))
    | ~ spl3_238 ),
    inference(avatar_component_clause,[],[f19203])).

fof(f9428,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X8),X8)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_183 ),
    inference(forward_demodulation,[],[f9427,f5018])).

fof(f5018,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))
    | ~ spl3_145 ),
    inference(avatar_component_clause,[],[f5017])).

fof(f9427,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X8)),X8)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_183 ),
    inference(forward_demodulation,[],[f9426,f5133])).

fof(f5133,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X3,X4))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(backward_demodulation,[],[f3823,f5128])).

fof(f5128,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),X10) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(backward_demodulation,[],[f4822,f5127])).

fof(f5127,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X9),X10),sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_112
    | ~ spl3_122
    | ~ spl3_134
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(forward_demodulation,[],[f5126,f4757])).

fof(f4757,plain,
    ( ! [X6,X5] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X5),X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6))
    | ~ spl3_112
    | ~ spl3_122
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4724,f3193])).

fof(f3193,plain,
    ( ! [X4,X3] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X4))) = k4_xboole_0(k4_xboole_0(sK2,X3),X4)
    | ~ spl3_122 ),
    inference(avatar_component_clause,[],[f3192])).

fof(f4724,plain,
    ( ! [X6,X5] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X5),X6))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6))
    | ~ spl3_112
    | ~ spl3_141 ),
    inference(superposition,[],[f4460,f2725])).

fof(f2725,plain,
    ( ! [X2,X1] : k4_xboole_0(k4_xboole_0(sK1,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X1),X2)))
    | ~ spl3_112 ),
    inference(avatar_component_clause,[],[f2724])).

fof(f4460,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))
    | ~ spl3_141 ),
    inference(avatar_component_clause,[],[f4459])).

fof(f5126,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134
    | ~ spl3_145 ),
    inference(forward_demodulation,[],[f5125,f3803])).

fof(f3803,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f3695,f3772])).

fof(f3772,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(backward_demodulation,[],[f1719,f3771])).

fof(f3771,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(sK2,k4_xboole_0(X0,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f3768,f950])).

fof(f950,plain,
    ( ! [X10] : k4_xboole_0(sK2,X10) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X10)))
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f949])).

fof(f3768,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(backward_demodulation,[],[f1761,f3765])).

fof(f3765,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))
    | ~ spl3_8
    | ~ spl3_61
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f3694,f808])).

fof(f808,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f807])).

fof(f3694,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X1,sK1)))
    | ~ spl3_8
    | ~ spl3_134 ),
    inference(superposition,[],[f3689,f68])).

fof(f3689,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))
    | ~ spl3_134 ),
    inference(avatar_component_clause,[],[f3688])).

fof(f1761,plain,
    ( ! [X0] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_89 ),
    inference(backward_demodulation,[],[f501,f1759])).

fof(f1759,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2))
    | ~ spl3_38
    | ~ spl3_55
    | ~ spl3_89 ),
    inference(forward_demodulation,[],[f1734,f682])).

fof(f682,plain,
    ( ! [X1] : k4_xboole_0(sK2,X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f681])).

fof(f1734,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2)))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2))
    | ~ spl3_38
    | ~ spl3_89 ),
    inference(superposition,[],[f394,f1719])).

fof(f394,plain,
    ( ! [X5] : k4_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X5))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f393])).

fof(f501,plain,
    ( ! [X0] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f443,f495])).

fof(f495,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(superposition,[],[f385,f480])).

fof(f480,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f478])).

fof(f385,plain,
    ( ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X7)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f384])).

fof(f443,plain,
    ( ! [X0] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK2,sK1),X0))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X0))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f177,f440])).

fof(f440,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f438,f95])).

fof(f95,plain,
    ( k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f438,plain,
    ( k4_xboole_0(sK2,sK2) = k5_xboole_0(sK2,sK2)
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f412,f423])).

fof(f423,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_10
    | ~ spl3_38 ),
    inference(superposition,[],[f394,f90])).

fof(f90,plain,
    ( sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f412,plain,
    ( k4_xboole_0(sK2,sK2) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))
    | ~ spl3_7
    | ~ spl3_37 ),
    inference(superposition,[],[f64,f390])).

fof(f390,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f388])).

fof(f177,plain,
    ( ! [X0] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),X0))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK2),X0))
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(superposition,[],[f101,f64])).

fof(f101,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k5_xboole_0(sK2,X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1719,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)))
    | ~ spl3_89 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f3695,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X2,sK1)))
    | ~ spl3_8
    | ~ spl3_134 ),
    inference(superposition,[],[f3689,f68])).

fof(f5125,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10)))
    | ~ spl3_23
    | ~ spl3_145 ),
    inference(forward_demodulation,[],[f5106,f206])).

fof(f5106,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X9)),X10)
    | ~ spl3_23
    | ~ spl3_145 ),
    inference(superposition,[],[f206,f5018])).

fof(f4822,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),X10) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X9),X10),sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4821,f4757])).

fof(f4821,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),X10)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4820,f4809])).

fof(f4809,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK1,sK1),X7) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X7),sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4808,f4802])).

fof(f4802,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(backward_demodulation,[],[f4460,f4791])).

fof(f4791,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6)
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4790,f3551])).

fof(f3551,plain,
    ( ! [X5] : k4_xboole_0(k4_xboole_0(sK1,sK1),X5) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X5))
    | ~ spl3_105
    | ~ spl3_128 ),
    inference(superposition,[],[f3545,f2086])).

fof(f2086,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))
    | ~ spl3_105 ),
    inference(avatar_component_clause,[],[f2085])).

fof(f3545,plain,
    ( ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(k4_xboole_0(sK1,sK1),k5_xboole_0(sK2,X0))
    | ~ spl3_128 ),
    inference(avatar_component_clause,[],[f3544])).

fof(f4790,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X6))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_116
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4742,f4599])).

fof(f4599,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X0),sK1))
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_116
    | ~ spl3_139 ),
    inference(backward_demodulation,[],[f1261,f4553])).

fof(f4553,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))
    | ~ spl3_116
    | ~ spl3_139 ),
    inference(superposition,[],[f4452,f2741])).

fof(f2741,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK2,X9),X10) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X9),X10)))
    | ~ spl3_116 ),
    inference(avatar_component_clause,[],[f2740])).

fof(f4452,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))
    | ~ spl3_139 ),
    inference(avatar_component_clause,[],[f4451])).

fof(f1261,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)))
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f1253,f1259])).

fof(f1259,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f1258,f586])).

fof(f586,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f584])).

fof(f1258,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f1252,f698])).

fof(f698,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f697])).

fof(f1252,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(superposition,[],[f946,f1233])).

fof(f1233,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f946,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sK2))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f945])).

fof(f1253,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)),X0)
    | ~ spl3_23
    | ~ spl3_71 ),
    inference(superposition,[],[f206,f1233])).

fof(f4742,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X6),sK1)))
    | ~ spl3_7
    | ~ spl3_141 ),
    inference(superposition,[],[f64,f4460])).

fof(f4808,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X7),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X7))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4807,f4269])).

fof(f4807,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X7),sK1) = k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(sK1,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4806,f4791])).

fof(f4806,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X7),sK1),sK1)
    | ~ spl3_8
    | ~ spl3_96
    | ~ spl3_116
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4743,f4756])).

fof(f4756,plain,
    ( ! [X4,X3] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X3),X4),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X3),X4))
    | ~ spl3_96
    | ~ spl3_116
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4723,f2741])).

fof(f4723,plain,
    ( ! [X4,X3] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X3),X4))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X3),X4))
    | ~ spl3_96
    | ~ spl3_141 ),
    inference(superposition,[],[f4460,f2050])).

fof(f2050,plain,
    ( ! [X2,X1] : k4_xboole_0(k4_xboole_0(sK2,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X1),X2)))
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f2049])).

fof(f4743,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X7),sK1))
    | ~ spl3_8
    | ~ spl3_141 ),
    inference(superposition,[],[f68,f4460])).

fof(f4820,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),sK1),X10)
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4819,f4791])).

fof(f4819,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X9),sK1),sK1),X10)
    | ~ spl3_23
    | ~ spl3_96
    | ~ spl3_116
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4745,f4756])).

fof(f4745,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X9),sK1)),X10)
    | ~ spl3_23
    | ~ spl3_141 ),
    inference(superposition,[],[f206,f4460])).

fof(f3823,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X3),X4)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f3706,f3772])).

fof(f3706,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X3,sK1))),X4)
    | ~ spl3_23
    | ~ spl3_134 ),
    inference(superposition,[],[f206,f3689])).

fof(f9426,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X8))),X8)
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_183 ),
    inference(forward_demodulation,[],[f9425,f206])).

fof(f9425,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),X8),X8)
    | ~ spl3_113
    | ~ spl3_183 ),
    inference(forward_demodulation,[],[f9332,f2729])).

fof(f9332,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X8))),X8)
    | ~ spl3_113
    | ~ spl3_183 ),
    inference(superposition,[],[f2729,f9126])).

fof(f9126,plain,
    ( ! [X9] : k4_xboole_0(sK1,X9) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))
    | ~ spl3_183 ),
    inference(avatar_component_clause,[],[f9125])).

fof(f4033,plain,
    ( ! [X8] : k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)))
    | ~ spl3_58
    | ~ spl3_103 ),
    inference(superposition,[],[f2078,f694])).

fof(f694,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f693])).

fof(f2078,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ spl3_103 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f4805,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK1,sK1),X0))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141 ),
    inference(backward_demodulation,[],[f4734,f4791])).

fof(f4734,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK2,X0),sK1))
    | ~ spl3_140
    | ~ spl3_141 ),
    inference(superposition,[],[f4456,f4460])).

fof(f4456,plain,
    ( ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(sK1,sK1),X7))
    | ~ spl3_140 ),
    inference(avatar_component_clause,[],[f4455])).

fof(f13909,plain,
    ( ! [X64,X65] : k4_xboole_0(k4_xboole_0(sK1,X64),X65) = k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189 ),
    inference(forward_demodulation,[],[f13908,f9126])).

fof(f13908,plain,
    ( ! [X64,X65] : k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,sK1),X64)),X65)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_189 ),
    inference(forward_demodulation,[],[f13907,f7268])).

fof(f7268,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1))
    | ~ spl3_166 ),
    inference(avatar_component_clause,[],[f7267])).

fof(f13907,plain,
    ( ! [X64,X65] : k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X64,sK1))),X65)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_160
    | ~ spl3_189 ),
    inference(forward_demodulation,[],[f13271,f5423])).

fof(f5423,plain,
    ( ! [X6,X5] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X5,X6))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(backward_demodulation,[],[f4757,f5418])).

fof(f5418,plain,
    ( ! [X30,X31] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X30),X31),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(forward_demodulation,[],[f5417,f3803])).

fof(f5417,plain,
    ( ! [X30,X31] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X30),X31),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(forward_demodulation,[],[f5416,f4757])).

fof(f5416,plain,
    ( ! [X30,X31] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X30),X31))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(forward_demodulation,[],[f5415,f5133])).

fof(f5415,plain,
    ( ! [X30,X31] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,sK1),X31)))
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_145 ),
    inference(forward_demodulation,[],[f5207,f206])).

fof(f5207,plain,
    ( ! [X30,X31] : k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,sK1),X31))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X30)),X31)
    | ~ spl3_113
    | ~ spl3_145 ),
    inference(superposition,[],[f2729,f5018])).

fof(f13271,plain,
    ( ! [X64,X65] : k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X64),sK1))),X65)
    | ~ spl3_160
    | ~ spl3_189 ),
    inference(superposition,[],[f9793,f5959])).

fof(f5959,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9))
    | ~ spl3_160 ),
    inference(avatar_component_clause,[],[f5958])).

fof(f9793,plain,
    ( ! [X2,X3,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3)
    | ~ spl3_189 ),
    inference(avatar_component_clause,[],[f9792])).

fof(f60561,plain,
    ( ! [X1] : k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X1,sK2),X1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_202
    | ~ spl3_238
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_300
    | ~ spl3_303
    | ~ spl3_307
    | ~ spl3_310
    | ~ spl3_336
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60560,f46878])).

fof(f46878,plain,
    ( ! [X57,X58] : k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,X58)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_300
    | ~ spl3_303
    | ~ spl3_307
    | ~ spl3_310
    | ~ spl3_336 ),
    inference(forward_demodulation,[],[f46876,f40787])).

fof(f40787,plain,
    ( ! [X94,X93] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X93,k4_xboole_0(sK1,sK1)),X94))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X93,X94)))
    | ~ spl3_23
    | ~ spl3_303 ),
    inference(forward_demodulation,[],[f40679,f206])).

fof(f40679,plain,
    ( ! [X94,X93] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X93,k4_xboole_0(sK1,sK1)),X94))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X93)),X94)
    | ~ spl3_23
    | ~ spl3_303 ),
    inference(superposition,[],[f206,f40537])).

fof(f40537,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))
    | ~ spl3_303 ),
    inference(avatar_component_clause,[],[f40536])).

fof(f46876,plain,
    ( ! [X57,X58] : k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(sK1,sK1)),X58)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_300
    | ~ spl3_307
    | ~ spl3_310
    | ~ spl3_336 ),
    inference(backward_demodulation,[],[f44697,f46875])).

fof(f46875,plain,
    ( ! [X28,X29] : k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(sK1,sK1)),X29) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X28,sK1),X28)),X29)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_310
    | ~ spl3_336 ),
    inference(forward_demodulation,[],[f46625,f46197])).

fof(f46197,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_310 ),
    inference(backward_demodulation,[],[f3829,f46193])).

fof(f46193,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_310 ),
    inference(forward_demodulation,[],[f46192,f4456])).

fof(f46192,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9)) = k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_310 ),
    inference(forward_demodulation,[],[f46068,f4812])).

fof(f4812,plain,
    ( ! [X10] : k4_xboole_0(k4_xboole_0(sK1,sK1),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X10),k4_xboole_0(k4_xboole_0(sK1,sK1),X10))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(backward_demodulation,[],[f1742,f4809])).

fof(f1742,plain,
    ( ! [X10] : k4_xboole_0(k4_xboole_0(sK1,sK1),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X10),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X10),sK1))
    | ~ spl3_87
    | ~ spl3_89 ),
    inference(superposition,[],[f1664,f1719])).

fof(f1664,plain,
    ( ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1))
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f46068,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9)) = k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9)))
    | ~ spl3_67
    | ~ spl3_310 ),
    inference(superposition,[],[f1026,f42804])).

fof(f42804,plain,
    ( ! [X18] : k4_xboole_0(k4_xboole_0(sK1,sK1),X18) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)
    | ~ spl3_310 ),
    inference(avatar_component_clause,[],[f42803])).

fof(f3829,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(sK1,sK1),X11)),X12)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f3712,f3772])).

fof(f3712,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X11,sK1)))),X12)
    | ~ spl3_23
    | ~ spl3_134 ),
    inference(superposition,[],[f206,f3689])).

fof(f46625,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(sK1,sK1)),X29))) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X28,sK1),X28)),X29)
    | ~ spl3_23
    | ~ spl3_336 ),
    inference(superposition,[],[f206,f46546])).

fof(f46546,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)
    | ~ spl3_336 ),
    inference(avatar_component_clause,[],[f46545])).

fof(f44697,plain,
    ( ! [X57,X58] : k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(k4_xboole_0(X57,sK1),X57)),X58)))
    | ~ spl3_112
    | ~ spl3_300
    | ~ spl3_307 ),
    inference(forward_demodulation,[],[f43193,f2725])).

fof(f43193,plain,
    ( ! [X57,X58] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(k4_xboole_0(X57,sK1),X57)),X58)))
    | ~ spl3_300
    | ~ spl3_307 ),
    inference(superposition,[],[f41936,f36587])).

fof(f36587,plain,
    ( ! [X17] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X17,sK1))) = k4_xboole_0(k4_xboole_0(X17,sK1),X17)
    | ~ spl3_300 ),
    inference(avatar_component_clause,[],[f36586])).

fof(f41936,plain,
    ( ! [X10,X8,X11,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X8,X9))))
    | ~ spl3_307 ),
    inference(avatar_component_clause,[],[f41935])).

fof(f60560,plain,
    ( ! [X1] : k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_202
    | ~ spl3_238
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60559,f694])).

fof(f60559,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))),k4_xboole_0(k4_xboole_0(sK1,sK1),X1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_202
    | ~ spl3_238
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60558,f68])).

fof(f60558,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(sK1,sK1),X1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_202
    | ~ spl3_238
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60557,f12102])).

fof(f12102,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))
    | ~ spl3_202 ),
    inference(avatar_component_clause,[],[f12101])).

fof(f60557,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X1,sK2)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_248
    | ~ spl3_285
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60556,f20388])).

fof(f20388,plain,
    ( ! [X19,X18] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X18,X19)) = k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(k4_xboole_0(sK1,X18),X19)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_248 ),
    inference(forward_demodulation,[],[f20387,f5128])).

fof(f20387,plain,
    ( ! [X19,X18] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X19) = k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(k4_xboole_0(sK1,X18),X19)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_248 ),
    inference(forward_demodulation,[],[f20296,f19302])).

fof(f20296,plain,
    ( ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(k4_xboole_0(sK1,X18),X19))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X18),k4_xboole_0(sK1,X18)),X19)
    | ~ spl3_113
    | ~ spl3_248 ),
    inference(superposition,[],[f2729,f20228])).

fof(f20228,plain,
    ( ! [X66] : k4_xboole_0(sK1,X66) = k4_xboole_0(k4_xboole_0(sK1,X66),X66)
    | ~ spl3_248 ),
    inference(avatar_component_clause,[],[f20227])).

fof(f60556,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(sK1,X1),sK2))))
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_285
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60555,f206])).

fof(f60555,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,X1))),sK2))
    | ~ spl3_113
    | ~ spl3_285
    | ~ spl3_377 ),
    inference(forward_demodulation,[],[f60404,f2729])).

fof(f60404,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))))
    | ~ spl3_285
    | ~ spl3_377 ),
    inference(superposition,[],[f35497,f60294])).

fof(f60294,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))
    | ~ spl3_377 ),
    inference(avatar_component_clause,[],[f60293])).

fof(f35497,plain,
    ( ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7)))))
    | ~ spl3_285 ),
    inference(avatar_component_clause,[],[f35496])).

fof(f60295,plain,
    ( spl3_377
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_120
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_177
    | ~ spl3_337
    | ~ spl3_375
    | ~ spl3_376 ),
    inference(avatar_split_clause,[],[f60290,f60048,f59745,f48074,f7312,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f3184,f2740,f2724,f2085,f2049,f2045,f1718,f1231,f953,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f60293])).

fof(f953,plain,
    ( spl3_66
  <=> ! [X4] : k4_xboole_0(sK2,X4) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f2045,plain,
    ( spl3_95
  <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).

fof(f7312,plain,
    ( spl3_177
  <=> ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_177])])).

fof(f60048,plain,
    ( spl3_376
  <=> ! [X1] : k4_xboole_0(X1,sK2) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_376])])).

fof(f60290,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_120
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_177
    | ~ spl3_337
    | ~ spl3_375
    | ~ spl3_376 ),
    inference(forward_demodulation,[],[f60289,f59746])).

fof(f60289,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_120
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_177
    | ~ spl3_337
    | ~ spl3_376 ),
    inference(forward_demodulation,[],[f60288,f4755])).

fof(f4755,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))
    | ~ spl3_61
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_120
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4754,f4452])).

fof(f4754,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X2,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))
    | ~ spl3_61
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_120
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4753,f3185])).

fof(f4753,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X2)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))
    | ~ spl3_61
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4722,f1068])).

fof(f1068,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))
    | ~ spl3_61
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f1042,f808])).

fof(f1042,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))
    | ~ spl3_61
    | ~ spl3_66 ),
    inference(superposition,[],[f808,f954])).

fof(f954,plain,
    ( ! [X4] : k4_xboole_0(sK2,X4) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2)))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f953])).

fof(f4722,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK2)))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))
    | ~ spl3_95
    | ~ spl3_141 ),
    inference(superposition,[],[f4460,f2046])).

fof(f2046,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(X1,sK2))))
    | ~ spl3_95 ),
    inference(avatar_component_clause,[],[f2045])).

fof(f60288,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k5_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,sK2))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_177
    | ~ spl3_337
    | ~ spl3_376 ),
    inference(forward_demodulation,[],[f60151,f8593])).

fof(f8593,plain,
    ( ! [X43,X44] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X43,X44))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_177 ),
    inference(forward_demodulation,[],[f8592,f5128])).

fof(f8592,plain,
    ( ! [X43,X44] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X43),X44)
    | ~ spl3_23
    | ~ spl3_112
    | ~ spl3_158
    | ~ spl3_177 ),
    inference(forward_demodulation,[],[f8591,f5951])).

fof(f8591,plain,
    ( ! [X43,X44] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X43,sK1))),X44) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44)
    | ~ spl3_23
    | ~ spl3_112
    | ~ spl3_177 ),
    inference(forward_demodulation,[],[f8518,f2902])).

fof(f2902,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X10),X11),X12) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X10),X11),X12)))
    | ~ spl3_112 ),
    inference(superposition,[],[f2725,f2725])).

fof(f8518,plain,
    ( ! [X43,X44] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X43,sK1))),X44) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44)))
    | ~ spl3_23
    | ~ spl3_177 ),
    inference(superposition,[],[f206,f7313])).

fof(f7313,plain,
    ( ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1))
    | ~ spl3_177 ),
    inference(avatar_component_clause,[],[f7312])).

fof(f60151,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k5_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),sK1),k4_xboole_0(X0,sK2)))
    | ~ spl3_337
    | ~ spl3_376 ),
    inference(superposition,[],[f48075,f60049])).

fof(f60049,plain,
    ( ! [X1] : k4_xboole_0(X1,sK2) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,X1),sK1))
    | ~ spl3_376 ),
    inference(avatar_component_clause,[],[f60048])).

fof(f60050,plain,
    ( spl3_376
    | ~ spl3_149
    | ~ spl3_375 ),
    inference(avatar_split_clause,[],[f59780,f59745,f5770,f60048])).

fof(f5770,plain,
    ( spl3_149
  <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).

fof(f59780,plain,
    ( ! [X1] : k4_xboole_0(X1,sK2) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,X1),sK1))
    | ~ spl3_149
    | ~ spl3_375 ),
    inference(superposition,[],[f59746,f5771])).

fof(f5771,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),sK1)
    | ~ spl3_149 ),
    inference(avatar_component_clause,[],[f5770])).

fof(f59747,plain,
    ( spl3_375
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_49
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_153
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_190
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_207
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_232
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(avatar_split_clause,[],[f59388,f57538,f35496,f28193,f23461,f20432,f17963,f15045,f14837,f14382,f12888,f9828,f9800,f9796,f7263,f5950,f5946,f5930,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f2045,f1771,f1718,f1667,f1663,f1231,f953,f949,f945,f807,f697,f693,f681,f584,f579,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f59745])).

fof(f579,plain,
    ( spl3_49
  <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f1771,plain,
    ( spl3_91
  <=> ! [X1,X2] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X1),X2))) = k4_xboole_0(k4_xboole_0(sK2,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f4923,plain,
    ( spl3_143
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_143])])).

fof(f5930,plain,
    ( spl3_153
  <=> ! [X16] : k4_xboole_0(sK2,X16) = k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).

fof(f5946,plain,
    ( spl3_157
  <=> ! [X7] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).

fof(f7263,plain,
    ( spl3_165
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).

fof(f9796,plain,
    ( spl3_190
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_190])])).

fof(f9800,plain,
    ( spl3_191
  <=> ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_191])])).

fof(f9828,plain,
    ( spl3_198
  <=> ! [X13] : k4_xboole_0(k4_xboole_0(sK1,X13),sK1) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_198])])).

fof(f12888,plain,
    ( spl3_207
  <=> ! [X36] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X36)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X36,k4_xboole_0(X36,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_207])])).

fof(f14382,plain,
    ( spl3_212
  <=> ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_212])])).

fof(f14837,plain,
    ( spl3_215
  <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_215])])).

fof(f15045,plain,
    ( spl3_217
  <=> ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_217])])).

fof(f17963,plain,
    ( spl3_232
  <=> ! [X8] : k4_xboole_0(X8,sK2) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_232])])).

fof(f20432,plain,
    ( spl3_249
  <=> ! [X14] : k4_xboole_0(k4_xboole_0(sK1,sK1),X14) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_249])])).

fof(f23461,plain,
    ( spl3_264
  <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X1,k4_xboole_0(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_264])])).

fof(f28193,plain,
    ( spl3_269
  <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_269])])).

fof(f57538,plain,
    ( spl3_348
  <=> ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_348])])).

fof(f59388,plain,
    ( ! [X8] : k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_49
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_153
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_190
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_207
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_232
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(backward_demodulation,[],[f18164,f59385])).

fof(f59385,plain,
    ( ! [X93] : k4_xboole_0(k4_xboole_0(sK1,sK1),X93) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_49
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_190
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59384,f9797])).

fof(f9797,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))
    | ~ spl3_190 ),
    inference(avatar_component_clause,[],[f9796])).

fof(f59384,plain,
    ( ! [X93] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_49
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59383,f808])).

fof(f59383,plain,
    ( ! [X93] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_49
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59382,f581])).

fof(f581,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f579])).

fof(f59382,plain,
    ( ! [X93] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59381,f30370])).

fof(f30370,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_264
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f30369,f64])).

fof(f30369,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(sK1,sK1))))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_264
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f30368,f206])).

fof(f30368,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_264
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f30367,f23462])).

fof(f23462,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X1,k4_xboole_0(sK1,X1))
    | ~ spl3_264 ),
    inference(avatar_component_clause,[],[f23461])).

fof(f30367,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f30366,f4456])).

fof(f30366,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X7,X8)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f30194,f14677])).

fof(f14677,plain,
    ( ! [X14,X15] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X14,X15))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212 ),
    inference(backward_demodulation,[],[f12021,f14622])).

fof(f14622,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X7)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X6)))),sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_212 ),
    inference(backward_demodulation,[],[f6649,f14610])).

fof(f14610,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_212 ),
    inference(forward_demodulation,[],[f14591,f5128])).

fof(f14591,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X11),X12) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_212 ),
    inference(backward_demodulation,[],[f10639,f14584])).

fof(f14584,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK1,sK1),X6) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_191
    | ~ spl3_212 ),
    inference(backward_demodulation,[],[f10632,f14583])).

fof(f14583,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8))
    | ~ spl3_36
    | ~ spl3_113
    | ~ spl3_143
    | ~ spl3_212 ),
    inference(forward_demodulation,[],[f14582,f4924])).

fof(f4924,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)
    | ~ spl3_143 ),
    inference(avatar_component_clause,[],[f4923])).

fof(f14582,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK2,X8),sK2) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8))
    | ~ spl3_36
    | ~ spl3_113
    | ~ spl3_212 ),
    inference(forward_demodulation,[],[f14555,f385])).

fof(f14555,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X8))),sK2)
    | ~ spl3_113
    | ~ spl3_212 ),
    inference(superposition,[],[f2729,f14383])).

fof(f14383,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))
    | ~ spl3_212 ),
    inference(avatar_component_clause,[],[f14382])).

fof(f10632,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_191 ),
    inference(forward_demodulation,[],[f10631,f5128])).

fof(f10631,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X6),X6)
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_91
    | ~ spl3_113
    | ~ spl3_191 ),
    inference(forward_demodulation,[],[f10630,f586])).

fof(f10630,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK1),X6),X6)
    | ~ spl3_23
    | ~ spl3_91
    | ~ spl3_113
    | ~ spl3_191 ),
    inference(forward_demodulation,[],[f10629,f1772])).

fof(f1772,plain,
    ( ! [X2,X1] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X1),X2))) = k4_xboole_0(k4_xboole_0(sK2,X1),X2)
    | ~ spl3_91 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f10629,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X6))),X6)
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_191 ),
    inference(forward_demodulation,[],[f10628,f206])).

fof(f10628,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),X6),X6)
    | ~ spl3_113
    | ~ spl3_191 ),
    inference(forward_demodulation,[],[f10542,f2729])).

fof(f10542,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X6))),X6)
    | ~ spl3_113
    | ~ spl3_191 ),
    inference(superposition,[],[f2729,f9801])).

fof(f9801,plain,
    ( ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,sK1),X2))
    | ~ spl3_191 ),
    inference(avatar_component_clause,[],[f9800])).

fof(f10639,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,X11)),X12)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191 ),
    inference(backward_demodulation,[],[f7410,f10632])).

fof(f7410,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_165 ),
    inference(backward_demodulation,[],[f5137,f7409])).

fof(f7409,plain,
    ( ! [X21,X22] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_158
    | ~ spl3_165 ),
    inference(forward_demodulation,[],[f7408,f5951])).

fof(f7408,plain,
    ( ! [X21,X22] : k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X21,X22),sK1)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_165 ),
    inference(forward_demodulation,[],[f7407,f5372])).

fof(f7407,plain,
    ( ! [X21,X22] : k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X21,X22)))
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_165 ),
    inference(forward_demodulation,[],[f7358,f206])).

fof(f7358,plain,
    ( ! [X21,X22] : k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X21)),X22)
    | ~ spl3_113
    | ~ spl3_165 ),
    inference(superposition,[],[f2729,f7264])).

fof(f7264,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))
    | ~ spl3_165 ),
    inference(avatar_component_clause,[],[f7263])).

fof(f5137,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12) = k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,X12))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145 ),
    inference(backward_demodulation,[],[f4797,f5128])).

fof(f4797,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12) = k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X11),X12)))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(backward_demodulation,[],[f1697,f4791])).

fof(f1697,plain,
    ( ! [X12,X11] : k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),sK1),X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12)
    | ~ spl3_23
    | ~ spl3_87 ),
    inference(superposition,[],[f206,f1664])).

fof(f6649,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X6)))),sK1)
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_157 ),
    inference(forward_demodulation,[],[f6648,f5454])).

fof(f5454,plain,
    ( ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10))))))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(forward_demodulation,[],[f5231,f206])).

fof(f5231,plain,
    ( ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10))))
    | ~ spl3_8
    | ~ spl3_113 ),
    inference(superposition,[],[f2729,f68])).

fof(f6648,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,sK1)))))),sK1)
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_157 ),
    inference(forward_demodulation,[],[f6588,f206])).

fof(f6588,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,sK1)))),sK1)
    | ~ spl3_113
    | ~ spl3_157 ),
    inference(superposition,[],[f5947,f2729])).

fof(f5947,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X7)
    | ~ spl3_157 ),
    inference(avatar_component_clause,[],[f5946])).

fof(f12021,plain,
    ( ! [X14,X15] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X15,k4_xboole_0(X15,X14)))),sK1)
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_198 ),
    inference(forward_demodulation,[],[f12020,f5454])).

fof(f12020,plain,
    ( ! [X14,X15] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X14,sK1)))))),sK1)
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_198 ),
    inference(forward_demodulation,[],[f11910,f206])).

fof(f11910,plain,
    ( ! [X14,X15] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X14,sK1)))),sK1)
    | ~ spl3_113
    | ~ spl3_198 ),
    inference(superposition,[],[f9829,f2729])).

fof(f9829,plain,
    ( ! [X13] : k4_xboole_0(k4_xboole_0(sK1,X13),sK1) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1)
    | ~ spl3_198 ),
    inference(avatar_component_clause,[],[f9828])).

fof(f30194,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))),sK1))
    | ~ spl3_88
    | ~ spl3_269 ),
    inference(superposition,[],[f1668,f28194])).

fof(f28194,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK1))
    | ~ spl3_269 ),
    inference(avatar_component_clause,[],[f28193])).

fof(f59381,plain,
    ( ! [X93] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK1,sK1)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_103
    | ~ spl3_113
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_249
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59380,f586])).

fof(f59380,plain,
    ( ! [X93] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_103
    | ~ spl3_113
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_249
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59379,f68])).

fof(f59379,plain,
    ( ! [X93] : k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_103
    | ~ spl3_113
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_249
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59378,f15156])).

fof(f15156,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_103
    | ~ spl3_215
    | ~ spl3_217 ),
    inference(backward_demodulation,[],[f4121,f15155])).

fof(f15155,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,X9)))
    | ~ spl3_8
    | ~ spl3_215
    | ~ spl3_217 ),
    inference(forward_demodulation,[],[f15092,f14838])).

fof(f14838,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8))
    | ~ spl3_215 ),
    inference(avatar_component_clause,[],[f14837])).

fof(f15092,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK2,X9),k4_xboole_0(sK2,X9)) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,X9)))
    | ~ spl3_8
    | ~ spl3_217 ),
    inference(superposition,[],[f68,f15046])).

fof(f15046,plain,
    ( ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),X7)
    | ~ spl3_217 ),
    inference(avatar_component_clause,[],[f15045])).

fof(f4121,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,X9))))
    | ~ spl3_23
    | ~ spl3_66
    | ~ spl3_95
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f4120,f954])).

fof(f4120,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,k4_xboole_0(X9,sK2))))))
    | ~ spl3_23
    | ~ spl3_95
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f4034,f206])).

fof(f4034,plain,
    ( ! [X9] : k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,k4_xboole_0(X9,sK2))))
    | ~ spl3_95
    | ~ spl3_103 ),
    inference(superposition,[],[f2078,f2046])).

fof(f59378,plain,
    ( ! [X93] : k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X93,sK2)))
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_249
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59377,f20433])).

fof(f20433,plain,
    ( ! [X14] : k4_xboole_0(k4_xboole_0(sK1,sK1),X14) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14)))
    | ~ spl3_249 ),
    inference(avatar_component_clause,[],[f20432])).

fof(f59377,plain,
    ( ! [X93] : k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2)))))
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59376,f206])).

fof(f59376,plain,
    ( ! [X93] : k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X93,sK2))),k4_xboole_0(X93,sK2)))
    | ~ spl3_113
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(forward_demodulation,[],[f59230,f2729])).

fof(f59230,plain,
    ( ! [X93] : k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK1,k4_xboole_0(X93,sK2)))))
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(superposition,[],[f35497,f57539])).

fof(f57539,plain,
    ( ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X2,sK2),sK2))
    | ~ spl3_348 ),
    inference(avatar_component_clause,[],[f57538])).

fof(f18164,plain,
    ( ! [X8] : k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(X8,sK2)))
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_103
    | ~ spl3_153
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(backward_demodulation,[],[f3990,f18159])).

fof(f18159,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_153
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(forward_demodulation,[],[f18158,f13007])).

fof(f13007,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(sK1,X1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_153
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f13006,f5931])).

fof(f5931,plain,
    ( ! [X16] : k4_xboole_0(sK2,X16) = k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2))
    | ~ spl3_153 ),
    inference(avatar_component_clause,[],[f5930])).

fof(f13006,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f12905,f206])).

fof(f12905,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),k4_xboole_0(sK1,sK2))
    | ~ spl3_58
    | ~ spl3_207 ),
    inference(superposition,[],[f12889,f694])).

fof(f12889,plain,
    ( ! [X36] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X36)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X36,k4_xboole_0(X36,sK2))
    | ~ spl3_207 ),
    inference(avatar_component_clause,[],[f12888])).

fof(f18158,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))))
    | ~ spl3_23
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(forward_demodulation,[],[f17983,f206])).

fof(f17983,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,sK2)))
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(superposition,[],[f17964,f12889])).

fof(f17964,plain,
    ( ! [X8] : k4_xboole_0(X8,sK2) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2)))
    | ~ spl3_232 ),
    inference(avatar_component_clause,[],[f17963])).

fof(f3990,plain,
    ( ! [X8] : k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK1,X8))) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK1,X8)))))
    | ~ spl3_64
    | ~ spl3_103 ),
    inference(superposition,[],[f2078,f946])).

fof(f59430,plain,
    ( spl3_373
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_49
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_69
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_153
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_190
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_207
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_232
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(avatar_split_clause,[],[f59389,f57538,f35496,f28193,f23461,f20432,f17963,f15045,f14837,f14382,f12888,f9828,f9800,f9796,f7263,f5950,f5946,f5930,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f2045,f1771,f1718,f1667,f1663,f1231,f1139,f953,f949,f945,f807,f697,f693,f681,f584,f579,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f59428])).

fof(f59389,plain,
    ( ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),sK2)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_49
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_66
    | ~ spl3_69
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_95
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_153
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_190
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_207
    | ~ spl3_212
    | ~ spl3_215
    | ~ spl3_217
    | ~ spl3_232
    | ~ spl3_249
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_285
    | ~ spl3_348 ),
    inference(backward_demodulation,[],[f10213,f59388])).

fof(f10213,plain,
    ( ! [X4] : k4_xboole_0(k4_xboole_0(X4,sK2),sK2) = k5_xboole_0(k4_xboole_0(X4,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X4))
    | ~ spl3_69
    | ~ spl3_190 ),
    inference(superposition,[],[f1140,f9797])).

fof(f57845,plain,
    ( spl3_370
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(avatar_split_clause,[],[f5228,f2728,f205,f57843])).

fof(f5228,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5)))
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(superposition,[],[f2729,f206])).

fof(f57548,plain,
    ( spl3_350
    | ~ spl3_6
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f1355,f1025,f59,f57546])).

fof(f59,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1355,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ spl3_6
    | ~ spl3_67 ),
    inference(superposition,[],[f60,f1026])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f57540,plain,
    ( spl3_348
    | ~ spl3_205
    | ~ spl3_303 ),
    inference(avatar_split_clause,[],[f40543,f40536,f12480,f57538])).

fof(f12480,plain,
    ( spl3_205
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(X1,sK2),sK2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_205])])).

fof(f40543,plain,
    ( ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X2,sK2),sK2))
    | ~ spl3_205
    | ~ spl3_303 ),
    inference(superposition,[],[f40537,f12481])).

fof(f12481,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(X1,sK2),sK2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1))
    | ~ spl3_205 ),
    inference(avatar_component_clause,[],[f12480])).

fof(f48076,plain,
    ( spl3_337
    | ~ spl3_67
    | ~ spl3_162 ),
    inference(avatar_split_clause,[],[f11575,f5966,f1025,f48074])).

fof(f5966,plain,
    ( spl3_162
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_162])])).

fof(f11575,plain,
    ( ! [X0,X1] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X1,X0)))
    | ~ spl3_67
    | ~ spl3_162 ),
    inference(superposition,[],[f5967,f1026])).

fof(f5967,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2))))
    | ~ spl3_162 ),
    inference(avatar_component_clause,[],[f5966])).

fof(f46547,plain,
    ( spl3_336
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_189
    | ~ spl3_271
    | ~ spl3_284
    | ~ spl3_310 ),
    inference(avatar_split_clause,[],[f46218,f42803,f35246,f28952,f9792,f4459,f4455,f4451,f4268,f3544,f2740,f2085,f2049,f1718,f1663,f1231,f1025,f945,f697,f584,f205,f67,f63,f46545])).

fof(f28952,plain,
    ( spl3_271
  <=> ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_271])])).

fof(f35246,plain,
    ( spl3_284
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(X1,sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_284])])).

fof(f46218,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_189
    | ~ spl3_271
    | ~ spl3_284
    | ~ spl3_310 ),
    inference(backward_demodulation,[],[f35428,f46193])).

fof(f35428,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)
    | ~ spl3_189
    | ~ spl3_271
    | ~ spl3_284 ),
    inference(forward_demodulation,[],[f35314,f28953])).

fof(f28953,plain,
    ( ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))
    | ~ spl3_271 ),
    inference(avatar_component_clause,[],[f28952])).

fof(f35314,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0)
    | ~ spl3_189
    | ~ spl3_284 ),
    inference(superposition,[],[f9793,f35247])).

fof(f35247,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(X1,sK1),X1)
    | ~ spl3_284 ),
    inference(avatar_component_clause,[],[f35246])).

fof(f42805,plain,
    ( spl3_310
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_137
    | ~ spl3_158
    | ~ spl3_238 ),
    inference(avatar_split_clause,[],[f19301,f19203,f5950,f4268,f2728,f205,f67,f42803])).

fof(f41937,plain,
    ( spl3_307
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_223 ),
    inference(avatar_split_clause,[],[f26001,f15989,f2728,f205,f67,f41935])).

fof(f15989,plain,
    ( spl3_223
  <=> ! [X1,X0,X2] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_223])])).

fof(f26001,plain,
    ( ! [X10,X8,X11,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X8,X9))))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_223 ),
    inference(backward_demodulation,[],[f359,f26000])).

fof(f26000,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10)))))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X11,X12))))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_223 ),
    inference(forward_demodulation,[],[f25999,f5372])).

fof(f25999,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X10)) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10))))))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_223 ),
    inference(forward_demodulation,[],[f25418,f206])).

fof(f25418,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X10)) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10))))
    | ~ spl3_8
    | ~ spl3_223 ),
    inference(superposition,[],[f15990,f68])).

fof(f15990,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))
    | ~ spl3_223 ),
    inference(avatar_component_clause,[],[f15989])).

fof(f359,plain,
    ( ! [X10,X8,X11,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X10,X11)))))))
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f358,f206])).

fof(f358,plain,
    ( ! [X10,X8,X11,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11)))))
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f357,f206])).

fof(f357,plain,
    ( ! [X10,X8,X11,X9] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11)))
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f356,f206])).

fof(f356,plain,
    ( ! [X10,X8,X11,X9] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))),X11)
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f342,f206])).

fof(f342,plain,
    ( ! [X10,X8,X11,X9] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11)
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f206])).

fof(f40538,plain,
    ( spl3_303
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_290
    | ~ spl3_296 ),
    inference(avatar_split_clause,[],[f40532,f36570,f36546,f28193,f23461,f14382,f9828,f9800,f7263,f5950,f5946,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1771,f1718,f1667,f1663,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f40536])).

fof(f36546,plain,
    ( spl3_290
  <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,sK1),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_290])])).

fof(f36570,plain,
    ( spl3_296
  <=> ! [X13] : k4_xboole_0(sK1,X13) = k5_xboole_0(k4_xboole_0(sK1,X13),k4_xboole_0(k4_xboole_0(X13,sK1),X13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_296])])).

fof(f40532,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_290
    | ~ spl3_296 ),
    inference(forward_demodulation,[],[f40531,f64])).

fof(f40531,plain,
    ( ! [X1] : k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_290
    | ~ spl3_296 ),
    inference(forward_demodulation,[],[f40530,f30370])).

fof(f40530,plain,
    ( ! [X1] : k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,sK1))
    | ~ spl3_88
    | ~ spl3_290
    | ~ spl3_296 ),
    inference(forward_demodulation,[],[f40373,f36547])).

fof(f36547,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,sK1),X1))
    | ~ spl3_290 ),
    inference(avatar_component_clause,[],[f36546])).

fof(f40373,plain,
    ( ! [X1] : k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))) = k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),sK1),k4_xboole_0(sK1,X1)))
    | ~ spl3_88
    | ~ spl3_296 ),
    inference(superposition,[],[f1668,f36571])).

fof(f36571,plain,
    ( ! [X13] : k4_xboole_0(sK1,X13) = k5_xboole_0(k4_xboole_0(sK1,X13),k4_xboole_0(k4_xboole_0(X13,sK1),X13))
    | ~ spl3_296 ),
    inference(avatar_component_clause,[],[f36570])).

fof(f36588,plain,
    ( spl3_300
    | ~ spl3_112
    | ~ spl3_166
    | ~ spl3_173
    | ~ spl3_253
    | ~ spl3_283
    | ~ spl3_284 ),
    inference(avatar_split_clause,[],[f35388,f35246,f34678,f20834,f7296,f7267,f2724,f36586])).

fof(f7296,plain,
    ( spl3_173
  <=> ! [X4] : k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_173])])).

fof(f20834,plain,
    ( spl3_253
  <=> ! [X7] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) = k4_xboole_0(sK1,k4_xboole_0(X7,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_253])])).

fof(f34678,plain,
    ( spl3_283
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_283])])).

fof(f35388,plain,
    ( ! [X17] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X17,sK1))) = k4_xboole_0(k4_xboole_0(X17,sK1),X17)
    | ~ spl3_112
    | ~ spl3_166
    | ~ spl3_173
    | ~ spl3_253
    | ~ spl3_283
    | ~ spl3_284 ),
    inference(forward_demodulation,[],[f35294,f35213])).

fof(f35213,plain,
    ( ! [X11] : k4_xboole_0(sK1,k4_xboole_0(X11,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X11,sK1),X11))
    | ~ spl3_166
    | ~ spl3_173
    | ~ spl3_253
    | ~ spl3_283 ),
    inference(forward_demodulation,[],[f35212,f7297])).

fof(f7297,plain,
    ( ! [X4] : k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))
    | ~ spl3_173 ),
    inference(avatar_component_clause,[],[f7296])).

fof(f35212,plain,
    ( ! [X11] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X11)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X11,sK1),X11))
    | ~ spl3_166
    | ~ spl3_253
    | ~ spl3_283 ),
    inference(forward_demodulation,[],[f35134,f7268])).

fof(f35134,plain,
    ( ! [X11] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,sK1))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X11,sK1),X11))
    | ~ spl3_253
    | ~ spl3_283 ),
    inference(superposition,[],[f20835,f34679])).

fof(f34679,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)
    | ~ spl3_283 ),
    inference(avatar_component_clause,[],[f34678])).

fof(f20835,plain,
    ( ! [X7] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) = k4_xboole_0(sK1,k4_xboole_0(X7,X7))
    | ~ spl3_253 ),
    inference(avatar_component_clause,[],[f20834])).

fof(f35294,plain,
    ( ! [X17] : k4_xboole_0(k4_xboole_0(X17,sK1),X17) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X17,sK1),X17)))
    | ~ spl3_112
    | ~ spl3_284 ),
    inference(superposition,[],[f2725,f35247])).

fof(f36572,plain,
    ( spl3_296
    | ~ spl3_244
    | ~ spl3_284 ),
    inference(avatar_split_clause,[],[f35290,f35246,f19505,f36570])).

fof(f35290,plain,
    ( ! [X13] : k4_xboole_0(sK1,X13) = k5_xboole_0(k4_xboole_0(sK1,X13),k4_xboole_0(k4_xboole_0(X13,sK1),X13))
    | ~ spl3_244
    | ~ spl3_284 ),
    inference(superposition,[],[f19506,f35247])).

fof(f36548,plain,
    ( spl3_290
    | ~ spl3_140
    | ~ spl3_284 ),
    inference(avatar_split_clause,[],[f35278,f35246,f4455,f36546])).

fof(f35278,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,sK1),X1))
    | ~ spl3_140
    | ~ spl3_284 ),
    inference(superposition,[],[f4456,f35247])).

fof(f35498,plain,
    ( spl3_285
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_223 ),
    inference(avatar_split_clause,[],[f26002,f15989,f2728,f205,f67,f63,f35496])).

fof(f26002,plain,
    ( ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7)))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_223 ),
    inference(backward_demodulation,[],[f366,f26000])).

fof(f366,plain,
    ( ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8)))))))
    | ~ spl3_7
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f352,f206])).

fof(f352,plain,
    ( ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8)))))
    | ~ spl3_7
    | ~ spl3_23 ),
    inference(superposition,[],[f64,f206])).

fof(f35248,plain,
    ( spl3_284
    | ~ spl3_280
    | ~ spl3_283 ),
    inference(avatar_split_clause,[],[f35093,f34678,f34666,f35246])).

fof(f34666,plain,
    ( spl3_280
  <=> ! [X57] : k4_xboole_0(k4_xboole_0(sK1,sK1),X57) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_280])])).

fof(f35093,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(X1,sK1),X1)
    | ~ spl3_280
    | ~ spl3_283 ),
    inference(superposition,[],[f34679,f34667])).

fof(f34667,plain,
    ( ! [X57] : k4_xboole_0(k4_xboole_0(sK1,sK1),X57) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1))
    | ~ spl3_280 ),
    inference(avatar_component_clause,[],[f34666])).

fof(f34680,plain,
    ( spl3_283
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_163
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_237
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_272 ),
    inference(avatar_split_clause,[],[f32860,f29424,f28193,f23461,f18989,f18339,f14382,f9828,f9800,f8725,f7263,f6833,f5950,f5946,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1771,f1718,f1667,f1663,f1231,f1025,f949,f945,f811,f807,f697,f681,f584,f555,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f34678])).

fof(f555,plain,
    ( spl3_47
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f811,plain,
    ( spl3_62
  <=> ! [X2] : k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f6833,plain,
    ( spl3_163
  <=> ! [X29] : k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k4_xboole_0(k4_xboole_0(X29,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).

fof(f8725,plain,
    ( spl3_179
  <=> ! [X4] : k4_xboole_0(k4_xboole_0(X4,sK1),sK1) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).

fof(f18339,plain,
    ( spl3_233
  <=> ! [X1,X0,X2] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_233])])).

fof(f18989,plain,
    ( spl3_237
  <=> ! [X7] : k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_237])])).

fof(f29424,plain,
    ( spl3_272
  <=> ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_272])])).

fof(f32860,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_163
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_237
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_272 ),
    inference(forward_demodulation,[],[f32830,f29488])).

fof(f29488,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(X7,sK1),X7) = k5_xboole_0(k4_xboole_0(X7,sK1),k4_xboole_0(X7,sK1))
    | ~ spl3_67
    | ~ spl3_272 ),
    inference(superposition,[],[f1026,f29425])).

fof(f29425,plain,
    ( ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,sK1)))
    | ~ spl3_272 ),
    inference(avatar_component_clause,[],[f29424])).

fof(f32830,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_163
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_237
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_272 ),
    inference(backward_demodulation,[],[f18993,f32809])).

fof(f32809,plain,
    ( ! [X39] : k4_xboole_0(X39,sK1) = k4_xboole_0(k4_xboole_0(X39,sK1),sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_272 ),
    inference(backward_demodulation,[],[f6744,f32806])).

fof(f32806,plain,
    ( ! [X10] : k4_xboole_0(X10,sK1) = k5_xboole_0(k4_xboole_0(X10,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X10))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_264
    | ~ spl3_269
    | ~ spl3_272 ),
    inference(backward_demodulation,[],[f29490,f32805])).

fof(f32805,plain,
    ( ! [X57] : k4_xboole_0(k4_xboole_0(sK1,sK1),X57) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_264
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f32804,f5951])).

fof(f32804,plain,
    ( ! [X57] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_264
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f32803,f557])).

fof(f557,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f555])).

fof(f32803,plain,
    ( ! [X57] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_264
    | ~ spl3_269 ),
    inference(forward_demodulation,[],[f32802,f30370])).

fof(f32802,plain,
    ( ! [X57] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(sK1,sK1)))
    | ~ spl3_62
    | ~ spl3_179
    | ~ spl3_233
    | ~ spl3_264 ),
    inference(forward_demodulation,[],[f32801,f23462])).

fof(f32801,plain,
    ( ! [X57] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(sK1,k4_xboole_0(X57,sK1))))
    | ~ spl3_62
    | ~ spl3_179
    | ~ spl3_233 ),
    inference(forward_demodulation,[],[f30842,f812])).

fof(f812,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f811])).

fof(f30842,plain,
    ( ! [X57] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),sK1)))))
    | ~ spl3_179
    | ~ spl3_233 ),
    inference(superposition,[],[f18340,f8726])).

fof(f8726,plain,
    ( ! [X4] : k4_xboole_0(k4_xboole_0(X4,sK1),sK1) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl3_179 ),
    inference(avatar_component_clause,[],[f8725])).

fof(f18340,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))
    | ~ spl3_233 ),
    inference(avatar_component_clause,[],[f18339])).

fof(f29490,plain,
    ( ! [X10] : k4_xboole_0(X10,sK1) = k5_xboole_0(k4_xboole_0(X10,sK1),k4_xboole_0(k4_xboole_0(X10,sK1),k4_xboole_0(X10,sK1)))
    | ~ spl3_103
    | ~ spl3_272 ),
    inference(superposition,[],[f2078,f29425])).

fof(f6744,plain,
    ( ! [X39] : k4_xboole_0(k4_xboole_0(X39,sK1),sK1) = k5_xboole_0(k4_xboole_0(X39,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X39))
    | ~ spl3_67
    | ~ spl3_158 ),
    inference(superposition,[],[f1026,f5951])).

fof(f18993,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK1))
    | ~ spl3_163
    | ~ spl3_237 ),
    inference(superposition,[],[f18990,f6834])).

fof(f6834,plain,
    ( ! [X29] : k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k4_xboole_0(k4_xboole_0(X29,sK1),sK1)
    | ~ spl3_163 ),
    inference(avatar_component_clause,[],[f6833])).

fof(f18990,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,sK2))
    | ~ spl3_237 ),
    inference(avatar_component_clause,[],[f18989])).

fof(f34668,plain,
    ( spl3_280
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_62
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_88
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_157
    | ~ spl3_158
    | ~ spl3_165
    | ~ spl3_179
    | ~ spl3_191
    | ~ spl3_198
    | ~ spl3_212
    | ~ spl3_233
    | ~ spl3_264
    | ~ spl3_269 ),
    inference(avatar_split_clause,[],[f32805,f28193,f23461,f18339,f14382,f9828,f9800,f8725,f7263,f5950,f5946,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1771,f1718,f1667,f1663,f1231,f949,f945,f811,f807,f697,f681,f584,f555,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f34666])).

fof(f29426,plain,
    ( spl3_272
    | ~ spl3_8
    | ~ spl3_271 ),
    inference(avatar_split_clause,[],[f29000,f28952,f67,f29424])).

fof(f29000,plain,
    ( ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,sK1)))
    | ~ spl3_8
    | ~ spl3_271 ),
    inference(superposition,[],[f28953,f68])).

fof(f28954,plain,
    ( spl3_271
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_145
    | ~ spl3_183
    | ~ spl3_268 ),
    inference(avatar_split_clause,[],[f28800,f28189,f9125,f5017,f1025,f205,f28952])).

fof(f28189,plain,
    ( spl3_268
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_268])])).

fof(f28800,plain,
    ( ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_145
    | ~ spl3_183
    | ~ spl3_268 ),
    inference(forward_demodulation,[],[f28799,f1026])).

fof(f28799,plain,
    ( ! [X11] : k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11))) = k5_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_145
    | ~ spl3_183
    | ~ spl3_268 ),
    inference(forward_demodulation,[],[f28798,f9393])).

fof(f9393,plain,
    ( ! [X2] : k4_xboole_0(sK1,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2))))
    | ~ spl3_23
    | ~ spl3_145
    | ~ spl3_183 ),
    inference(forward_demodulation,[],[f9306,f5018])).

fof(f9306,plain,
    ( ! [X2] : k4_xboole_0(sK1,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X2)))))
    | ~ spl3_23
    | ~ spl3_183 ),
    inference(superposition,[],[f9126,f206])).

fof(f28798,plain,
    ( ! [X11] : k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11))) = k5_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(sK1,sK1),X11)))))
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_268 ),
    inference(forward_demodulation,[],[f28635,f206])).

fof(f28635,plain,
    ( ! [X11] : k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11))) = k5_xboole_0(X11,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X11)),k4_xboole_0(k4_xboole_0(sK1,sK1),X11)))
    | ~ spl3_67
    | ~ spl3_268 ),
    inference(superposition,[],[f1026,f28190])).

fof(f28190,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),X1)
    | ~ spl3_268 ),
    inference(avatar_component_clause,[],[f28189])).

fof(f28195,plain,
    ( spl3_269
    | ~ spl3_149
    | ~ spl3_260 ),
    inference(avatar_split_clause,[],[f23221,f22207,f5770,f28193])).

fof(f22207,plain,
    ( spl3_260
  <=> ! [X12] : k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,sK1),X12)) = k4_xboole_0(X12,k4_xboole_0(sK1,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_260])])).

fof(f23221,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK1))
    | ~ spl3_149
    | ~ spl3_260 ),
    inference(superposition,[],[f22208,f5771])).

fof(f22208,plain,
    ( ! [X12] : k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,sK1),X12)) = k4_xboole_0(X12,k4_xboole_0(sK1,X12))
    | ~ spl3_260 ),
    inference(avatar_component_clause,[],[f22207])).

fof(f28191,plain,
    ( spl3_268
    | ~ spl3_113
    | ~ spl3_259 ),
    inference(avatar_split_clause,[],[f22781,f22203,f2728,f28189])).

fof(f22203,plain,
    ( spl3_259
  <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_259])])).

fof(f22781,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),X1)
    | ~ spl3_113
    | ~ spl3_259 ),
    inference(superposition,[],[f22204,f2729])).

fof(f22204,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8)))
    | ~ spl3_259 ),
    inference(avatar_component_clause,[],[f22203])).

fof(f27686,plain,
    ( spl3_265
    | ~ spl3_138
    | ~ spl3_241 ),
    inference(avatar_split_clause,[],[f25158,f19215,f4447,f27684])).

fof(f4447,plain,
    ( spl3_138
  <=> ! [X0] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(sK2,k4_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).

fof(f19215,plain,
    ( spl3_241
  <=> ! [X1] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_241])])).

fof(f25158,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))
    | ~ spl3_138
    | ~ spl3_241 ),
    inference(superposition,[],[f19216,f4448])).

fof(f4448,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(sK2,k4_xboole_0(X0,sK1))
    | ~ spl3_138 ),
    inference(avatar_component_clause,[],[f4447])).

fof(f19216,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))
    | ~ spl3_241 ),
    inference(avatar_component_clause,[],[f19215])).

fof(f23463,plain,
    ( spl3_264
    | ~ spl3_140
    | ~ spl3_260 ),
    inference(avatar_split_clause,[],[f23261,f22207,f4455,f23461])).

fof(f23261,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X1,k4_xboole_0(sK1,X1))
    | ~ spl3_140
    | ~ spl3_260 ),
    inference(superposition,[],[f22208,f4456])).

fof(f22209,plain,
    ( spl3_260
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_248 ),
    inference(avatar_split_clause,[],[f20383,f20227,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f1025,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f22207])).

fof(f20383,plain,
    ( ! [X12] : k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,sK1),X12)) = k4_xboole_0(X12,k4_xboole_0(sK1,X12))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_248 ),
    inference(forward_demodulation,[],[f20292,f19302])).

fof(f20292,plain,
    ( ! [X12] : k4_xboole_0(X12,k4_xboole_0(sK1,X12)) = k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,X12),k4_xboole_0(sK1,X12)))
    | ~ spl3_67
    | ~ spl3_248 ),
    inference(superposition,[],[f1026,f20228])).

fof(f22205,plain,
    ( spl3_259
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_248 ),
    inference(avatar_split_clause,[],[f20377,f20227,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f22203])).

fof(f20377,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_248 ),
    inference(forward_demodulation,[],[f20289,f19302])).

fof(f20289,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8)))
    | ~ spl3_8
    | ~ spl3_248 ),
    inference(superposition,[],[f68,f20228])).

fof(f22193,plain,
    ( spl3_256
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238 ),
    inference(avatar_split_clause,[],[f19302,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f22191])).

fof(f20836,plain,
    ( spl3_253
    | ~ spl3_58
    | ~ spl3_249 ),
    inference(avatar_split_clause,[],[f20466,f20432,f693,f20834])).

fof(f20466,plain,
    ( ! [X7] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) = k4_xboole_0(sK1,k4_xboole_0(X7,X7))
    | ~ spl3_58
    | ~ spl3_249 ),
    inference(superposition,[],[f694,f20433])).

fof(f20434,plain,
    ( spl3_249
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_120
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_142
    | ~ spl3_227
    | ~ spl3_243
    | ~ spl3_247 ),
    inference(avatar_split_clause,[],[f19952,f19676,f19372,f16005,f4831,f4451,f4268,f3184,f2728,f2724,f205,f67,f20432])).

fof(f4831,plain,
    ( spl3_142
  <=> ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_142])])).

fof(f16005,plain,
    ( spl3_227
  <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_227])])).

fof(f19372,plain,
    ( spl3_243
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_243])])).

fof(f19676,plain,
    ( spl3_247
  <=> ! [X23,X24] : k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),X23),X24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_247])])).

fof(f19952,plain,
    ( ! [X14] : k4_xboole_0(k4_xboole_0(sK1,sK1),X14) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_120
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_142
    | ~ spl3_227
    | ~ spl3_243
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f19951,f17133])).

fof(f17133,plain,
    ( ! [X25] : k4_xboole_0(k4_xboole_0(sK1,sK1),X25) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X25),X25))
    | ~ spl3_120
    | ~ spl3_139
    | ~ spl3_142
    | ~ spl3_227 ),
    inference(forward_demodulation,[],[f17132,f4452])).

fof(f17132,plain,
    ( ! [X25] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X25,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X25),X25))
    | ~ spl3_120
    | ~ spl3_142
    | ~ spl3_227 ),
    inference(forward_demodulation,[],[f17058,f3185])).

fof(f17058,plain,
    ( ! [X25] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X25),X25)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X25)),sK1)
    | ~ spl3_142
    | ~ spl3_227 ),
    inference(superposition,[],[f4832,f16006])).

fof(f16006,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2))
    | ~ spl3_227 ),
    inference(avatar_component_clause,[],[f16005])).

fof(f4832,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6)
    | ~ spl3_142 ),
    inference(avatar_component_clause,[],[f4831])).

fof(f19951,plain,
    ( ! [X14] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X14),X14))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_137
    | ~ spl3_243
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f19950,f5372])).

fof(f19950,plain,
    ( ! [X14] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X14),X14)) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(sK1,X14),X14))
    | ~ spl3_112
    | ~ spl3_137
    | ~ spl3_243
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f19788,f19379])).

fof(f19379,plain,
    ( ! [X4,X5] : k4_xboole_0(k4_xboole_0(sK1,X4),X5) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X4),X5),k4_xboole_0(sK1,sK1))
    | ~ spl3_112
    | ~ spl3_243 ),
    inference(superposition,[],[f19373,f2725])).

fof(f19373,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1))
    | ~ spl3_243 ),
    inference(avatar_component_clause,[],[f19372])).

fof(f19788,plain,
    ( ! [X14] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X14),X14)) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X14),X14),k4_xboole_0(sK1,sK1)))
    | ~ spl3_137
    | ~ spl3_247 ),
    inference(superposition,[],[f19677,f4269])).

fof(f19677,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),X23),X24)
    | ~ spl3_247 ),
    inference(avatar_component_clause,[],[f19676])).

fof(f20229,plain,
    ( spl3_248
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_147
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_247 ),
    inference(avatar_split_clause,[],[f20095,f19676,f19203,f9125,f5632,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f335,f331,f205,f100,f93,f88,f67,f63,f20227])).

fof(f331,plain,
    ( spl3_33
  <=> ! [X0] : k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f335,plain,
    ( spl3_34
  <=> ! [X0] : k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f5632,plain,
    ( spl3_147
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).

fof(f20095,plain,
    ( ! [X66] : k4_xboole_0(sK1,X66) = k4_xboole_0(k4_xboole_0(sK1,X66),X66)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_147
    | ~ spl3_183
    | ~ spl3_238
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f20094,f9126])).

fof(f20094,plain,
    ( ! [X66] : k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(sK1,sK1),X66)) = k4_xboole_0(k4_xboole_0(sK1,X66),X66)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_147
    | ~ spl3_238
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f20093,f19204])).

fof(f20093,plain,
    ( ! [X66] : k4_xboole_0(k4_xboole_0(sK1,X66),X66) = k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X66,X66)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_147
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f20092,f5723])).

fof(f5723,plain,
    ( ! [X6,X5] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X5),X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X5,X6))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_147 ),
    inference(forward_demodulation,[],[f5655,f5423])).

fof(f5655,plain,
    ( ! [X6,X5] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X5),X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6))
    | ~ spl3_112
    | ~ spl3_147 ),
    inference(superposition,[],[f5633,f2725])).

fof(f5633,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK1)
    | ~ spl3_147 ),
    inference(avatar_component_clause,[],[f5632])).

fof(f20092,plain,
    ( ! [X66] : k4_xboole_0(k4_xboole_0(sK1,X66),X66) = k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X66),X66),sK1))
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_112
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f20091,f2725])).

fof(f20091,plain,
    ( ! [X66] : k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X66),X66),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X66),X66)))
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_247 ),
    inference(forward_demodulation,[],[f19836,f332])).

fof(f332,plain,
    ( ! [X0] : k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f331])).

fof(f19836,plain,
    ( ! [X66] : k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X66),X66),sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X66),X66)))
    | ~ spl3_34
    | ~ spl3_247 ),
    inference(superposition,[],[f336,f19677])).

fof(f336,plain,
    ( ! [X0] : k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f335])).

fof(f19678,plain,
    ( spl3_247
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_238
    | ~ spl3_243 ),
    inference(avatar_split_clause,[],[f19491,f19372,f19203,f9792,f9125,f7267,f5958,f5950,f5017,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19676])).

fof(f19491,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),X23),X24)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_238
    | ~ spl3_243 ),
    inference(forward_demodulation,[],[f19490,f2725])).

fof(f19490,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_238
    | ~ spl3_243 ),
    inference(forward_demodulation,[],[f19489,f19373])).

fof(f19489,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(sK1,sK1)),X24)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_160
    | ~ spl3_166
    | ~ spl3_183
    | ~ spl3_189
    | ~ spl3_238
    | ~ spl3_243 ),
    inference(forward_demodulation,[],[f19488,f19328])).

fof(f19488,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X23)))),X24)
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_189
    | ~ spl3_243 ),
    inference(forward_demodulation,[],[f19487,f206])).

fof(f19487,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),X23)),X24)
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_189
    | ~ spl3_243 ),
    inference(forward_demodulation,[],[f19486,f2729])).

fof(f19486,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X23)))),X24)
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_189
    | ~ spl3_243 ),
    inference(forward_demodulation,[],[f19445,f5472])).

fof(f5472,plain,
    ( ! [X12,X10,X13,X11] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X11,X12),X13))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X12))),X13)
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(forward_demodulation,[],[f5244,f206])).

fof(f5244,plain,
    ( ! [X12,X10,X13,X11] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X11,X12),X13))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X10)),X12),X13)
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(superposition,[],[f206,f2729])).

fof(f19445,plain,
    ( ! [X24,X23] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X23)))),X24) = k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,X23),X24)))
    | ~ spl3_189
    | ~ spl3_243 ),
    inference(superposition,[],[f9793,f19373])).

fof(f19674,plain,
    ( ~ spl3_246
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_134
    | ~ spl3_158
    | spl3_169
    | ~ spl3_173
    | ~ spl3_231 ),
    inference(avatar_split_clause,[],[f19161,f17611,f7296,f7279,f5950,f3688,f1775,f1718,f949,f807,f697,f693,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f19671])).

fof(f1775,plain,
    ( spl3_92
  <=> ! [X1] : k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f7279,plain,
    ( spl3_169
  <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_169])])).

fof(f17611,plain,
    ( spl3_231
  <=> ! [X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),X11) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_231])])).

fof(f19161,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK0))))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_134
    | ~ spl3_158
    | spl3_169
    | ~ spl3_173
    | ~ spl3_231 ),
    inference(backward_demodulation,[],[f7281,f19160])).

fof(f19160,plain,
    ( ! [X21] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X21,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X21,X21)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_134
    | ~ spl3_158
    | ~ spl3_173
    | ~ spl3_231 ),
    inference(forward_demodulation,[],[f19159,f698])).

fof(f19159,plain,
    ( ! [X21] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X21,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X21,X21)))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_134
    | ~ spl3_158
    | ~ spl3_173
    | ~ spl3_231 ),
    inference(forward_demodulation,[],[f19158,f6773])).

fof(f6773,plain,
    ( ! [X1] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X1,sK1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_134
    | ~ spl3_158 ),
    inference(backward_demodulation,[],[f3774,f6718])).

fof(f6718,plain,
    ( ! [X4] : k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))
    | ~ spl3_58
    | ~ spl3_158 ),
    inference(superposition,[],[f694,f5951])).

fof(f3774,plain,
    ( ! [X1] : k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X1,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_134 ),
    inference(backward_demodulation,[],[f1957,f3771])).

fof(f1957,plain,
    ( ! [X1] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))
    | ~ spl3_55
    | ~ spl3_89
    | ~ spl3_92 ),
    inference(forward_demodulation,[],[f1936,f682])).

fof(f1936,plain,
    ( ! [X1] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))
    | ~ spl3_89
    | ~ spl3_92 ),
    inference(superposition,[],[f1776,f1719])).

fof(f1776,plain,
    ( ! [X1] : k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,X1)))
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f1775])).

fof(f19158,plain,
    ( ! [X21] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X21,X21))))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X21,sK1)))
    | ~ spl3_92
    | ~ spl3_173
    | ~ spl3_231 ),
    inference(forward_demodulation,[],[f19084,f7297])).

fof(f19084,plain,
    ( ! [X21] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X21,X21))))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X21)))
    | ~ spl3_92
    | ~ spl3_231 ),
    inference(superposition,[],[f1776,f17612])).

fof(f17612,plain,
    ( ! [X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),X11) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11)))
    | ~ spl3_231 ),
    inference(avatar_component_clause,[],[f17611])).

fof(f7281,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))))))
    | spl3_169 ),
    inference(avatar_component_clause,[],[f7279])).

fof(f19507,plain,
    ( spl3_244
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238 ),
    inference(avatar_split_clause,[],[f19303,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19505])).

fof(f19374,plain,
    ( spl3_243
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_103
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_140
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_183
    | ~ spl3_238 ),
    inference(avatar_split_clause,[],[f19317,f19203,f9125,f5950,f5017,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19372])).

fof(f19217,plain,
    ( spl3_241
    | ~ spl3_35
    | ~ spl3_231 ),
    inference(avatar_split_clause,[],[f19065,f17611,f371,f19215])).

fof(f371,plain,
    ( spl3_35
  <=> ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f19065,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))
    | ~ spl3_35
    | ~ spl3_231 ),
    inference(superposition,[],[f372,f17612])).

fof(f372,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f371])).

fof(f19205,plain,
    ( spl3_238
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_143
    | ~ spl3_145
    | ~ spl3_191
    | ~ spl3_212 ),
    inference(avatar_split_clause,[],[f14584,f14382,f9800,f5017,f4923,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1771,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19203])).

fof(f18991,plain,
    ( spl3_237
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_67
    | ~ spl3_153
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(avatar_split_clause,[],[f18162,f17963,f12888,f5930,f1025,f945,f693,f205,f18989])).

fof(f18162,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,sK2))
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_67
    | ~ spl3_153
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(backward_demodulation,[],[f1313,f18159])).

fof(f1313,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,X7))))
    | ~ spl3_64
    | ~ spl3_67 ),
    inference(superposition,[],[f1026,f946])).

fof(f18463,plain,
    ( spl3_235
    | ~ spl3_7
    | ~ spl3_232 ),
    inference(avatar_split_clause,[],[f18000,f17963,f63,f18461])).

fof(f18000,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k5_xboole_0(X1,k4_xboole_0(X1,sK2))
    | ~ spl3_7
    | ~ spl3_232 ),
    inference(superposition,[],[f64,f17964])).

fof(f18345,plain,
    ( spl3_234
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_153
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(avatar_split_clause,[],[f18161,f17963,f12888,f5930,f945,f693,f205,f63,f18343])).

fof(f18161,plain,
    ( ! [X9] : k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,sK2))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_153
    | ~ spl3_207
    | ~ spl3_232 ),
    inference(backward_demodulation,[],[f977,f18159])).

fof(f977,plain,
    ( ! [X9] : k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(sK1,X9))))
    | ~ spl3_7
    | ~ spl3_64 ),
    inference(superposition,[],[f64,f946])).

fof(f18341,plain,
    ( spl3_233
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f364,f205,f67,f18339])).

fof(f364,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f348,f206])).

fof(f348,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f68])).

fof(f17965,plain,
    ( spl3_232
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_67
    | ~ spl3_69
    | ~ spl3_94
    | ~ spl3_113
    | ~ spl3_125
    | ~ spl3_138
    | ~ spl3_230 ),
    inference(avatar_split_clause,[],[f17820,f17607,f4447,f3204,f2728,f1875,f1139,f1025,f807,f205,f17963])).

fof(f1875,plain,
    ( spl3_94
  <=> ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f3204,plain,
    ( spl3_125
  <=> ! [X7,X8] : k4_xboole_0(sK2,k4_xboole_0(X7,X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f17607,plain,
    ( spl3_230
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_230])])).

fof(f17820,plain,
    ( ! [X8] : k4_xboole_0(X8,sK2) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2)))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_67
    | ~ spl3_69
    | ~ spl3_94
    | ~ spl3_113
    | ~ spl3_125
    | ~ spl3_138
    | ~ spl3_230 ),
    inference(forward_demodulation,[],[f17819,f1140])).

fof(f17819,plain,
    ( ! [X8] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK1,X8)))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_67
    | ~ spl3_94
    | ~ spl3_113
    | ~ spl3_125
    | ~ spl3_138
    | ~ spl3_230 ),
    inference(forward_demodulation,[],[f17818,f5451])).

fof(f5451,plain,
    ( ! [X6] : k4_xboole_0(sK2,k4_xboole_0(sK1,X6)) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(sK2,k4_xboole_0(X6,sK1))))
    | ~ spl3_61
    | ~ spl3_94
    | ~ spl3_113
    | ~ spl3_125 ),
    inference(forward_demodulation,[],[f5450,f808])).

fof(f5450,plain,
    ( ! [X6] : k4_xboole_0(sK2,k4_xboole_0(sK2,X6)) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(sK2,k4_xboole_0(X6,sK1))))
    | ~ spl3_94
    | ~ spl3_113
    | ~ spl3_125 ),
    inference(forward_demodulation,[],[f5229,f3205])).

fof(f3205,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(X7,X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8))
    | ~ spl3_125 ),
    inference(avatar_component_clause,[],[f3204])).

fof(f5229,plain,
    ( ! [X6] : k4_xboole_0(sK2,k4_xboole_0(sK2,X6)) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X6)),sK1))))
    | ~ spl3_94
    | ~ spl3_113 ),
    inference(superposition,[],[f2729,f1876])).

fof(f1876,plain,
    ( ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1))
    | ~ spl3_94 ),
    inference(avatar_component_clause,[],[f1875])).

fof(f17818,plain,
    ( ! [X8] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(X8,sK1)))))
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_138
    | ~ spl3_230 ),
    inference(forward_demodulation,[],[f17817,f4448])).

fof(f17817,plain,
    ( ! [X8] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X8)))))
    | ~ spl3_23
    | ~ spl3_67
    | ~ spl3_230 ),
    inference(forward_demodulation,[],[f17679,f206])).

fof(f17679,plain,
    ( ! [X8] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK1),X8)))
    | ~ spl3_67
    | ~ spl3_230 ),
    inference(superposition,[],[f1026,f17608])).

fof(f17608,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0)
    | ~ spl3_230 ),
    inference(avatar_component_clause,[],[f17607])).

fof(f17613,plain,
    ( spl3_231
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_63
    | ~ spl3_91
    | ~ spl3_120
    | ~ spl3_139
    | ~ spl3_142
    | ~ spl3_227
    | ~ spl3_228
    | ~ spl3_229 ),
    inference(avatar_split_clause,[],[f17557,f17162,f17158,f16005,f4831,f4451,f3184,f1771,f815,f807,f205,f67,f17611])).

fof(f815,plain,
    ( spl3_63
  <=> ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(sK2,k4_xboole_0(X2,k4_xboole_0(X2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f17158,plain,
    ( spl3_228
  <=> ! [X4] : k4_xboole_0(k4_xboole_0(sK1,sK1),X4) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_228])])).

fof(f17162,plain,
    ( spl3_229
  <=> ! [X3] : k4_xboole_0(sK2,X3) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_229])])).

fof(f17557,plain,
    ( ! [X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),X11) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_63
    | ~ spl3_91
    | ~ spl3_120
    | ~ spl3_139
    | ~ spl3_142
    | ~ spl3_227
    | ~ spl3_228
    | ~ spl3_229 ),
    inference(forward_demodulation,[],[f17556,f17133])).

fof(f17556,plain,
    ( ! [X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X11),X11)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_63
    | ~ spl3_91
    | ~ spl3_228
    | ~ spl3_229 ),
    inference(forward_demodulation,[],[f17468,f1845])).

fof(f1845,plain,
    ( ! [X2,X3] : k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,X2),X3)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X3,X2)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_63
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f1794,f943])).

fof(f943,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,X8))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(sK1,X8)))))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f942,f206])).

fof(f942,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),X8))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,X8)))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f941,f808])).

fof(f941,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),X8))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,X8)))
    | ~ spl3_23
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f920,f206])).

fof(f920,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),X8))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X7)),X8)
    | ~ spl3_23
    | ~ spl3_63 ),
    inference(superposition,[],[f206,f816])).

fof(f816,plain,
    ( ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(sK2,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f815])).

fof(f1794,plain,
    ( ! [X2,X3] : k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,X2),X3)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK1,X2)))))
    | ~ spl3_8
    | ~ spl3_91 ),
    inference(superposition,[],[f1772,f68])).

fof(f17468,plain,
    ( ! [X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X11),X11)) = k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK1,X11),X11))
    | ~ spl3_228
    | ~ spl3_229 ),
    inference(superposition,[],[f17159,f17163])).

fof(f17163,plain,
    ( ! [X3] : k4_xboole_0(sK2,X3) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))
    | ~ spl3_229 ),
    inference(avatar_component_clause,[],[f17162])).

fof(f17159,plain,
    ( ! [X4] : k4_xboole_0(k4_xboole_0(sK1,sK1),X4) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4)
    | ~ spl3_228 ),
    inference(avatar_component_clause,[],[f17158])).

fof(f17609,plain,
    ( spl3_230
    | ~ spl3_64
    | ~ spl3_228 ),
    inference(avatar_split_clause,[],[f17184,f17158,f945,f17607])).

fof(f17184,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0)
    | ~ spl3_64
    | ~ spl3_228 ),
    inference(superposition,[],[f17159,f946])).

fof(f17164,plain,
    ( spl3_229
    | ~ spl3_38
    | ~ spl3_59
    | ~ spl3_227 ),
    inference(avatar_split_clause,[],[f17117,f16005,f697,f393,f17162])).

fof(f17117,plain,
    ( ! [X3] : k4_xboole_0(sK2,X3) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))
    | ~ spl3_38
    | ~ spl3_59
    | ~ spl3_227 ),
    inference(forward_demodulation,[],[f17116,f698])).

fof(f17116,plain,
    ( ! [X3] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X3))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))
    | ~ spl3_38
    | ~ spl3_227 ),
    inference(forward_demodulation,[],[f17042,f394])).

fof(f17042,plain,
    ( ! [X3] : k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X3))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))
    | ~ spl3_38
    | ~ spl3_227 ),
    inference(superposition,[],[f394,f16006])).

fof(f17160,plain,
    ( spl3_228
    | ~ spl3_61
    | ~ spl3_113
    | ~ spl3_137
    | ~ spl3_218 ),
    inference(avatar_split_clause,[],[f15464,f15237,f4268,f2728,f807,f17158])).

fof(f15237,plain,
    ( spl3_218
  <=> ! [X13] : k4_xboole_0(X13,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X13,k4_xboole_0(sK2,X13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_218])])).

fof(f15464,plain,
    ( ! [X4] : k4_xboole_0(k4_xboole_0(sK1,sK1),X4) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4)
    | ~ spl3_61
    | ~ spl3_113
    | ~ spl3_137
    | ~ spl3_218 ),
    inference(forward_demodulation,[],[f15463,f4269])).

fof(f15463,plain,
    ( ! [X4] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4)
    | ~ spl3_61
    | ~ spl3_113
    | ~ spl3_218 ),
    inference(forward_demodulation,[],[f15290,f808])).

fof(f15290,plain,
    ( ! [X4] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X4)),X4)
    | ~ spl3_113
    | ~ spl3_218 ),
    inference(superposition,[],[f2729,f15238])).

fof(f15238,plain,
    ( ! [X13] : k4_xboole_0(X13,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X13,k4_xboole_0(sK2,X13))
    | ~ spl3_218 ),
    inference(avatar_component_clause,[],[f15237])).

fof(f16007,plain,
    ( spl3_227
    | ~ spl3_38
    | ~ spl3_106
    | ~ spl3_217 ),
    inference(avatar_split_clause,[],[f15147,f15045,f2089,f393,f16005])).

fof(f2089,plain,
    ( spl3_106
  <=> ! [X5,X6] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).

fof(f15147,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2))
    | ~ spl3_38
    | ~ spl3_106
    | ~ spl3_217 ),
    inference(forward_demodulation,[],[f15084,f394])).

fof(f15084,plain,
    ( ! [X2] : k5_xboole_0(sK2,k4_xboole_0(sK2,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2))
    | ~ spl3_106
    | ~ spl3_217 ),
    inference(superposition,[],[f2090,f15046])).

fof(f2090,plain,
    ( ! [X6,X5] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6))
    | ~ spl3_106 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f15991,plain,
    ( spl3_223
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f350,f205,f67,f15989])).

fof(f350,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(superposition,[],[f68,f206])).

fof(f15979,plain,
    ( spl3_220
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_66
    | ~ spl3_103
    | ~ spl3_113
    | ~ spl3_211 ),
    inference(avatar_split_clause,[],[f14497,f14378,f2728,f2077,f953,f945,f693,f15977])).

fof(f14378,plain,
    ( spl3_211
  <=> ! [X14] : k4_xboole_0(sK2,X14) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_211])])).

fof(f14497,plain,
    ( ! [X22] : k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),sK2))
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_66
    | ~ spl3_103
    | ~ spl3_113
    | ~ spl3_211 ),
    inference(backward_demodulation,[],[f4100,f14492])).

fof(f14492,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8))
    | ~ spl3_58
    | ~ spl3_113
    | ~ spl3_211 ),
    inference(forward_demodulation,[],[f14434,f694])).

fof(f14434,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X8))),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8))
    | ~ spl3_113
    | ~ spl3_211 ),
    inference(superposition,[],[f2729,f14379])).

fof(f14379,plain,
    ( ! [X14] : k4_xboole_0(sK2,X14) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))
    | ~ spl3_211 ),
    inference(avatar_component_clause,[],[f14378])).

fof(f4100,plain,
    ( ! [X22] : k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(sK2,X22)))
    | ~ spl3_64
    | ~ spl3_66
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f4008,f954])).

fof(f4008,plain,
    ( ! [X22] : k4_xboole_0(sK2,k4_xboole_0(X22,k4_xboole_0(X22,sK2))) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(sK2,k4_xboole_0(X22,k4_xboole_0(X22,sK2)))))
    | ~ spl3_64
    | ~ spl3_103 ),
    inference(superposition,[],[f2078,f946])).

fof(f15239,plain,
    ( spl3_218
    | ~ spl3_67
    | ~ spl3_140
    | ~ spl3_215
    | ~ spl3_217 ),
    inference(avatar_split_clause,[],[f15164,f15045,f14837,f4455,f1025,f15237])).

fof(f15164,plain,
    ( ! [X13] : k4_xboole_0(X13,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X13,k4_xboole_0(sK2,X13))
    | ~ spl3_67
    | ~ spl3_140
    | ~ spl3_215
    | ~ spl3_217 ),
    inference(forward_demodulation,[],[f15163,f4456])).

fof(f15163,plain,
    ( ! [X13] : k4_xboole_0(X13,k4_xboole_0(sK2,X13)) = k5_xboole_0(X13,k4_xboole_0(k4_xboole_0(sK1,sK1),X13))
    | ~ spl3_67
    | ~ spl3_215
    | ~ spl3_217 ),
    inference(forward_demodulation,[],[f15095,f14838])).

fof(f15095,plain,
    ( ! [X13] : k4_xboole_0(X13,k4_xboole_0(sK2,X13)) = k5_xboole_0(X13,k4_xboole_0(k4_xboole_0(sK2,X13),k4_xboole_0(sK2,X13)))
    | ~ spl3_67
    | ~ spl3_217 ),
    inference(superposition,[],[f1026,f15046])).

fof(f15047,plain,
    ( spl3_217
    | ~ spl3_23
    | ~ spl3_91
    | ~ spl3_113
    | ~ spl3_153
    | ~ spl3_214 ),
    inference(avatar_split_clause,[],[f15018,f14833,f5930,f2728,f1771,f205,f15045])).

fof(f14833,plain,
    ( spl3_214
  <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_214])])).

fof(f15018,plain,
    ( ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),X7)
    | ~ spl3_23
    | ~ spl3_91
    | ~ spl3_113
    | ~ spl3_153
    | ~ spl3_214 ),
    inference(forward_demodulation,[],[f15017,f5931])).

fof(f15017,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK2)) = k4_xboole_0(k4_xboole_0(sK2,X7),X7)
    | ~ spl3_23
    | ~ spl3_91
    | ~ spl3_113
    | ~ spl3_214 ),
    inference(forward_demodulation,[],[f15016,f1772])).

fof(f15016,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X7),X7)))
    | ~ spl3_23
    | ~ spl3_113
    | ~ spl3_214 ),
    inference(forward_demodulation,[],[f14913,f206])).

fof(f14913,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK2)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X7))),X7)
    | ~ spl3_113
    | ~ spl3_214 ),
    inference(superposition,[],[f2729,f14834])).

fof(f14834,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8))
    | ~ spl3_214 ),
    inference(avatar_component_clause,[],[f14833])).

fof(f14839,plain,
    ( spl3_215
    | ~ spl3_36
    | ~ spl3_113
    | ~ spl3_143
    | ~ spl3_212 ),
    inference(avatar_split_clause,[],[f14583,f14382,f4923,f2728,f384,f14837])).

fof(f14835,plain,
    ( spl3_214
    | ~ spl3_58
    | ~ spl3_113
    | ~ spl3_211 ),
    inference(avatar_split_clause,[],[f14492,f14378,f2728,f693,f14833])).

fof(f14384,plain,
    ( spl3_212
    | ~ spl3_8
    | ~ spl3_36
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_207 ),
    inference(avatar_split_clause,[],[f13047,f12888,f807,f681,f384,f67,f14382])).

fof(f13047,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))
    | ~ spl3_8
    | ~ spl3_36
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f13046,f682])).

fof(f13046,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))
    | ~ spl3_8
    | ~ spl3_36
    | ~ spl3_61
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f13045,f808])).

fof(f13045,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))
    | ~ spl3_8
    | ~ spl3_36
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f12919,f68])).

fof(f12919,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(sK2,X0),sK2)) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))
    | ~ spl3_36
    | ~ spl3_207 ),
    inference(superposition,[],[f12889,f385])).

fof(f14380,plain,
    ( spl3_211
    | ~ spl3_8
    | ~ spl3_35
    | ~ spl3_62
    | ~ spl3_207 ),
    inference(avatar_split_clause,[],[f13037,f12888,f811,f371,f67,f14378])).

fof(f13037,plain,
    ( ! [X14] : k4_xboole_0(sK2,X14) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))
    | ~ spl3_8
    | ~ spl3_35
    | ~ spl3_62
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f13036,f372])).

fof(f13036,plain,
    ( ! [X14] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X14))) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f13035,f68])).

fof(f13035,plain,
    ( ! [X14] : k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(sK1,X14),sK2)) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_207 ),
    inference(forward_demodulation,[],[f12914,f812])).

fof(f12914,plain,
    ( ! [X14] : k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(sK1,X14),sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,sK1))),k4_xboole_0(sK1,sK2))
    | ~ spl3_8
    | ~ spl3_207 ),
    inference(superposition,[],[f12889,f68])).

fof(f12890,plain,
    ( spl3_207
    | ~ spl3_13
    | ~ spl3_113 ),
    inference(avatar_split_clause,[],[f5158,f2728,f112,f12888])).

fof(f112,plain,
    ( spl3_13
  <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f5158,plain,
    ( ! [X36] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X36)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X36,k4_xboole_0(X36,sK2))
    | ~ spl3_13
    | ~ spl3_113 ),
    inference(superposition,[],[f2729,f114])).

fof(f114,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f12482,plain,
    ( spl3_205
    | ~ spl3_69
    | ~ spl3_140
    | ~ spl3_190
    | ~ spl3_202 ),
    inference(avatar_split_clause,[],[f12300,f12101,f9796,f4455,f1139,f12480])).

fof(f12300,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(X1,sK2),sK2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1))
    | ~ spl3_69
    | ~ spl3_140
    | ~ spl3_190
    | ~ spl3_202 ),
    inference(forward_demodulation,[],[f12245,f10213])).

fof(f12245,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X1))
    | ~ spl3_140
    | ~ spl3_202 ),
    inference(superposition,[],[f4456,f12102])).

fof(f12103,plain,
    ( spl3_202
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_155
    | ~ spl3_166
    | ~ spl3_190 ),
    inference(avatar_split_clause,[],[f10285,f9796,f7267,f5938,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f12101])).

fof(f5938,plain,
    ( spl3_155
  <=> ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).

fof(f10285,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_155
    | ~ spl3_166
    | ~ spl3_190 ),
    inference(forward_demodulation,[],[f10284,f7268])).

fof(f10284,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_155
    | ~ spl3_190 ),
    inference(forward_demodulation,[],[f10217,f5128])).

fof(f10217,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))
    | ~ spl3_155
    | ~ spl3_190 ),
    inference(superposition,[],[f5939,f9797])).

fof(f5939,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1)
    | ~ spl3_155 ),
    inference(avatar_component_clause,[],[f5938])).

fof(f10331,plain,
    ( spl3_199
    | ~ spl3_35
    | ~ spl3_138
    | ~ spl3_190 ),
    inference(avatar_split_clause,[],[f10275,f9796,f4447,f371,f10329])).

fof(f10275,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(X1,sK1))
    | ~ spl3_35
    | ~ spl3_138
    | ~ spl3_190 ),
    inference(forward_demodulation,[],[f10211,f4448])).

fof(f10211,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))
    | ~ spl3_35
    | ~ spl3_190 ),
    inference(superposition,[],[f372,f9797])).

fof(f9830,plain,
    ( spl3_198
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_186 ),
    inference(avatar_split_clause,[],[f9722,f9137,f811,f67,f9828])).

fof(f9137,plain,
    ( spl3_186
  <=> ! [X3] : k4_xboole_0(k4_xboole_0(sK1,X3),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_186])])).

fof(f9722,plain,
    ( ! [X13] : k4_xboole_0(k4_xboole_0(sK1,X13),sK1) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1)
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_186 ),
    inference(forward_demodulation,[],[f9651,f812])).

fof(f9651,plain,
    ( ! [X13] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X13,k4_xboole_0(X13,sK1))),sK1)
    | ~ spl3_8
    | ~ spl3_186 ),
    inference(superposition,[],[f9138,f68])).

fof(f9138,plain,
    ( ! [X3] : k4_xboole_0(k4_xboole_0(sK1,X3),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X3)),sK1)
    | ~ spl3_186 ),
    inference(avatar_component_clause,[],[f9137])).

fof(f9802,plain,
    ( spl3_191
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(avatar_split_clause,[],[f4795,f4459,f4451,f3544,f2740,f2085,f1663,f1231,f945,f697,f584,f205,f63,f9800])).

fof(f4795,plain,
    ( ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,sK1),X2))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_87
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(backward_demodulation,[],[f1664,f4791])).

fof(f9798,plain,
    ( spl3_190
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_78
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f3805,f3688,f1718,f1427,f949,f807,f681,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f9796])).

fof(f1427,plain,
    ( spl3_78
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f3805,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_78
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(backward_demodulation,[],[f1465,f3804])).

fof(f3804,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(backward_demodulation,[],[f3765,f3803])).

fof(f1465,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_78 ),
    inference(forward_demodulation,[],[f1464,f872])).

fof(f872,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X6,X7)))
    | ~ spl3_23
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f856,f808])).

fof(f856,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X6,X7)))
    | ~ spl3_23
    | ~ spl3_61 ),
    inference(superposition,[],[f206,f808])).

fof(f1464,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X1)),sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_78 ),
    inference(forward_demodulation,[],[f1463,f808])).

fof(f1463,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_78 ),
    inference(forward_demodulation,[],[f1444,f808])).

fof(f1444,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK1) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X1,sK2)))
    | ~ spl3_23
    | ~ spl3_78 ),
    inference(superposition,[],[f1428,f206])).

fof(f1428,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f9794,plain,
    ( spl3_189
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f339,f205,f67,f9792])).

fof(f339,plain,
    ( ! [X2,X3,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3)
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f68])).

fof(f9139,plain,
    ( spl3_186
    | ~ spl3_112
    | ~ spl3_180 ),
    inference(avatar_split_clause,[],[f8837,f8729,f2724,f9137])).

fof(f8729,plain,
    ( spl3_180
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_180])])).

fof(f8837,plain,
    ( ! [X3] : k4_xboole_0(k4_xboole_0(sK1,X3),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X3)),sK1)
    | ~ spl3_112
    | ~ spl3_180 ),
    inference(superposition,[],[f8730,f2725])).

fof(f8730,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1)))
    | ~ spl3_180 ),
    inference(avatar_component_clause,[],[f8729])).

fof(f9127,plain,
    ( spl3_183
    | ~ spl3_7
    | ~ spl3_34
    | ~ spl3_149 ),
    inference(avatar_split_clause,[],[f5871,f5770,f335,f63,f9125])).

fof(f5871,plain,
    ( ! [X9] : k4_xboole_0(sK1,X9) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))
    | ~ spl3_7
    | ~ spl3_34
    | ~ spl3_149 ),
    inference(forward_demodulation,[],[f5814,f64])).

fof(f5814,plain,
    ( ! [X9] : k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X9))) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))
    | ~ spl3_34
    | ~ spl3_149 ),
    inference(superposition,[],[f336,f5771])).

fof(f8731,plain,
    ( spl3_180
    | ~ spl3_112
    | ~ spl3_177 ),
    inference(avatar_split_clause,[],[f8484,f7312,f2724,f8729])).

fof(f8484,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1)))
    | ~ spl3_112
    | ~ spl3_177 ),
    inference(superposition,[],[f2725,f7313])).

fof(f8727,plain,
    ( spl3_179
    | ~ spl3_67
    | ~ spl3_140
    | ~ spl3_158
    | ~ spl3_166 ),
    inference(avatar_split_clause,[],[f7473,f7267,f5950,f4455,f1025,f8725])).

fof(f7473,plain,
    ( ! [X4] : k4_xboole_0(k4_xboole_0(X4,sK1),sK1) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl3_67
    | ~ spl3_140
    | ~ spl3_158
    | ~ spl3_166 ),
    inference(forward_demodulation,[],[f7433,f6744])).

fof(f7433,plain,
    ( ! [X4] : k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X4)) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl3_140
    | ~ spl3_166 ),
    inference(superposition,[],[f4456,f7268])).

fof(f7314,plain,
    ( spl3_177
    | ~ spl3_145
    | ~ spl3_164 ),
    inference(avatar_split_clause,[],[f7204,f7171,f5017,f7312])).

fof(f7171,plain,
    ( spl3_164
  <=> ! [X3] : k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).

fof(f7204,plain,
    ( ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1))
    | ~ spl3_145
    | ~ spl3_164 ),
    inference(forward_demodulation,[],[f7178,f7172])).

fof(f7172,plain,
    ( ! [X3] : k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK1))
    | ~ spl3_164 ),
    inference(avatar_component_clause,[],[f7171])).

fof(f7178,plain,
    ( ! [X2] : k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1))
    | ~ spl3_145
    | ~ spl3_164 ),
    inference(superposition,[],[f7172,f5018])).

fof(f7298,plain,
    ( spl3_173
    | ~ spl3_58
    | ~ spl3_158 ),
    inference(avatar_split_clause,[],[f6718,f5950,f693,f7296])).

fof(f7282,plain,
    ( ~ spl3_169
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | spl3_45
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_148
    | ~ spl3_158
    | ~ spl3_163
    | ~ spl3_164 ),
    inference(avatar_split_clause,[],[f7220,f7171,f6833,f5950,f5636,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1775,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f545,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f7279])).

fof(f545,plain,
    ( spl3_45
  <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f5636,plain,
    ( spl3_148
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK2),X1) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).

fof(f7220,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | spl3_45
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_148
    | ~ spl3_158
    | ~ spl3_163
    | ~ spl3_164 ),
    inference(backward_demodulation,[],[f547,f7219])).

fof(f7219,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X8,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X8,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_92
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_148
    | ~ spl3_158
    | ~ spl3_163
    | ~ spl3_164 ),
    inference(forward_demodulation,[],[f7214,f6773])).

fof(f7214,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X8,sK1)) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X8,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_148
    | ~ spl3_158
    | ~ spl3_163
    | ~ spl3_164 ),
    inference(backward_demodulation,[],[f6872,f7213])).

fof(f7213,plain,
    ( ! [X4] : k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X4,sK1),sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_113
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_164 ),
    inference(forward_demodulation,[],[f7212,f5468])).

fof(f7212,plain,
    ( ! [X4] : k5_xboole_0(sK1,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X4,sK1),sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_58
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_158
    | ~ spl3_164 ),
    inference(forward_demodulation,[],[f7211,f6718])).

fof(f7211,plain,
    ( ! [X4] : k5_xboole_0(sK1,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X4,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_50
    | ~ spl3_55
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_64
    | ~ spl3_65
    | ~ spl3_71
    | ~ spl3_89
    | ~ spl3_96
    | ~ spl3_105
    | ~ spl3_112
    | ~ spl3_116
    | ~ spl3_122
    | ~ spl3_128
    | ~ spl3_134
    | ~ spl3_137
    | ~ spl3_139
    | ~ spl3_141
    | ~ spl3_145
    | ~ spl3_164 ),
    inference(forward_demodulation,[],[f7181,f5128])).

fof(f7181,plain,
    ( ! [X4] : k5_xboole_0(sK1,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X4),sK1))
    | ~ spl3_8
    | ~ spl3_164 ),
    inference(superposition,[],[f7172,f68])).

fof(f6872,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X8,sK1)) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X8,sK1),sK1)))
    | ~ spl3_148
    | ~ spl3_163 ),
    inference(superposition,[],[f5637,f6834])).

fof(f5637,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK2),X1) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))
    | ~ spl3_148 ),
    inference(avatar_component_clause,[],[f5636])).

fof(f547,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f545])).

fof(f7269,plain,
    ( spl3_166
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134
    | ~ spl3_138
    | ~ spl3_142 ),
    inference(avatar_split_clause,[],[f4875,f4831,f4447,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f7267])).

fof(f4875,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134
    | ~ spl3_138
    | ~ spl3_142 ),
    inference(forward_demodulation,[],[f4874,f3803])).

fof(f4874,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1))
    | ~ spl3_138
    | ~ spl3_142 ),
    inference(forward_demodulation,[],[f4836,f4832])).

fof(f4836,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(X2,sK1)),sK1)
    | ~ spl3_138
    | ~ spl3_142 ),
    inference(superposition,[],[f4832,f4448])).

fof(f7265,plain,
    ( spl3_165
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(avatar_split_clause,[],[f4803,f4459,f4451,f3544,f2740,f2085,f1231,f945,f697,f584,f205,f63,f7263])).

fof(f4803,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(backward_demodulation,[],[f4553,f4791])).

fof(f7173,plain,
    ( spl3_164
    | ~ spl3_58
    | ~ spl3_114
    | ~ spl3_158 ),
    inference(avatar_split_clause,[],[f6769,f5950,f2732,f693,f7171])).

fof(f2732,plain,
    ( spl3_114
  <=> ! [X3] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f6769,plain,
    ( ! [X3] : k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK1))
    | ~ spl3_58
    | ~ spl3_114
    | ~ spl3_158 ),
    inference(backward_demodulation,[],[f2733,f6718])).

fof(f2733,plain,
    ( ! [X3] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3))
    | ~ spl3_114 ),
    inference(avatar_component_clause,[],[f2732])).

fof(f6835,plain,
    ( spl3_163
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_89
    | ~ spl3_134
    | ~ spl3_158 ),
    inference(avatar_split_clause,[],[f6824,f5950,f3688,f1718,f1025,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f6833])).

fof(f6824,plain,
    ( ! [X29] : k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k4_xboole_0(k4_xboole_0(X29,sK1),sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_89
    | ~ spl3_134
    | ~ spl3_158 ),
    inference(backward_demodulation,[],[f3893,f6744])).

fof(f3893,plain,
    ( ! [X29] : k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k5_xboole_0(k4_xboole_0(X29,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X29))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f3751,f3787])).

fof(f3787,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(backward_demodulation,[],[f3689,f3772])).

fof(f3751,plain,
    ( ! [X29] : k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k5_xboole_0(k4_xboole_0(X29,sK1),k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(sK1,sK1))))
    | ~ spl3_67
    | ~ spl3_134 ),
    inference(superposition,[],[f1026,f3689])).

fof(f5968,plain,
    ( spl3_162
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f83,f63,f59,f5966])).

fof(f83,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2))))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f64,f60])).

fof(f5960,plain,
    ( spl3_160
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_147 ),
    inference(avatar_split_clause,[],[f5717,f5632,f811,f67,f5958])).

fof(f5717,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9))
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_147 ),
    inference(forward_demodulation,[],[f5648,f812])).

fof(f5648,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X9,k4_xboole_0(X9,sK1))),sK1)
    | ~ spl3_8
    | ~ spl3_147 ),
    inference(superposition,[],[f5633,f68])).

fof(f5952,plain,
    ( spl3_158
    | ~ spl3_23
    | ~ spl3_147 ),
    inference(avatar_split_clause,[],[f5662,f5632,f205,f5950])).

fof(f5662,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,sK1)))
    | ~ spl3_23
    | ~ spl3_147 ),
    inference(superposition,[],[f5633,f206])).

fof(f5948,plain,
    ( spl3_157
    | ~ spl3_8
    | ~ spl3_147 ),
    inference(avatar_split_clause,[],[f5658,f5632,f67,f5946])).

fof(f5658,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X7)
    | ~ spl3_8
    | ~ spl3_147 ),
    inference(superposition,[],[f5633,f68])).

fof(f5940,plain,
    ( spl3_155
    | ~ spl3_8
    | ~ spl3_120
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(avatar_split_clause,[],[f4769,f4459,f4451,f3184,f67,f5938])).

fof(f4769,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1)
    | ~ spl3_8
    | ~ spl3_120
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4728,f4768])).

fof(f4768,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,k4_xboole_0(X8,sK1)))
    | ~ spl3_8
    | ~ spl3_120
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4767,f4452])).

fof(f4767,plain,
    ( ! [X8] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X8,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,k4_xboole_0(X8,sK1)))
    | ~ spl3_8
    | ~ spl3_120
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f4727,f3185])).

fof(f4727,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X8)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,k4_xboole_0(X8,sK1)))
    | ~ spl3_8
    | ~ spl3_141 ),
    inference(superposition,[],[f4460,f68])).

fof(f4728,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,k4_xboole_0(X9,sK1)))
    | ~ spl3_8
    | ~ spl3_141 ),
    inference(superposition,[],[f4460,f68])).

fof(f5932,plain,
    ( spl3_153
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_63
    | ~ spl3_91
    | ~ spl3_103
    | ~ spl3_107 ),
    inference(avatar_split_clause,[],[f4134,f2093,f2077,f1771,f815,f807,f681,f205,f67,f5930])).

fof(f2093,plain,
    ( spl3_107
  <=> ! [X44,X43] : k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X43),X44))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_107])])).

fof(f4134,plain,
    ( ! [X16] : k4_xboole_0(sK2,X16) = k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_63
    | ~ spl3_91
    | ~ spl3_103
    | ~ spl3_107 ),
    inference(forward_demodulation,[],[f4133,f682])).

fof(f4133,plain,
    ( ! [X16] : k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X16)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_63
    | ~ spl3_91
    | ~ spl3_103
    | ~ spl3_107 ),
    inference(forward_demodulation,[],[f4060,f1845])).

fof(f4060,plain,
    ( ! [X16] : k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2)) = k4_xboole_0(k4_xboole_0(sK2,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2))
    | ~ spl3_103
    | ~ spl3_107 ),
    inference(superposition,[],[f2078,f2094])).

fof(f2094,plain,
    ( ! [X43,X44] : k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X43),X44)))
    | ~ spl3_107 ),
    inference(avatar_component_clause,[],[f2093])).

fof(f5772,plain,
    ( spl3_149
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_145
    | ~ spl3_147 ),
    inference(avatar_split_clause,[],[f5716,f5632,f5017,f811,f67,f5770])).

fof(f5716,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),sK1)
    | ~ spl3_8
    | ~ spl3_62
    | ~ spl3_145
    | ~ spl3_147 ),
    inference(forward_demodulation,[],[f5715,f812])).

fof(f5715,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X8,k4_xboole_0(X8,sK1))),sK1)
    | ~ spl3_8
    | ~ spl3_145
    | ~ spl3_147 ),
    inference(forward_demodulation,[],[f5647,f5018])).

fof(f5647,plain,
    ( ! [X8] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X8,k4_xboole_0(X8,sK1))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X8))
    | ~ spl3_8
    | ~ spl3_147 ),
    inference(superposition,[],[f5633,f68])).

fof(f5638,plain,
    ( spl3_148
    | ~ spl3_7
    | ~ spl3_33
    | ~ spl3_53
    | ~ spl3_112
    | ~ spl3_146 ),
    inference(avatar_split_clause,[],[f5622,f5575,f2724,f640,f331,f63,f5636])).

fof(f640,plain,
    ( spl3_53
  <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f5575,plain,
    ( spl3_146
  <=> ! [X3] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).

fof(f5622,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK2),X1) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))
    | ~ spl3_7
    | ~ spl3_33
    | ~ spl3_53
    | ~ spl3_112
    | ~ spl3_146 ),
    inference(forward_demodulation,[],[f5621,f2939])).

fof(f2939,plain,
    ( ! [X61,X60] : k4_xboole_0(k4_xboole_0(sK1,X60),X61) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X60),X61)))
    | ~ spl3_7
    | ~ spl3_112 ),
    inference(superposition,[],[f64,f2725])).

fof(f5621,plain,
    ( ! [X1] : k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)))
    | ~ spl3_33
    | ~ spl3_53
    | ~ spl3_112
    | ~ spl3_146 ),
    inference(forward_demodulation,[],[f5591,f2921])).

fof(f2921,plain,
    ( ! [X6,X5] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X5),X6))
    | ~ spl3_33
    | ~ spl3_112 ),
    inference(superposition,[],[f332,f2725])).

fof(f5591,plain,
    ( ! [X1] : k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)))
    | ~ spl3_53
    | ~ spl3_146 ),
    inference(superposition,[],[f641,f5576])).

fof(f5576,plain,
    ( ! [X3] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK2))
    | ~ spl3_146 ),
    inference(avatar_component_clause,[],[f5575])).

fof(f641,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f640])).

fof(f5634,plain,
    ( spl3_147
    | ~ spl3_113
    | ~ spl3_137 ),
    inference(avatar_split_clause,[],[f5196,f4268,f2728,f5632])).

fof(f5196,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK1)
    | ~ spl3_113
    | ~ spl3_137 ),
    inference(superposition,[],[f2729,f4269])).

fof(f5577,plain,
    ( spl3_146
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(avatar_split_clause,[],[f5392,f2728,f205,f75,f67,f63,f5575])).

fof(f75,plain,
    ( spl3_9
  <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f5392,plain,
    ( ! [X3] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK2))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(forward_demodulation,[],[f5379,f64])).

fof(f5379,plain,
    ( ! [X3] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X3,sK2))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_23
    | ~ spl3_113 ),
    inference(backward_demodulation,[],[f85,f5372])).

fof(f85,plain,
    ( ! [X3] : k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X3))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f76,f64])).

fof(f76,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f5019,plain,
    ( spl3_145
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(avatar_split_clause,[],[f4802,f4459,f4451,f3544,f2740,f2085,f1231,f945,f697,f584,f205,f63,f5017])).

fof(f4925,plain,
    ( spl3_143
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_78
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(avatar_split_clause,[],[f4792,f4459,f4451,f3544,f2740,f2085,f1427,f1231,f945,f697,f584,f205,f63,f4923])).

fof(f4792,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_78
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(backward_demodulation,[],[f1428,f4791])).

fof(f4833,plain,
    ( spl3_142
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_59
    | ~ spl3_64
    | ~ spl3_71
    | ~ spl3_105
    | ~ spl3_116
    | ~ spl3_128
    | ~ spl3_139
    | ~ spl3_141 ),
    inference(avatar_split_clause,[],[f4791,f4459,f4451,f3544,f2740,f2085,f1231,f945,f697,f584,f205,f63,f4831])).

fof(f4461,plain,
    ( spl3_141
    | ~ spl3_91
    | ~ spl3_135 ),
    inference(avatar_split_clause,[],[f3922,f3909,f1771,f4459])).

fof(f3909,plain,
    ( spl3_135
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).

fof(f3922,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))
    | ~ spl3_91
    | ~ spl3_135 ),
    inference(superposition,[],[f3910,f1772])).

fof(f3910,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))
    | ~ spl3_135 ),
    inference(avatar_component_clause,[],[f3909])).

fof(f4457,plain,
    ( spl3_140
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f3826,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4455])).

fof(f3826,plain,
    ( ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(sK1,sK1),X7))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f3709,f3772])).

fof(f3709,plain,
    ( ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK1))))
    | ~ spl3_7
    | ~ spl3_134 ),
    inference(superposition,[],[f64,f3689])).

fof(f4453,plain,
    ( spl3_139
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f3804,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4451])).

fof(f4449,plain,
    ( spl3_138
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f3771,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4447])).

fof(f4270,plain,
    ( spl3_137
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f3787,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4268])).

fof(f3911,plain,
    ( spl3_135
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_65
    | ~ spl3_89
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f3772,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f3909])).

fof(f3690,plain,
    ( spl3_134
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_62
    | ~ spl3_63
    | ~ spl3_89
    | ~ spl3_126 ),
    inference(avatar_split_clause,[],[f3462,f3412,f1718,f815,f811,f205,f67,f3688])).

fof(f3412,plain,
    ( spl3_126
  <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(X2,sK1)) = k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_126])])).

fof(f3462,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_62
    | ~ spl3_63
    | ~ spl3_89
    | ~ spl3_126 ),
    inference(backward_demodulation,[],[f1723,f3459])).

fof(f3459,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))
    | ~ spl3_23
    | ~ spl3_62
    | ~ spl3_63
    | ~ spl3_126 ),
    inference(forward_demodulation,[],[f3458,f3413])).

fof(f3413,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(X2,sK1)) = k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK1,X2)))
    | ~ spl3_126 ),
    inference(avatar_component_clause,[],[f3412])).

fof(f3458,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))
    | ~ spl3_23
    | ~ spl3_62
    | ~ spl3_63
    | ~ spl3_126 ),
    inference(forward_demodulation,[],[f3457,f206])).

fof(f3457,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK1))
    | ~ spl3_62
    | ~ spl3_63
    | ~ spl3_126 ),
    inference(forward_demodulation,[],[f3415,f812])).

fof(f3415,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))))
    | ~ spl3_63
    | ~ spl3_126 ),
    inference(superposition,[],[f3413,f816])).

fof(f1723,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))))
    | ~ spl3_8
    | ~ spl3_89 ),
    inference(superposition,[],[f1719,f68])).

fof(f3546,plain,
    ( spl3_128
    | ~ spl3_6
    | ~ spl3_127 ),
    inference(avatar_split_clause,[],[f3540,f3534,f59,f3544])).

fof(f3534,plain,
    ( spl3_127
  <=> sK2 = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_127])])).

fof(f3540,plain,
    ( ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(k4_xboole_0(sK1,sK1),k5_xboole_0(sK2,X0))
    | ~ spl3_6
    | ~ spl3_127 ),
    inference(superposition,[],[f60,f3536])).

fof(f3536,plain,
    ( sK2 = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_127 ),
    inference(avatar_component_clause,[],[f3534])).

fof(f3537,plain,
    ( spl3_127
    | ~ spl3_48
    | ~ spl3_49
    | ~ spl3_51
    | ~ spl3_61
    | ~ spl3_126 ),
    inference(avatar_split_clause,[],[f3504,f3412,f807,f589,f579,f574,f3534])).

fof(f574,plain,
    ( spl3_48
  <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f589,plain,
    ( spl3_51
  <=> k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f3504,plain,
    ( sK2 = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_48
    | ~ spl3_49
    | ~ spl3_51
    | ~ spl3_61
    | ~ spl3_126 ),
    inference(forward_demodulation,[],[f3503,f581])).

fof(f3503,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_48
    | ~ spl3_51
    | ~ spl3_61
    | ~ spl3_126 ),
    inference(forward_demodulation,[],[f3502,f808])).

fof(f3502,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_48
    | ~ spl3_51
    | ~ spl3_126 ),
    inference(forward_demodulation,[],[f3433,f576])).

fof(f576,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f574])).

fof(f3433,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))
    | ~ spl3_51
    | ~ spl3_126 ),
    inference(superposition,[],[f3413,f591])).

fof(f591,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f589])).

fof(f3414,plain,
    ( spl3_126
    | ~ spl3_61
    | ~ spl3_80
    | ~ spl3_88
    | ~ spl3_106
    | ~ spl3_125 ),
    inference(avatar_split_clause,[],[f3365,f3204,f2089,f1667,f1487,f807,f3412])).

fof(f1487,plain,
    ( spl3_80
  <=> ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f3365,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(X2,sK1)) = k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK1,X2)))
    | ~ spl3_61
    | ~ spl3_80
    | ~ spl3_88
    | ~ spl3_106
    | ~ spl3_125 ),
    inference(forward_demodulation,[],[f3364,f808])).

fof(f3364,plain,
    ( ! [X2] : k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) = k4_xboole_0(sK2,k4_xboole_0(X2,sK1))
    | ~ spl3_80
    | ~ spl3_88
    | ~ spl3_106
    | ~ spl3_125 ),
    inference(forward_demodulation,[],[f3363,f3205])).

fof(f3363,plain,
    ( ! [X2] : k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X2)),sK1))
    | ~ spl3_80
    | ~ spl3_88
    | ~ spl3_106 ),
    inference(forward_demodulation,[],[f3270,f2090])).

fof(f3270,plain,
    ( ! [X2] : k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X2)),sK1))
    | ~ spl3_80
    | ~ spl3_88 ),
    inference(superposition,[],[f1668,f1488])).

fof(f1488,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f3206,plain,
    ( spl3_125
    | ~ spl3_23
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_106 ),
    inference(avatar_split_clause,[],[f2507,f2089,f807,f697,f205,f3204])).

fof(f2507,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(X7,X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8))
    | ~ spl3_23
    | ~ spl3_59
    | ~ spl3_61
    | ~ spl3_106 ),
    inference(forward_demodulation,[],[f2506,f698])).

fof(f2506,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X7,X8))))
    | ~ spl3_23
    | ~ spl3_61
    | ~ spl3_106 ),
    inference(forward_demodulation,[],[f2505,f206])).

fof(f2505,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X7)),X8))
    | ~ spl3_61
    | ~ spl3_106 ),
    inference(forward_demodulation,[],[f2477,f2090])).

fof(f2477,plain,
    ( ! [X8,X7] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X7)),X8))
    | ~ spl3_61
    | ~ spl3_106 ),
    inference(superposition,[],[f2090,f808])).

fof(f3194,plain,
    ( spl3_122
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f1805,f1771,f807,f3192])).

fof(f1805,plain,
    ( ! [X4,X3] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X4))) = k4_xboole_0(k4_xboole_0(sK2,X3),X4)
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(superposition,[],[f1772,f808])).

fof(f3186,plain,
    ( spl3_120
    | ~ spl3_23
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f872,f807,f205,f3184])).

fof(f2742,plain,
    ( spl3_116
    | ~ spl3_55
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f1811,f1771,f681,f2740])).

fof(f1811,plain,
    ( ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK2,X9),X10) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X9),X10)))
    | ~ spl3_55
    | ~ spl3_91 ),
    inference(superposition,[],[f682,f1772])).

fof(f2734,plain,
    ( spl3_114
    | ~ spl3_54
    | ~ spl3_89 ),
    inference(avatar_split_clause,[],[f1735,f1718,f677,f2732])).

fof(f677,plain,
    ( spl3_54
  <=> ! [X5] : k4_xboole_0(sK1,k4_xboole_0(sK2,X5)) = k5_xboole_0(sK1,k4_xboole_0(sK2,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f1735,plain,
    ( ! [X3] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3))
    | ~ spl3_54
    | ~ spl3_89 ),
    inference(superposition,[],[f678,f1719])).

fof(f678,plain,
    ( ! [X5] : k4_xboole_0(sK1,k4_xboole_0(sK2,X5)) = k5_xboole_0(sK1,k4_xboole_0(sK2,X5))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f677])).

fof(f2730,plain,
    ( spl3_113
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f344,f205,f67,f2728])).

fof(f344,plain,
    ( ! [X2,X3,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f68])).

fof(f2726,plain,
    ( spl3_112
    | ~ spl3_23
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f781,f693,f205,f2724])).

fof(f781,plain,
    ( ! [X2,X1] : k4_xboole_0(k4_xboole_0(sK1,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X1),X2)))
    | ~ spl3_23
    | ~ spl3_58 ),
    inference(superposition,[],[f206,f694])).

fof(f2095,plain,
    ( spl3_107
    | ~ spl3_7
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f1873,f1771,f807,f681,f63,f2093])).

fof(f1873,plain,
    ( ! [X43,X44] : k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X43),X44)))
    | ~ spl3_7
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f1823,f1867])).

fof(f1867,plain,
    ( ! [X14,X13] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X13),X14)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X13),X14))
    | ~ spl3_55
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f1813,f682])).

fof(f1813,plain,
    ( ! [X14,X13] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X13),X14)))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X13),X14))
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(superposition,[],[f808,f1772])).

fof(f1823,plain,
    ( ! [X43,X44] : k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X43),X44)))
    | ~ spl3_7
    | ~ spl3_91 ),
    inference(superposition,[],[f64,f1772])).

fof(f2091,plain,
    ( spl3_106
    | ~ spl3_38
    | ~ spl3_55
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f1866,f1771,f681,f393,f2089])).

fof(f1866,plain,
    ( ! [X6,X5] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6))
    | ~ spl3_38
    | ~ spl3_55
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f1809,f682])).

fof(f1809,plain,
    ( ! [X6,X5] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6))
    | ~ spl3_38
    | ~ spl3_91 ),
    inference(superposition,[],[f394,f1772])).

fof(f2087,plain,
    ( spl3_105
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_20
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_89 ),
    inference(avatar_split_clause,[],[f1760,f1718,f681,f478,f393,f388,f384,f174,f100,f93,f88,f63,f2085])).

fof(f174,plain,
    ( spl3_20
  <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(k4_xboole_0(sK2,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1760,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_20
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_55
    | ~ spl3_89 ),
    inference(backward_demodulation,[],[f506,f1759])).

fof(f506,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_20
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f450,f495])).

fof(f450,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,sK1),X1) = k5_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X1)))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_20
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f192,f443])).

fof(f192,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,sK1),X1) = k5_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK2,sK1),X1))))
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(superposition,[],[f175,f64])).

fof(f175,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(k4_xboole_0(sK2,sK1),X0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f2079,plain,
    ( spl3_103
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f107,f67,f63,f2077])).

fof(f107,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f64,f68])).

fof(f2051,plain,
    ( spl3_96
    | ~ spl3_23
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f401,f384,f205,f2049])).

fof(f401,plain,
    ( ! [X2,X1] : k4_xboole_0(k4_xboole_0(sK2,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X1),X2)))
    | ~ spl3_23
    | ~ spl3_36 ),
    inference(superposition,[],[f206,f385])).

fof(f2047,plain,
    ( spl3_95
    | ~ spl3_8
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f398,f384,f67,f2045])).

fof(f398,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(X1,sK2))))
    | ~ spl3_8
    | ~ spl3_36 ),
    inference(superposition,[],[f385,f68])).

fof(f1877,plain,
    ( spl3_94
    | ~ spl3_7
    | ~ spl3_34
    | ~ spl3_35
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f1851,f1771,f371,f335,f63,f1875])).

fof(f1851,plain,
    ( ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1))
    | ~ spl3_7
    | ~ spl3_34
    | ~ spl3_35
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f1850,f372])).

fof(f1850,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X7)))
    | ~ spl3_7
    | ~ spl3_34
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f1797,f64])).

fof(f1797,plain,
    ( ! [X7] : k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X7)))))
    | ~ spl3_34
    | ~ spl3_91 ),
    inference(superposition,[],[f1772,f336])).

fof(f1777,plain,
    ( spl3_92
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f732,f681,f393,f384,f133,f63,f1775])).

fof(f133,plain,
    ( spl3_16
  <=> ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f732,plain,
    ( ! [X1] : k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,X1)))
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_55 ),
    inference(backward_demodulation,[],[f409,f729])).

fof(f729,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2))
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f728,f385])).

fof(f728,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X2))))
    | ~ spl3_38
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f722,f394])).

fof(f722,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X2)))) = k5_xboole_0(sK2,k4_xboole_0(sK2,X2))
    | ~ spl3_38
    | ~ spl3_55 ),
    inference(superposition,[],[f394,f682])).

fof(f409,plain,
    ( ! [X1] : k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f406,f402])).

fof(f402,plain,
    ( ! [X5] : k4_xboole_0(sK1,k4_xboole_0(sK2,X5)) = k5_xboole_0(sK1,k4_xboole_0(sK2,X5))
    | ~ spl3_7
    | ~ spl3_36 ),
    inference(superposition,[],[f64,f385])).

fof(f406,plain,
    ( ! [X1] : k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f140,f402])).

fof(f140,plain,
    ( ! [X1] : k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k4_xboole_0(sK2,X1)))
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(superposition,[],[f134,f64])).

fof(f134,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1773,plain,
    ( spl3_91
    | ~ spl3_23
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f378,f371,f205,f1771])).

fof(f378,plain,
    ( ! [X2,X1] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X1),X2))) = k4_xboole_0(k4_xboole_0(sK2,X1),X2)
    | ~ spl3_23
    | ~ spl3_35 ),
    inference(superposition,[],[f206,f372])).

fof(f1720,plain,
    ( spl3_89
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f505,f478,f393,f388,f384,f205,f93,f88,f63,f54,f1718])).

fof(f54,plain,
    ( spl3_5
  <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f505,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f447,f495])).

fof(f447,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK2,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f338,f440])).

fof(f338,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK2,sK2),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X0)))
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f56])).

fof(f56,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f1669,plain,
    ( spl3_88
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f63,f59,f1667])).

fof(f84,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f60,f64])).

fof(f1665,plain,
    ( spl3_87
    | ~ spl3_55
    | ~ spl3_64
    | ~ spl3_78 ),
    inference(avatar_split_clause,[],[f1469,f1427,f945,f681,f1663])).

fof(f1469,plain,
    ( ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1))
    | ~ spl3_55
    | ~ spl3_64
    | ~ spl3_78 ),
    inference(forward_demodulation,[],[f1447,f682])).

fof(f1447,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X2)))
    | ~ spl3_64
    | ~ spl3_78 ),
    inference(superposition,[],[f946,f1428])).

fof(f1489,plain,
    ( spl3_80
    | ~ spl3_36
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f1340,f1025,f384,f1487])).

fof(f1340,plain,
    ( ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6))
    | ~ spl3_36
    | ~ spl3_67 ),
    inference(superposition,[],[f1026,f385])).

fof(f1429,plain,
    ( spl3_78
    | ~ spl3_36
    | ~ spl3_67
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f1392,f1307,f1025,f384,f1427])).

fof(f1307,plain,
    ( spl3_76
  <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK2) = k5_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1392,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)
    | ~ spl3_36
    | ~ spl3_67
    | ~ spl3_76 ),
    inference(backward_demodulation,[],[f1308,f1340])).

fof(f1308,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK2) = k5_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(sK2,X1))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f1307])).

fof(f1309,plain,
    ( spl3_76
    | ~ spl3_55
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f1156,f1139,f681,f1307])).

fof(f1156,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK2) = k5_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(sK2,X1))
    | ~ spl3_55
    | ~ spl3_69 ),
    inference(superposition,[],[f1140,f682])).

fof(f1234,plain,
    ( spl3_71
    | ~ spl3_50
    | ~ spl3_54
    | ~ spl3_59
    | ~ spl3_60
    | ~ spl3_68
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f1196,f1139,f1135,f803,f697,f677,f584,f1231])).

fof(f803,plain,
    ( spl3_60
  <=> ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f1135,plain,
    ( spl3_68
  <=> ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK1,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f1196,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_50
    | ~ spl3_54
    | ~ spl3_59
    | ~ spl3_60
    | ~ spl3_68
    | ~ spl3_69 ),
    inference(forward_demodulation,[],[f1195,f586])).

fof(f1195,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_54
    | ~ spl3_59
    | ~ spl3_60
    | ~ spl3_68
    | ~ spl3_69 ),
    inference(forward_demodulation,[],[f1194,f804])).

fof(f804,plain,
    ( ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X3)))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f803])).

fof(f1194,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_54
    | ~ spl3_59
    | ~ spl3_68
    | ~ spl3_69 ),
    inference(forward_demodulation,[],[f1193,f698])).

fof(f1193,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))))
    | ~ spl3_54
    | ~ spl3_68
    | ~ spl3_69 ),
    inference(forward_demodulation,[],[f1163,f678])).

fof(f1163,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))))
    | ~ spl3_68
    | ~ spl3_69 ),
    inference(superposition,[],[f1140,f1136])).

fof(f1136,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK1,sK1),X0)
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1141,plain,
    ( spl3_69
    | ~ spl3_7
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f975,f945,f63,f1139])).

fof(f975,plain,
    ( ! [X4] : k4_xboole_0(X4,sK2) = k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4)))
    | ~ spl3_7
    | ~ spl3_64 ),
    inference(superposition,[],[f64,f946])).

fof(f1137,plain,
    ( spl3_68
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f504,f478,f393,f388,f384,f327,f93,f88,f63,f1135])).

fof(f327,plain,
    ( spl3_32
  <=> ! [X0] : k5_xboole_0(k4_xboole_0(sK2,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f504,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK1,sK1),X0)
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f446,f495])).

fof(f446,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK2,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f328,f440])).

fof(f328,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK2,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f327])).

fof(f1027,plain,
    ( spl3_67
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f106,f67,f63,f1025])).

fof(f106,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f64,f68])).

fof(f955,plain,
    ( spl3_66
    | ~ spl3_8
    | ~ spl3_55
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f867,f807,f681,f67,f953])).

fof(f867,plain,
    ( ! [X4] : k4_xboole_0(sK2,X4) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2)))
    | ~ spl3_8
    | ~ spl3_55
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f844,f682])).

fof(f844,plain,
    ( ! [X4] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X4))) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2)))
    | ~ spl3_8
    | ~ spl3_61 ),
    inference(superposition,[],[f808,f68])).

fof(f951,plain,
    ( spl3_65
    | ~ spl3_7
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f859,f807,f63,f949])).

fof(f859,plain,
    ( ! [X10] : k4_xboole_0(sK2,X10) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X10)))
    | ~ spl3_7
    | ~ spl3_61 ),
    inference(superposition,[],[f64,f808])).

fof(f947,plain,
    ( spl3_64
    | ~ spl3_8
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f848,f807,f67,f945])).

fof(f848,plain,
    ( ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sK2))
    | ~ spl3_8
    | ~ spl3_61 ),
    inference(superposition,[],[f808,f68])).

fof(f817,plain,
    ( spl3_63
    | ~ spl3_8
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f788,f697,f67,f815])).

fof(f788,plain,
    ( ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(sK2,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))
    | ~ spl3_8
    | ~ spl3_59 ),
    inference(superposition,[],[f698,f68])).

fof(f813,plain,
    ( spl3_62
    | ~ spl3_8
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f778,f693,f67,f811])).

fof(f778,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))
    | ~ spl3_8
    | ~ spl3_58 ),
    inference(superposition,[],[f694,f68])).

fof(f809,plain,
    ( spl3_61
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f729,f681,f393,f384,f807])).

fof(f805,plain,
    ( spl3_60
    | ~ spl3_7
    | ~ spl3_29
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f405,f384,f271,f63,f803])).

fof(f271,plain,
    ( spl3_29
  <=> ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f405,plain,
    ( ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X3)))
    | ~ spl3_7
    | ~ spl3_29
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f272,f402])).

fof(f272,plain,
    ( ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X3)))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f271])).

fof(f699,plain,
    ( spl3_59
    | ~ spl3_7
    | ~ spl3_33
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f660,f640,f393,f384,f331,f63,f697])).

fof(f660,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
    | ~ spl3_7
    | ~ spl3_33
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f659,f385])).

fof(f659,plain,
    ( ! [X0] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
    | ~ spl3_7
    | ~ spl3_33
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f658,f332])).

fof(f658,plain,
    ( ! [X0] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))
    | ~ spl3_7
    | ~ spl3_36
    | ~ spl3_38
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f657,f402])).

fof(f657,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
    | ~ spl3_38
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f644,f394])).

fof(f644,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))
    | ~ spl3_38
    | ~ spl3_53 ),
    inference(superposition,[],[f641,f394])).

fof(f695,plain,
    ( spl3_58
    | ~ spl3_23
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f567,f555,f205,f693])).

fof(f567,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
    | ~ spl3_23
    | ~ spl3_47 ),
    inference(superposition,[],[f206,f557])).

fof(f683,plain,
    ( spl3_55
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f434,f393,f67,f63,f681])).

fof(f434,plain,
    ( ! [X1] : k4_xboole_0(sK2,X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f421,f106])).

fof(f421,plain,
    ( ! [X1] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))
    | ~ spl3_8
    | ~ spl3_38 ),
    inference(superposition,[],[f394,f68])).

fof(f679,plain,
    ( spl3_54
    | ~ spl3_7
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f402,f384,f63,f677])).

fof(f642,plain,
    ( spl3_53
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_32
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f451,f393,f388,f327,f174,f93,f88,f63,f640])).

fof(f451,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_32
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f175,f446])).

fof(f592,plain,
    ( spl3_51
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f500,f478,f393,f388,f384,f93,f88,f63,f589])).

fof(f500,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f440,f495])).

fof(f587,plain,
    ( spl3_50
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f495,f478,f384,f584])).

fof(f582,plain,
    ( spl3_49
    | ~ spl3_38
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f461,f457,f393,f579])).

fof(f457,plain,
    ( spl3_39
  <=> sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f461,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl3_38
    | ~ spl3_39 ),
    inference(superposition,[],[f459,f394])).

fof(f459,plain,
    ( sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f457])).

fof(f577,plain,
    ( spl3_48
    | ~ spl3_10
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f423,f393,f88,f574])).

fof(f558,plain,
    ( spl3_47
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f509,f478,f384,f555])).

fof(f509,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f480,f495])).

fof(f548,plain,(
    ~ spl3_45 ),
    inference(avatar_split_clause,[],[f32,f545])).

fof(f32,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f27,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f27,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f19,f20])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f481,plain,
    ( spl3_41
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_36
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f469,f457,f384,f133,f119,f63,f48,f478])).

fof(f48,plain,
    ( spl3_4
  <=> sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f119,plain,
    ( spl3_14
  <=> k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f469,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_36
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f468,f50])).

fof(f50,plain,
    ( sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f468,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_7
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_36
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f467,f121])).

fof(f121,plain,
    ( k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f467,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_36
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f464,f402])).

fof(f464,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_16
    | ~ spl3_39 ),
    inference(superposition,[],[f134,f459])).

fof(f460,plain,
    ( spl3_39
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f441,f393,f388,f93,f88,f63,f457])).

fof(f441,plain,
    ( sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f90,f440])).

fof(f395,plain,
    ( spl3_38
    | ~ spl3_7
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f379,f371,f63,f393])).

fof(f379,plain,
    ( ! [X5] : k4_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X5))
    | ~ spl3_7
    | ~ spl3_35 ),
    inference(superposition,[],[f64,f372])).

fof(f391,plain,
    ( spl3_37
    | ~ spl3_13
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f374,f371,f112,f388])).

fof(f374,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_13
    | ~ spl3_35 ),
    inference(superposition,[],[f372,f114])).

fof(f386,plain,
    ( spl3_36
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f346,f205,f112,f384])).

fof(f346,plain,
    ( ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X7)))
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f114])).

fof(f373,plain,
    ( spl3_35
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f343,f205,f54,f371])).

fof(f343,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f56])).

fof(f337,plain,
    ( spl3_34
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f321,f310,f67,f63,f335])).

fof(f310,plain,
    ( spl3_31
  <=> ! [X3] : k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f321,plain,
    ( ! [X0] : k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f314,f106])).

fof(f314,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1))))
    | ~ spl3_8
    | ~ spl3_31 ),
    inference(superposition,[],[f311,f68])).

fof(f311,plain,
    ( ! [X3] : k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X3)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f310])).

fof(f333,plain,
    ( spl3_33
    | ~ spl3_7
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f317,f310,f63,f331])).

fof(f317,plain,
    ( ! [X0] : k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0))
    | ~ spl3_7
    | ~ spl3_31 ),
    inference(superposition,[],[f311,f64])).

fof(f329,plain,
    ( spl3_32
    | ~ spl3_6
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f306,f300,f59,f327])).

fof(f300,plain,
    ( spl3_30
  <=> k4_xboole_0(sK2,sK2) = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f306,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK2,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))
    | ~ spl3_6
    | ~ spl3_30 ),
    inference(superposition,[],[f60,f302])).

fof(f302,plain,
    ( k4_xboole_0(sK2,sK2) = k5_xboole_0(sK1,sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f300])).

fof(f312,plain,
    ( spl3_31
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f282,f267,f63,f310])).

fof(f267,plain,
    ( spl3_28
  <=> ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f282,plain,
    ( ! [X3] : k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X3)))
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(superposition,[],[f268,f64])).

fof(f268,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f267])).

fof(f303,plain,
    ( spl3_30
    | ~ spl3_18
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f292,f271,f156,f300])).

fof(f156,plain,
    ( spl3_18
  <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f292,plain,
    ( k4_xboole_0(sK2,sK2) = k5_xboole_0(sK1,sK1)
    | ~ spl3_18
    | ~ spl3_29 ),
    inference(superposition,[],[f272,f158])).

fof(f158,plain,
    ( sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f273,plain,
    ( spl3_29
    | ~ spl3_7
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f249,f224,f63,f271])).

fof(f224,plain,
    ( spl3_25
  <=> ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f249,plain,
    ( ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X3)))
    | ~ spl3_7
    | ~ spl3_25 ),
    inference(superposition,[],[f225,f64])).

fof(f225,plain,
    ( ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f224])).

fof(f269,plain,
    ( spl3_28
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f172,f167,f59,f267])).

fof(f167,plain,
    ( spl3_19
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f172,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f171,f60])).

fof(f171,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK1),X0))
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(superposition,[],[f60,f169])).

fof(f169,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f226,plain,
    ( spl3_25
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f131,f124,f119,f59,f224])).

fof(f124,plain,
    ( spl3_15
  <=> sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f131,plain,
    ( ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f130,f128])).

fof(f128,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK1,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK2,X0))
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f60,f121])).

fof(f130,plain,
    ( ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,sK2),X0))
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(superposition,[],[f60,f126])).

fof(f126,plain,
    ( sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f207,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f31,f205])).

fof(f176,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f98,f93,f59,f174])).

fof(f98,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(k4_xboole_0(sK2,sK1),X0)
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f60,f95])).

fof(f170,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f163,f151,f133,f119,f48,f167])).

fof(f151,plain,
    ( spl3_17
  <=> sK2 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f163,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f162,f50])).

fof(f162,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f160,f121])).

fof(f160,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(superposition,[],[f134,f153])).

fof(f153,plain,
    ( sK2 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f159,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f144,f133,f119,f88,f48,f156])).

fof(f144,plain,
    ( sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f143,f50])).

fof(f143,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2))
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f137,f121])).

fof(f137,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(superposition,[],[f134,f90])).

fof(f154,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f142,f133,f124,f48,f151])).

fof(f142,plain,
    ( sK2 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f136,f126])).

fof(f136,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(superposition,[],[f134,f50])).

fof(f135,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f129,f119,f75,f59,f133])).

fof(f129,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f76,f128])).

fof(f127,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f117,f112,f63,f124])).

fof(f117,plain,
    ( sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(superposition,[],[f64,f114])).

fof(f122,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f116,f112,f63,f119])).

fof(f116,plain,
    ( k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2)
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(superposition,[],[f64,f114])).

fof(f115,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f103,f67,f54,f112])).

fof(f103,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(superposition,[],[f68,f56])).

fof(f102,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f97,f88,f59,f100])).

fof(f97,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k5_xboole_0(sK2,X0)
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f60,f90])).

fof(f96,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f82,f63,f54,f93])).

fof(f82,plain,
    ( k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f64,f56])).

fof(f91,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f81,f63,f54,f88])).

fof(f81,plain,
    ( sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f64,f56])).

fof(f77,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f70,f59,f48,f75])).

fof(f70,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f60,f50])).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f20,f20])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f57,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f52,f43,f34,f54])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f51,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f39,f34,f48])).

fof(f39,plain,
    ( spl3_2
  <=> ! [X1,X0] :
        ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f43])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f39])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (17227)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (17222)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17216)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (17229)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (17219)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (17221)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (17231)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (17228)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (17225)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (17220)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (17226)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (17224)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (17230)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (17233)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (17232)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (17218)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (17217)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (17223)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 5.16/1.01  % (17220)Time limit reached!
% 5.16/1.01  % (17220)------------------------------
% 5.16/1.01  % (17220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.16/1.01  % (17220)Termination reason: Time limit
% 5.16/1.01  
% 5.16/1.01  % (17220)Memory used [KB]: 12792
% 5.16/1.01  % (17220)Time elapsed: 0.609 s
% 5.16/1.01  % (17220)------------------------------
% 5.16/1.01  % (17220)------------------------------
% 12.40/1.96  % (17222)Time limit reached!
% 12.40/1.96  % (17222)------------------------------
% 12.40/1.96  % (17222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.40/1.96  % (17222)Termination reason: Time limit
% 12.40/1.96  % (17222)Termination phase: Saturation
% 12.40/1.96  
% 12.40/1.96  % (17222)Memory used [KB]: 41321
% 12.40/1.96  % (17222)Time elapsed: 1.500 s
% 12.40/1.96  % (17222)------------------------------
% 12.40/1.96  % (17222)------------------------------
% 12.40/1.98  % (17221)Time limit reached!
% 12.40/1.98  % (17221)------------------------------
% 12.40/1.98  % (17221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.40/1.98  % (17221)Termination reason: Time limit
% 12.40/1.98  % (17221)Termination phase: Saturation
% 12.40/1.98  
% 12.40/1.98  % (17221)Memory used [KB]: 25969
% 12.40/1.98  % (17221)Time elapsed: 1.500 s
% 12.40/1.98  % (17221)------------------------------
% 12.40/1.98  % (17221)------------------------------
% 14.88/2.23  % (17218)Time limit reached!
% 14.88/2.23  % (17218)------------------------------
% 14.88/2.23  % (17218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.88/2.23  % (17218)Termination reason: Time limit
% 14.88/2.23  % (17218)Termination phase: Saturation
% 14.88/2.23  
% 14.88/2.23  % (17218)Memory used [KB]: 29423
% 14.88/2.23  % (17218)Time elapsed: 1.800 s
% 14.88/2.23  % (17218)------------------------------
% 14.88/2.23  % (17218)------------------------------
% 17.96/2.61  % (17228)Time limit reached!
% 17.96/2.61  % (17228)------------------------------
% 17.96/2.61  % (17228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.96/2.61  % (17228)Termination reason: Time limit
% 17.96/2.61  
% 17.96/2.61  % (17228)Memory used [KB]: 35436
% 17.96/2.61  % (17228)Time elapsed: 2.211 s
% 17.96/2.61  % (17228)------------------------------
% 17.96/2.61  % (17228)------------------------------
% 38.63/5.21  % (17223)Refutation found. Thanks to Tanya!
% 38.63/5.21  % SZS status Theorem for theBenchmark
% 38.78/5.23  % SZS output start Proof for theBenchmark
% 38.78/5.23  fof(f84861,plain,(
% 38.78/5.23    $false),
% 38.78/5.23    inference(avatar_sat_refutation,[],[f37,f41,f45,f51,f57,f61,f65,f69,f77,f91,f96,f102,f115,f122,f127,f135,f154,f159,f170,f176,f207,f226,f269,f273,f303,f312,f329,f333,f337,f373,f386,f391,f395,f460,f481,f548,f558,f577,f582,f587,f592,f642,f679,f683,f695,f699,f805,f809,f813,f817,f947,f951,f955,f1027,f1137,f1141,f1234,f1309,f1429,f1489,f1665,f1669,f1720,f1773,f1777,f1877,f2047,f2051,f2079,f2087,f2091,f2095,f2726,f2730,f2734,f2742,f3186,f3194,f3206,f3414,f3537,f3546,f3690,f3911,f4270,f4449,f4453,f4457,f4461,f4833,f4925,f5019,f5577,f5634,f5638,f5772,f5932,f5940,f5948,f5952,f5960,f5968,f6835,f7173,f7265,f7269,f7282,f7298,f7314,f8727,f8731,f9127,f9139,f9794,f9798,f9802,f9830,f10331,f12103,f12482,f12890,f14380,f14384,f14835,f14839,f15047,f15239,f15979,f15991,f16007,f17160,f17164,f17609,f17613,f17965,f18341,f18345,f18463,f18991,f19205,f19217,f19374,f19507,f19674,f19678,f20229,f20434,f20836,f22193,f22205,f22209,f23463,f27686,f28191,f28195,f28954,f29426,f34668,f34680,f35248,f35498,f36548,f36572,f36588,f40538,f41937,f42805,f46547,f48076,f57540,f57548,f57845,f59430,f59747,f60050,f60295,f60605,f60850,f60854,f82565,f84251,f84588])).
% 38.78/5.23  fof(f84588,plain,(
% 38.78/5.23    ~spl3_23 | ~spl3_69 | ~spl3_220 | spl3_246 | ~spl3_350 | ~spl3_370 | ~spl3_407),
% 38.78/5.23    inference(avatar_contradiction_clause,[],[f84587])).
% 38.78/5.23  fof(f84587,plain,(
% 38.78/5.23    $false | (~spl3_23 | ~spl3_69 | ~spl3_220 | spl3_246 | ~spl3_350 | ~spl3_370 | ~spl3_407)),
% 38.78/5.23    inference(subsumption_resolution,[],[f84586,f65193])).
% 38.78/5.23  fof(f65193,plain,(
% 38.78/5.23    ( ! [X4] : (k4_xboole_0(X4,sK2) = k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X4,sK2))))) ) | (~spl3_23 | ~spl3_69 | ~spl3_220 | ~spl3_350)),
% 38.78/5.23    inference(forward_demodulation,[],[f65192,f1140])).
% 38.78/5.23  fof(f1140,plain,(
% 38.78/5.23    ( ! [X4] : (k4_xboole_0(X4,sK2) = k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4)))) ) | ~spl3_69),
% 38.78/5.23    inference(avatar_component_clause,[],[f1139])).
% 38.78/5.23  fof(f1139,plain,(
% 38.78/5.23    spl3_69 <=> ! [X4] : k4_xboole_0(X4,sK2) = k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 38.78/5.23  fof(f65192,plain,(
% 38.78/5.23    ( ! [X4] : (k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4))) = k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X4,sK2))))) ) | (~spl3_23 | ~spl3_220 | ~spl3_350)),
% 38.78/5.23    inference(forward_demodulation,[],[f64511,f206])).
% 38.78/5.23  fof(f206,plain,(
% 38.78/5.23    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl3_23),
% 38.78/5.23    inference(avatar_component_clause,[],[f205])).
% 38.78/5.23  fof(f205,plain,(
% 38.78/5.23    spl3_23 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 38.78/5.23  fof(f64511,plain,(
% 38.78/5.23    ( ! [X4] : (k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4))) = k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X4)),sK2))) ) | (~spl3_220 | ~spl3_350)),
% 38.78/5.23    inference(superposition,[],[f57547,f15978])).
% 38.78/5.23  fof(f15978,plain,(
% 38.78/5.23    ( ! [X22] : (k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),sK2))) ) | ~spl3_220),
% 38.78/5.23    inference(avatar_component_clause,[],[f15977])).
% 38.78/5.23  fof(f15977,plain,(
% 38.78/5.23    spl3_220 <=> ! [X22] : k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_220])])).
% 38.78/5.23  fof(f57547,plain,(
% 38.78/5.23    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)) ) | ~spl3_350),
% 38.78/5.23    inference(avatar_component_clause,[],[f57546])).
% 38.78/5.23  fof(f57546,plain,(
% 38.78/5.23    spl3_350 <=> ! [X1,X3,X2] : k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_350])])).
% 38.78/5.23  fof(f84586,plain,(
% 38.78/5.23    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) | (spl3_246 | ~spl3_370 | ~spl3_407)),
% 38.78/5.23    inference(backward_demodulation,[],[f19673,f84344])).
% 38.78/5.23  fof(f84344,plain,(
% 38.78/5.23    ( ! [X41,X40] : (k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X40,sK2))) = k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(X41,k4_xboole_0(sK2,k4_xboole_0(X40,X40)))))) ) | (~spl3_370 | ~spl3_407)),
% 38.78/5.23    inference(superposition,[],[f57844,f84250])).
% 38.78/5.23  fof(f84250,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(X0,X0)))) ) | ~spl3_407),
% 38.78/5.23    inference(avatar_component_clause,[],[f84249])).
% 38.78/5.23  fof(f84249,plain,(
% 38.78/5.23    spl3_407 <=> ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(X0,X0)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_407])])).
% 38.78/5.23  fof(f57844,plain,(
% 38.78/5.23    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5)))) ) | ~spl3_370),
% 38.78/5.23    inference(avatar_component_clause,[],[f57843])).
% 38.78/5.23  fof(f57843,plain,(
% 38.78/5.23    spl3_370 <=> ! [X3,X5,X4] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_370])])).
% 38.78/5.23  fof(f19673,plain,(
% 38.78/5.23    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK0)))))) | spl3_246),
% 38.78/5.23    inference(avatar_component_clause,[],[f19671])).
% 38.78/5.23  fof(f19671,plain,(
% 38.78/5.23    spl3_246 <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK0))))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_246])])).
% 38.78/5.23  fof(f84251,plain,(
% 38.78/5.23    spl3_407 | ~spl3_265 | ~spl3_404),
% 38.78/5.23    inference(avatar_split_clause,[],[f82614,f82563,f27684,f84249])).
% 38.78/5.23  fof(f27684,plain,(
% 38.78/5.23    spl3_265 <=> ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_265])])).
% 38.78/5.23  fof(f82563,plain,(
% 38.78/5.23    spl3_404 <=> ! [X9] : k4_xboole_0(X9,sK2) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_404])])).
% 38.78/5.23  fof(f82614,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(X0,X0)))) ) | (~spl3_265 | ~spl3_404)),
% 38.78/5.23    inference(superposition,[],[f82564,f27685])).
% 38.78/5.23  fof(f27685,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(X1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))) ) | ~spl3_265),
% 38.78/5.23    inference(avatar_component_clause,[],[f27684])).
% 38.78/5.23  fof(f82564,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,sK2) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))) ) | ~spl3_404),
% 38.78/5.23    inference(avatar_component_clause,[],[f82563])).
% 38.78/5.23  fof(f82565,plain,(
% 38.78/5.23    spl3_404 | ~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_67 | ~spl3_69 | ~spl3_88 | ~spl3_113 | ~spl3_120 | ~spl3_199 | ~spl3_234 | ~spl3_235 | ~spl3_337 | ~spl3_373 | ~spl3_380 | ~spl3_381),
% 38.78/5.23    inference(avatar_split_clause,[],[f80324,f60852,f60848,f59428,f48074,f18461,f18343,f10329,f3184,f2728,f1667,f1139,f1025,f205,f67,f63,f82563])).
% 38.78/5.23  fof(f63,plain,(
% 38.78/5.23    spl3_7 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 38.78/5.23  fof(f67,plain,(
% 38.78/5.23    spl3_8 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 38.78/5.23  fof(f1025,plain,(
% 38.78/5.23    spl3_67 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 38.78/5.23  fof(f1667,plain,(
% 38.78/5.23    spl3_88 <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 38.78/5.23  fof(f2728,plain,(
% 38.78/5.23    spl3_113 <=> ! [X1,X3,X2] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).
% 38.78/5.23  fof(f3184,plain,(
% 38.78/5.23    spl3_120 <=> ! [X7,X6] : k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X6,X7)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).
% 38.78/5.23  fof(f10329,plain,(
% 38.78/5.23    spl3_199 <=> ! [X1] : k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(X1,sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_199])])).
% 38.78/5.23  fof(f18343,plain,(
% 38.78/5.23    spl3_234 <=> ! [X9] : k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_234])])).
% 38.78/5.23  fof(f18461,plain,(
% 38.78/5.23    spl3_235 <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k5_xboole_0(X1,k4_xboole_0(X1,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_235])])).
% 38.78/5.23  fof(f48074,plain,(
% 38.78/5.23    spl3_337 <=> ! [X1,X0] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X1,X0)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_337])])).
% 38.78/5.23  fof(f59428,plain,(
% 38.78/5.23    spl3_373 <=> ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),sK2)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_373])])).
% 38.78/5.23  fof(f60848,plain,(
% 38.78/5.23    spl3_380 <=> ! [X1,X3,X2] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_380])])).
% 38.78/5.23  fof(f60852,plain,(
% 38.78/5.23    spl3_381 <=> ! [X15] : k4_xboole_0(X15,sK2) = k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_381])])).
% 38.78/5.23  fof(f80324,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,sK2) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_67 | ~spl3_69 | ~spl3_88 | ~spl3_113 | ~spl3_120 | ~spl3_199 | ~spl3_234 | ~spl3_235 | ~spl3_337 | ~spl3_373 | ~spl3_380 | ~spl3_381)),
% 38.78/5.23    inference(forward_demodulation,[],[f80323,f59429])).
% 38.78/5.23  fof(f59429,plain,(
% 38.78/5.23    ( ! [X4] : (k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),sK2)) ) | ~spl3_373),
% 38.78/5.23    inference(avatar_component_clause,[],[f59428])).
% 38.78/5.23  fof(f80323,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1))) = k4_xboole_0(k4_xboole_0(X9,sK2),sK2)) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_67 | ~spl3_69 | ~spl3_88 | ~spl3_113 | ~spl3_120 | ~spl3_199 | ~spl3_234 | ~spl3_235 | ~spl3_337 | ~spl3_380 | ~spl3_381)),
% 38.78/5.23    inference(backward_demodulation,[],[f53898,f80320])).
% 38.78/5.23  fof(f80320,plain,(
% 38.78/5.23    ( ! [X235,X234] : (k4_xboole_0(k4_xboole_0(X234,sK2),k4_xboole_0(X235,k4_xboole_0(sK1,X234))) = k4_xboole_0(k4_xboole_0(X234,sK2),X235)) ) | (~spl3_67 | ~spl3_380 | ~spl3_381)),
% 38.78/5.23    inference(forward_demodulation,[],[f79642,f1026])).
% 38.78/5.23  fof(f1026,plain,(
% 38.78/5.23    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl3_67),
% 38.78/5.23    inference(avatar_component_clause,[],[f1025])).
% 38.78/5.23  fof(f79642,plain,(
% 38.78/5.23    ( ! [X235,X234] : (k4_xboole_0(k4_xboole_0(X234,sK2),k4_xboole_0(X235,k4_xboole_0(sK1,X234))) = k5_xboole_0(k4_xboole_0(X234,sK2),k4_xboole_0(X235,k4_xboole_0(X235,k4_xboole_0(X234,sK2))))) ) | (~spl3_380 | ~spl3_381)),
% 38.78/5.23    inference(superposition,[],[f60849,f60853])).
% 38.78/5.23  fof(f60853,plain,(
% 38.78/5.23    ( ! [X15] : (k4_xboole_0(X15,sK2) = k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15))) ) | ~spl3_381),
% 38.78/5.23    inference(avatar_component_clause,[],[f60852])).
% 38.78/5.23  fof(f60849,plain,(
% 38.78/5.23    ( ! [X2,X3,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))) ) | ~spl3_380),
% 38.78/5.23    inference(avatar_component_clause,[],[f60848])).
% 38.78/5.23  fof(f53898,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK1))) = k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_69 | ~spl3_88 | ~spl3_113 | ~spl3_120 | ~spl3_199 | ~spl3_234 | ~spl3_235 | ~spl3_337)),
% 38.78/5.23    inference(forward_demodulation,[],[f53897,f10330])).
% 38.78/5.23  fof(f10330,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(X1,sK1))) ) | ~spl3_199),
% 38.78/5.23    inference(avatar_component_clause,[],[f10329])).
% 38.78/5.23  fof(f53897,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9))) = k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,sK2)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_69 | ~spl3_88 | ~spl3_113 | ~spl3_120 | ~spl3_234 | ~spl3_235 | ~spl3_337)),
% 38.78/5.23    inference(forward_demodulation,[],[f53896,f18569])).
% 38.78/5.23  fof(f18569,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k4_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(X7,X8)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_88 | ~spl3_113 | ~spl3_234 | ~spl3_235)),
% 38.78/5.23    inference(backward_demodulation,[],[f18447,f18568])).
% 38.78/5.23  fof(f18568,plain,(
% 38.78/5.23    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,sK2))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_88 | ~spl3_113 | ~spl3_235)),
% 38.78/5.23    inference(forward_demodulation,[],[f18567,f206])).
% 38.78/5.23  fof(f18567,plain,(
% 38.78/5.23    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_88 | ~spl3_113 | ~spl3_235)),
% 38.78/5.23    inference(forward_demodulation,[],[f18566,f5468])).
% 38.78/5.23  fof(f5468,plain,(
% 38.78/5.23    ( ! [X2,X3,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))) ) | (~spl3_7 | ~spl3_23 | ~spl3_113)),
% 38.78/5.23    inference(forward_demodulation,[],[f5241,f206])).
% 38.78/5.23  fof(f5241,plain,(
% 38.78/5.23    ( ! [X2,X3,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3))) ) | (~spl3_7 | ~spl3_113)),
% 38.78/5.23    inference(superposition,[],[f64,f2729])).
% 38.78/5.23  fof(f2729,plain,(
% 38.78/5.23    ( ! [X2,X3,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) ) | ~spl3_113),
% 38.78/5.23    inference(avatar_component_clause,[],[f2728])).
% 38.78/5.23  fof(f64,plain,(
% 38.78/5.23    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_7),
% 38.78/5.23    inference(avatar_component_clause,[],[f63])).
% 38.78/5.23  fof(f18566,plain,(
% 38.78/5.23    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2)) = k5_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X8,k4_xboole_0(X8,X9)))))) ) | (~spl3_8 | ~spl3_88 | ~spl3_235)),
% 38.78/5.23    inference(forward_demodulation,[],[f18504,f68])).
% 38.78/5.23  fof(f68,plain,(
% 38.78/5.23    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_8),
% 38.78/5.23    inference(avatar_component_clause,[],[f67])).
% 38.78/5.23  fof(f18504,plain,(
% 38.78/5.23    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2)) = k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),sK2)))) ) | (~spl3_88 | ~spl3_235)),
% 38.78/5.23    inference(superposition,[],[f1668,f18462])).
% 38.78/5.23  fof(f18462,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k5_xboole_0(X1,k4_xboole_0(X1,sK2))) ) | ~spl3_235),
% 38.78/5.23    inference(avatar_component_clause,[],[f18461])).
% 38.78/5.23  fof(f1668,plain,(
% 38.78/5.23    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)) ) | ~spl3_88),
% 38.78/5.23    inference(avatar_component_clause,[],[f1667])).
% 38.78/5.23  fof(f18447,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,sK2))))) ) | (~spl3_23 | ~spl3_88 | ~spl3_234)),
% 38.78/5.23    inference(forward_demodulation,[],[f18381,f206])).
% 38.78/5.23  fof(f18381,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),sK2)) = k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8)))))) ) | (~spl3_88 | ~spl3_234)),
% 38.78/5.23    inference(superposition,[],[f1668,f18344])).
% 38.78/5.23  fof(f18344,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,sK2))) ) | ~spl3_234),
% 38.78/5.23    inference(avatar_component_clause,[],[f18343])).
% 38.78/5.23  fof(f53896,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9))) = k5_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X9,k4_xboole_0(X9,sK2)))))) ) | (~spl3_69 | ~spl3_120 | ~spl3_337)),
% 38.78/5.23    inference(forward_demodulation,[],[f53731,f3185])).
% 38.78/5.23  fof(f3185,plain,(
% 38.78/5.23    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X6,X7)))) ) | ~spl3_120),
% 38.78/5.23    inference(avatar_component_clause,[],[f3184])).
% 38.78/5.23  fof(f53731,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,X9))) = k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),k4_xboole_0(X9,sK2)))) ) | (~spl3_69 | ~spl3_337)),
% 38.78/5.23    inference(superposition,[],[f48075,f1140])).
% 38.78/5.23  fof(f48075,plain,(
% 38.78/5.23    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X1,X0)))) ) | ~spl3_337),
% 38.78/5.23    inference(avatar_component_clause,[],[f48074])).
% 38.78/5.23  fof(f60854,plain,(
% 38.78/5.23    spl3_381 | ~spl3_67 | ~spl3_256 | ~spl3_375 | ~spl3_378),
% 38.78/5.23    inference(avatar_split_clause,[],[f60817,f60603,f59745,f22191,f1025,f60852])).
% 38.78/5.23  fof(f22191,plain,(
% 38.78/5.23    spl3_256 <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_256])])).
% 38.78/5.23  fof(f59745,plain,(
% 38.78/5.23    spl3_375 <=> ! [X8] : k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_375])])).
% 38.78/5.23  fof(f60603,plain,(
% 38.78/5.23    spl3_378 <=> ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_378])])).
% 38.78/5.23  fof(f60817,plain,(
% 38.78/5.23    ( ! [X15] : (k4_xboole_0(X15,sK2) = k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15))) ) | (~spl3_67 | ~spl3_256 | ~spl3_375 | ~spl3_378)),
% 38.78/5.23    inference(forward_demodulation,[],[f60816,f59746])).
% 38.78/5.23  fof(f59746,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))) ) | ~spl3_375),
% 38.78/5.23    inference(avatar_component_clause,[],[f59745])).
% 38.78/5.23  fof(f60816,plain,(
% 38.78/5.23    ( ! [X15] : (k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15)) = k5_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X15))) ) | (~spl3_67 | ~spl3_256 | ~spl3_378)),
% 38.78/5.23    inference(forward_demodulation,[],[f60725,f22192])).
% 38.78/5.23  fof(f22192,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8))) ) | ~spl3_256),
% 38.78/5.23    inference(avatar_component_clause,[],[f22191])).
% 38.78/5.23  fof(f60725,plain,(
% 38.78/5.23    ( ! [X15] : (k4_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(sK1,X15)) = k5_xboole_0(k4_xboole_0(X15,sK2),k4_xboole_0(k4_xboole_0(sK1,X15),k4_xboole_0(sK1,X15)))) ) | (~spl3_67 | ~spl3_378)),
% 38.78/5.23    inference(superposition,[],[f1026,f60604])).
% 38.78/5.23  fof(f60604,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))) ) | ~spl3_378),
% 38.78/5.23    inference(avatar_component_clause,[],[f60603])).
% 38.78/5.23  fof(f60850,plain,(
% 38.78/5.23    spl3_380 | ~spl3_7 | ~spl3_23 | ~spl3_113),
% 38.78/5.23    inference(avatar_split_clause,[],[f5468,f2728,f205,f63,f60848])).
% 38.78/5.23  fof(f60605,plain,(
% 38.78/5.23    spl3_378 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_202 | ~spl3_238 | ~spl3_244 | ~spl3_248 | ~spl3_285 | ~spl3_300 | ~spl3_303 | ~spl3_307 | ~spl3_310 | ~spl3_336 | ~spl3_377),
% 38.78/5.23    inference(avatar_split_clause,[],[f60563,f60293,f46545,f42803,f41935,f40536,f36586,f35496,f20227,f19505,f19203,f12101,f9792,f9125,f7267,f5958,f5950,f5017,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1663,f1231,f1025,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f60603])).
% 38.78/5.23  fof(f88,plain,(
% 38.78/5.23    spl3_10 <=> sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 38.78/5.23  fof(f93,plain,(
% 38.78/5.23    spl3_11 <=> k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 38.78/5.23  fof(f100,plain,(
% 38.78/5.23    spl3_12 <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k5_xboole_0(sK2,X0)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 38.78/5.23  fof(f384,plain,(
% 38.78/5.23    spl3_36 <=> ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X7)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 38.78/5.23  fof(f388,plain,(
% 38.78/5.23    spl3_37 <=> k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 38.78/5.23  fof(f393,plain,(
% 38.78/5.23    spl3_38 <=> ! [X5] : k4_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X5))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 38.78/5.23  fof(f478,plain,(
% 38.78/5.23    spl3_41 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 38.78/5.23  fof(f584,plain,(
% 38.78/5.23    spl3_50 <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 38.78/5.23  fof(f681,plain,(
% 38.78/5.23    spl3_55 <=> ! [X1] : k4_xboole_0(sK2,X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 38.78/5.23  fof(f693,plain,(
% 38.78/5.23    spl3_58 <=> ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 38.78/5.23  fof(f697,plain,(
% 38.78/5.23    spl3_59 <=> ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 38.78/5.23  fof(f807,plain,(
% 38.78/5.23    spl3_61 <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 38.78/5.23  fof(f945,plain,(
% 38.78/5.23    spl3_64 <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 38.78/5.23  fof(f949,plain,(
% 38.78/5.23    spl3_65 <=> ! [X10] : k4_xboole_0(sK2,X10) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X10)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 38.78/5.23  fof(f1231,plain,(
% 38.78/5.23    spl3_71 <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 38.78/5.23  fof(f1663,plain,(
% 38.78/5.23    spl3_87 <=> ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 38.78/5.23  fof(f1718,plain,(
% 38.78/5.23    spl3_89 <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 38.78/5.23  fof(f2049,plain,(
% 38.78/5.23    spl3_96 <=> ! [X1,X2] : k4_xboole_0(k4_xboole_0(sK2,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X1),X2)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 38.78/5.23  fof(f2077,plain,(
% 38.78/5.23    spl3_103 <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 38.78/5.23  fof(f2085,plain,(
% 38.78/5.23    spl3_105 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).
% 38.78/5.23  fof(f2724,plain,(
% 38.78/5.23    spl3_112 <=> ! [X1,X2] : k4_xboole_0(k4_xboole_0(sK1,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X1),X2)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).
% 38.78/5.23  fof(f2740,plain,(
% 38.78/5.23    spl3_116 <=> ! [X9,X10] : k4_xboole_0(k4_xboole_0(sK2,X9),X10) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X9),X10)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).
% 38.78/5.23  fof(f3192,plain,(
% 38.78/5.23    spl3_122 <=> ! [X3,X4] : k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X4))) = k4_xboole_0(k4_xboole_0(sK2,X3),X4)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).
% 38.78/5.23  fof(f3544,plain,(
% 38.78/5.23    spl3_128 <=> ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(k4_xboole_0(sK1,sK1),k5_xboole_0(sK2,X0))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).
% 38.78/5.23  fof(f3688,plain,(
% 38.78/5.23    spl3_134 <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_134])])).
% 38.78/5.23  fof(f4268,plain,(
% 38.78/5.23    spl3_137 <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).
% 38.78/5.23  fof(f4451,plain,(
% 38.78/5.23    spl3_139 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).
% 38.78/5.23  fof(f4455,plain,(
% 38.78/5.23    spl3_140 <=> ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(sK1,sK1),X7))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).
% 38.78/5.23  fof(f4459,plain,(
% 38.78/5.23    spl3_141 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).
% 38.78/5.23  fof(f5017,plain,(
% 38.78/5.23    spl3_145 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_145])])).
% 38.78/5.23  fof(f5950,plain,(
% 38.78/5.23    spl3_158 <=> ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,sK1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_158])])).
% 38.78/5.23  fof(f5958,plain,(
% 38.78/5.23    spl3_160 <=> ! [X9] : k4_xboole_0(k4_xboole_0(sK1,X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_160])])).
% 38.78/5.23  fof(f7267,plain,(
% 38.78/5.23    spl3_166 <=> ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_166])])).
% 38.78/5.23  fof(f9125,plain,(
% 38.78/5.23    spl3_183 <=> ! [X9] : k4_xboole_0(sK1,X9) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_183])])).
% 38.78/5.23  fof(f9792,plain,(
% 38.78/5.23    spl3_189 <=> ! [X1,X3,X2] : k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_189])])).
% 38.78/5.23  fof(f12101,plain,(
% 38.78/5.23    spl3_202 <=> ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_202])])).
% 38.78/5.23  fof(f19203,plain,(
% 38.78/5.23    spl3_238 <=> ! [X6] : k4_xboole_0(k4_xboole_0(sK1,sK1),X6) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_238])])).
% 38.78/5.23  fof(f19505,plain,(
% 38.78/5.23    spl3_244 <=> ! [X8] : k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_244])])).
% 38.78/5.23  fof(f20227,plain,(
% 38.78/5.23    spl3_248 <=> ! [X66] : k4_xboole_0(sK1,X66) = k4_xboole_0(k4_xboole_0(sK1,X66),X66)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_248])])).
% 38.78/5.23  fof(f35496,plain,(
% 38.78/5.23    spl3_285 <=> ! [X7,X8,X6] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7)))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_285])])).
% 38.78/5.23  fof(f36586,plain,(
% 38.78/5.23    spl3_300 <=> ! [X17] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X17,sK1))) = k4_xboole_0(k4_xboole_0(X17,sK1),X17)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_300])])).
% 38.78/5.23  fof(f40536,plain,(
% 38.78/5.23    spl3_303 <=> ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_303])])).
% 38.78/5.23  fof(f41935,plain,(
% 38.78/5.23    spl3_307 <=> ! [X9,X11,X8,X10] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X8,X9))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_307])])).
% 38.78/5.23  fof(f42803,plain,(
% 38.78/5.23    spl3_310 <=> ! [X18] : k4_xboole_0(k4_xboole_0(sK1,sK1),X18) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_310])])).
% 38.78/5.23  fof(f46545,plain,(
% 38.78/5.23    spl3_336 <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_336])])).
% 38.78/5.23  fof(f60293,plain,(
% 38.78/5.23    spl3_377 <=> ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_377])])).
% 38.78/5.23  fof(f60563,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_202 | ~spl3_238 | ~spl3_244 | ~spl3_248 | ~spl3_285 | ~spl3_300 | ~spl3_303 | ~spl3_307 | ~spl3_310 | ~spl3_336 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60562,f19506])).
% 38.78/5.23  fof(f19506,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))) ) | ~spl3_244),
% 38.78/5.23    inference(avatar_component_clause,[],[f19505])).
% 38.78/5.23  fof(f60562,plain,(
% 38.78/5.23    ( ! [X1] : (k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_202 | ~spl3_238 | ~spl3_248 | ~spl3_285 | ~spl3_300 | ~spl3_303 | ~spl3_307 | ~spl3_310 | ~spl3_336 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60561,f19328])).
% 38.78/5.23  fof(f19328,plain,(
% 38.78/5.23    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(sK1,X64),X65) = k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X65,X64))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_238)),
% 38.78/5.23    inference(forward_demodulation,[],[f19319,f5372])).
% 38.78/5.23  fof(f5372,plain,(
% 38.78/5.23    ( ! [X6,X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X4)) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X4,X6)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_113)),
% 38.78/5.23    inference(forward_demodulation,[],[f5197,f206])).
% 38.78/5.23  fof(f5197,plain,(
% 38.78/5.23    ( ! [X6,X4,X5] : (k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X4))) ) | (~spl3_8 | ~spl3_113)),
% 38.78/5.23    inference(superposition,[],[f2729,f68])).
% 38.78/5.23  fof(f19319,plain,(
% 38.78/5.23    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(sK1,X64),X65) = k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),X65)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_238)),
% 38.78/5.23    inference(backward_demodulation,[],[f13909,f19317])).
% 38.78/5.23  fof(f19317,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238)),
% 38.78/5.23    inference(backward_demodulation,[],[f4805,f19303])).
% 38.78/5.23  fof(f19303,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238)),
% 38.78/5.23    inference(backward_demodulation,[],[f4033,f19302])).
% 38.78/5.23  fof(f19302,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238)),
% 38.78/5.23    inference(backward_demodulation,[],[f9428,f19301])).
% 38.78/5.23  fof(f19301,plain,(
% 38.78/5.23    ( ! [X18] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X18) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_137 | ~spl3_158 | ~spl3_238)),
% 38.78/5.23    inference(forward_demodulation,[],[f19300,f5951])).
% 38.78/5.23  fof(f5951,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,sK1)))) ) | ~spl3_158),
% 38.78/5.23    inference(avatar_component_clause,[],[f5950])).
% 38.78/5.23  fof(f19300,plain,(
% 38.78/5.23    ( ! [X18] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X18,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_137 | ~spl3_238)),
% 38.78/5.23    inference(forward_demodulation,[],[f19299,f5372])).
% 38.78/5.23  fof(f19299,plain,(
% 38.78/5.23    ( ! [X18] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X18)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)) ) | (~spl3_113 | ~spl3_137 | ~spl3_238)),
% 38.78/5.23    inference(forward_demodulation,[],[f19261,f4269])).
% 38.78/5.23  fof(f4269,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))) ) | ~spl3_137),
% 38.78/5.23    inference(avatar_component_clause,[],[f4268])).
% 38.78/5.23  fof(f19261,plain,(
% 38.78/5.23    ( ! [X18] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X18)) = k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(sK1,sK1))),X18)) ) | (~spl3_113 | ~spl3_238)),
% 38.78/5.23    inference(superposition,[],[f2729,f19204])).
% 38.78/5.23  fof(f19204,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X6) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6))) ) | ~spl3_238),
% 38.78/5.23    inference(avatar_component_clause,[],[f19203])).
% 38.78/5.23  fof(f9428,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X8),X8)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_183)),
% 38.78/5.23    inference(forward_demodulation,[],[f9427,f5018])).
% 38.78/5.23  fof(f5018,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))) ) | ~spl3_145),
% 38.78/5.23    inference(avatar_component_clause,[],[f5017])).
% 38.78/5.23  fof(f9427,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X8)),X8)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_183)),
% 38.78/5.23    inference(forward_demodulation,[],[f9426,f5133])).
% 38.78/5.23  fof(f5133,plain,(
% 38.78/5.23    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X3,X4))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(backward_demodulation,[],[f3823,f5128])).
% 38.78/5.23  fof(f5128,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),X10) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(backward_demodulation,[],[f4822,f5127])).
% 38.78/5.23  fof(f5127,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X9),X10),sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_112 | ~spl3_122 | ~spl3_134 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(forward_demodulation,[],[f5126,f4757])).
% 38.78/5.23  fof(f4757,plain,(
% 38.78/5.23    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X5),X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6))) ) | (~spl3_112 | ~spl3_122 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4724,f3193])).
% 38.78/5.23  fof(f3193,plain,(
% 38.78/5.23    ( ! [X4,X3] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X4))) = k4_xboole_0(k4_xboole_0(sK2,X3),X4)) ) | ~spl3_122),
% 38.78/5.23    inference(avatar_component_clause,[],[f3192])).
% 38.78/5.23  fof(f4724,plain,(
% 38.78/5.23    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X5),X6))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6))) ) | (~spl3_112 | ~spl3_141)),
% 38.78/5.23    inference(superposition,[],[f4460,f2725])).
% 38.78/5.23  fof(f2725,plain,(
% 38.78/5.23    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X1),X2)))) ) | ~spl3_112),
% 38.78/5.23    inference(avatar_component_clause,[],[f2724])).
% 38.78/5.23  fof(f4460,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))) ) | ~spl3_141),
% 38.78/5.23    inference(avatar_component_clause,[],[f4459])).
% 38.78/5.23  fof(f5126,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134 | ~spl3_145)),
% 38.78/5.23    inference(forward_demodulation,[],[f5125,f3803])).
% 38.78/5.23  fof(f3803,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.23    inference(forward_demodulation,[],[f3695,f3772])).
% 38.78/5.23  fof(f3772,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.23    inference(backward_demodulation,[],[f1719,f3771])).
% 38.78/5.23  fof(f3771,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(sK2,k4_xboole_0(X0,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.23    inference(forward_demodulation,[],[f3768,f950])).
% 38.78/5.23  fof(f950,plain,(
% 38.78/5.23    ( ! [X10] : (k4_xboole_0(sK2,X10) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X10)))) ) | ~spl3_65),
% 38.78/5.23    inference(avatar_component_clause,[],[f949])).
% 38.78/5.23  fof(f3768,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_89 | ~spl3_134)),
% 38.78/5.23    inference(backward_demodulation,[],[f1761,f3765])).
% 38.78/5.23  fof(f3765,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))) ) | (~spl3_8 | ~spl3_61 | ~spl3_134)),
% 38.78/5.23    inference(forward_demodulation,[],[f3694,f808])).
% 38.78/5.23  fof(f808,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) ) | ~spl3_61),
% 38.78/5.23    inference(avatar_component_clause,[],[f807])).
% 38.78/5.23  fof(f3694,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X1,sK1)))) ) | (~spl3_8 | ~spl3_134)),
% 38.78/5.23    inference(superposition,[],[f3689,f68])).
% 38.78/5.23  fof(f3689,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))) ) | ~spl3_134),
% 38.78/5.23    inference(avatar_component_clause,[],[f3688])).
% 38.78/5.23  fof(f1761,plain,(
% 38.78/5.23    ( ! [X0] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_89)),
% 38.78/5.23    inference(backward_demodulation,[],[f501,f1759])).
% 38.78/5.23  fof(f1759,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2))) ) | (~spl3_38 | ~spl3_55 | ~spl3_89)),
% 38.78/5.23    inference(forward_demodulation,[],[f1734,f682])).
% 38.78/5.23  fof(f682,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(sK2,X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))) ) | ~spl3_55),
% 38.78/5.23    inference(avatar_component_clause,[],[f681])).
% 38.78/5.23  fof(f1734,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2)))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2))) ) | (~spl3_38 | ~spl3_89)),
% 38.78/5.23    inference(superposition,[],[f394,f1719])).
% 38.78/5.23  fof(f394,plain,(
% 38.78/5.23    ( ! [X5] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X5))) ) | ~spl3_38),
% 38.78/5.23    inference(avatar_component_clause,[],[f393])).
% 38.78/5.23  fof(f501,plain,(
% 38.78/5.23    ( ! [X0] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41)),
% 38.78/5.23    inference(backward_demodulation,[],[f443,f495])).
% 38.78/5.23  fof(f495,plain,(
% 38.78/5.23    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) | (~spl3_36 | ~spl3_41)),
% 38.78/5.23    inference(superposition,[],[f385,f480])).
% 38.78/5.23  fof(f480,plain,(
% 38.78/5.23    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | ~spl3_41),
% 38.78/5.23    inference(avatar_component_clause,[],[f478])).
% 38.78/5.23  fof(f385,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(sK2,X7) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X7)))) ) | ~spl3_36),
% 38.78/5.23    inference(avatar_component_clause,[],[f384])).
% 38.78/5.23  fof(f443,plain,(
% 38.78/5.23    ( ! [X0] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK2,sK1),X0))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X0))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_37 | ~spl3_38)),
% 38.78/5.23    inference(backward_demodulation,[],[f177,f440])).
% 38.78/5.23  fof(f440,plain,(
% 38.78/5.23    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_37 | ~spl3_38)),
% 38.78/5.23    inference(forward_demodulation,[],[f438,f95])).
% 38.78/5.23  fof(f95,plain,(
% 38.78/5.23    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2) | ~spl3_11),
% 38.78/5.23    inference(avatar_component_clause,[],[f93])).
% 38.78/5.23  fof(f438,plain,(
% 38.78/5.23    k4_xboole_0(sK2,sK2) = k5_xboole_0(sK2,sK2) | (~spl3_7 | ~spl3_10 | ~spl3_37 | ~spl3_38)),
% 38.78/5.23    inference(backward_demodulation,[],[f412,f423])).
% 38.78/5.23  fof(f423,plain,(
% 38.78/5.23    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | (~spl3_10 | ~spl3_38)),
% 38.78/5.23    inference(superposition,[],[f394,f90])).
% 38.78/5.23  fof(f90,plain,(
% 38.78/5.23    sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) | ~spl3_10),
% 38.78/5.23    inference(avatar_component_clause,[],[f88])).
% 38.78/5.23  fof(f412,plain,(
% 38.78/5.23    k4_xboole_0(sK2,sK2) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) | (~spl3_7 | ~spl3_37)),
% 38.78/5.23    inference(superposition,[],[f64,f390])).
% 38.78/5.23  fof(f390,plain,(
% 38.78/5.23    k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_37),
% 38.78/5.23    inference(avatar_component_clause,[],[f388])).
% 38.78/5.23  fof(f177,plain,(
% 38.78/5.23    ( ! [X0] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),X0))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK2),X0))) ) | (~spl3_7 | ~spl3_12)),
% 38.78/5.23    inference(superposition,[],[f101,f64])).
% 38.78/5.23  fof(f101,plain,(
% 38.78/5.23    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k5_xboole_0(sK2,X0)) ) | ~spl3_12),
% 38.78/5.23    inference(avatar_component_clause,[],[f100])).
% 38.78/5.23  fof(f1719,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)))) ) | ~spl3_89),
% 38.78/5.23    inference(avatar_component_clause,[],[f1718])).
% 38.78/5.23  fof(f3695,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X2,sK1)))) ) | (~spl3_8 | ~spl3_134)),
% 38.78/5.23    inference(superposition,[],[f3689,f68])).
% 38.78/5.23  fof(f5125,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,X10)))) ) | (~spl3_23 | ~spl3_145)),
% 38.78/5.23    inference(forward_demodulation,[],[f5106,f206])).
% 38.78/5.23  fof(f5106,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X9)),X10)) ) | (~spl3_23 | ~spl3_145)),
% 38.78/5.23    inference(superposition,[],[f206,f5018])).
% 38.78/5.23  fof(f4822,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),X10) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X9),X10),sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4821,f4757])).
% 38.78/5.23  fof(f4821,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),X10)) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4820,f4809])).
% 38.78/5.23  fof(f4809,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X7) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X7),sK1)) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4808,f4802])).
% 38.78/5.23  fof(f4802,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(backward_demodulation,[],[f4460,f4791])).
% 38.78/5.23  fof(f4791,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6)) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4790,f3551])).
% 38.78/5.23  fof(f3551,plain,(
% 38.78/5.23    ( ! [X5] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X5) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X5))) ) | (~spl3_105 | ~spl3_128)),
% 38.78/5.23    inference(superposition,[],[f3545,f2086])).
% 38.78/5.23  fof(f2086,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))) ) | ~spl3_105),
% 38.78/5.23    inference(avatar_component_clause,[],[f2085])).
% 38.78/5.23  fof(f3545,plain,(
% 38.78/5.23    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(k4_xboole_0(sK1,sK1),k5_xboole_0(sK2,X0))) ) | ~spl3_128),
% 38.78/5.23    inference(avatar_component_clause,[],[f3544])).
% 38.78/5.23  fof(f4790,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X6))) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_116 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4742,f4599])).
% 38.78/5.23  fof(f4599,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X0),sK1))) ) | (~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_116 | ~spl3_139)),
% 38.78/5.23    inference(backward_demodulation,[],[f1261,f4553])).
% 38.78/5.23  fof(f4553,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))) ) | (~spl3_116 | ~spl3_139)),
% 38.78/5.23    inference(superposition,[],[f4452,f2741])).
% 38.78/5.23  fof(f2741,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK2,X9),X10) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X9),X10)))) ) | ~spl3_116),
% 38.78/5.23    inference(avatar_component_clause,[],[f2740])).
% 38.78/5.23  fof(f4452,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))) ) | ~spl3_139),
% 38.78/5.23    inference(avatar_component_clause,[],[f4451])).
% 38.78/5.23  fof(f1261,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)))) ) | (~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71)),
% 38.78/5.23    inference(forward_demodulation,[],[f1253,f1259])).
% 38.78/5.23  fof(f1259,plain,(
% 38.78/5.23    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) | (~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71)),
% 38.78/5.23    inference(forward_demodulation,[],[f1258,f586])).
% 38.78/5.23  fof(f586,plain,(
% 38.78/5.23    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_50),
% 38.78/5.23    inference(avatar_component_clause,[],[f584])).
% 38.78/5.23  fof(f1258,plain,(
% 38.78/5.23    k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) | (~spl3_59 | ~spl3_64 | ~spl3_71)),
% 38.78/5.23    inference(forward_demodulation,[],[f1252,f698])).
% 38.78/5.23  fof(f698,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) | ~spl3_59),
% 38.78/5.23    inference(avatar_component_clause,[],[f697])).
% 38.78/5.23  fof(f1252,plain,(
% 38.78/5.23    k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) | (~spl3_64 | ~spl3_71)),
% 38.78/5.23    inference(superposition,[],[f946,f1233])).
% 38.78/5.23  fof(f1233,plain,(
% 38.78/5.23    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) | ~spl3_71),
% 38.78/5.23    inference(avatar_component_clause,[],[f1231])).
% 38.78/5.23  fof(f946,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sK2))) ) | ~spl3_64),
% 38.78/5.23    inference(avatar_component_clause,[],[f945])).
% 38.78/5.23  fof(f1253,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)),X0)) ) | (~spl3_23 | ~spl3_71)),
% 38.78/5.23    inference(superposition,[],[f206,f1233])).
% 38.78/5.23  fof(f4742,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X6),sK1)))) ) | (~spl3_7 | ~spl3_141)),
% 38.78/5.23    inference(superposition,[],[f64,f4460])).
% 38.78/5.23  fof(f4808,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X7),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X7))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4807,f4269])).
% 38.78/5.23  fof(f4807,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X7),sK1) = k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(sK1,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4806,f4791])).
% 38.78/5.23  fof(f4806,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X7),sK1),sK1)) ) | (~spl3_8 | ~spl3_96 | ~spl3_116 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4743,f4756])).
% 38.78/5.23  fof(f4756,plain,(
% 38.78/5.23    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X3),X4),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X3),X4))) ) | (~spl3_96 | ~spl3_116 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4723,f2741])).
% 38.78/5.23  fof(f4723,plain,(
% 38.78/5.23    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X3),X4))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X3),X4))) ) | (~spl3_96 | ~spl3_141)),
% 38.78/5.23    inference(superposition,[],[f4460,f2050])).
% 38.78/5.23  fof(f2050,plain,(
% 38.78/5.23    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X1),X2)))) ) | ~spl3_96),
% 38.78/5.23    inference(avatar_component_clause,[],[f2049])).
% 38.78/5.23  fof(f4743,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X7),sK1))) ) | (~spl3_8 | ~spl3_141)),
% 38.78/5.23    inference(superposition,[],[f68,f4460])).
% 38.78/5.23  fof(f4820,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),sK1),X10)) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4819,f4791])).
% 38.78/5.23  fof(f4819,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X9),sK1),sK1),X10)) ) | (~spl3_23 | ~spl3_96 | ~spl3_116 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4745,f4756])).
% 38.78/5.23  fof(f4745,plain,(
% 38.78/5.23    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X9),X10))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK2,X9),sK1)),X10)) ) | (~spl3_23 | ~spl3_141)),
% 38.78/5.23    inference(superposition,[],[f206,f4460])).
% 38.78/5.23  fof(f3823,plain,(
% 38.78/5.23    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X3),X4)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.23    inference(forward_demodulation,[],[f3706,f3772])).
% 38.78/5.23  fof(f3706,plain,(
% 38.78/5.23    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X3,sK1))),X4)) ) | (~spl3_23 | ~spl3_134)),
% 38.78/5.23    inference(superposition,[],[f206,f3689])).
% 38.78/5.23  fof(f9426,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X8))),X8)) ) | (~spl3_23 | ~spl3_113 | ~spl3_183)),
% 38.78/5.23    inference(forward_demodulation,[],[f9425,f206])).
% 38.78/5.23  fof(f9425,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),X8),X8)) ) | (~spl3_113 | ~spl3_183)),
% 38.78/5.23    inference(forward_demodulation,[],[f9332,f2729])).
% 38.78/5.23  fof(f9332,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X8))),X8)) ) | (~spl3_113 | ~spl3_183)),
% 38.78/5.23    inference(superposition,[],[f2729,f9126])).
% 38.78/5.23  fof(f9126,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(sK1,X9) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))) ) | ~spl3_183),
% 38.78/5.23    inference(avatar_component_clause,[],[f9125])).
% 38.78/5.23  fof(f4033,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(sK1,X8) = k5_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)))) ) | (~spl3_58 | ~spl3_103)),
% 38.78/5.23    inference(superposition,[],[f2078,f694])).
% 38.78/5.23  fof(f694,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) | ~spl3_58),
% 38.78/5.23    inference(avatar_component_clause,[],[f693])).
% 38.78/5.23  fof(f2078,plain,(
% 38.78/5.23    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) ) | ~spl3_103),
% 38.78/5.23    inference(avatar_component_clause,[],[f2077])).
% 38.78/5.23  fof(f4805,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_140 | ~spl3_141)),
% 38.78/5.23    inference(backward_demodulation,[],[f4734,f4791])).
% 38.78/5.23  fof(f4734,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK2,X0),sK1))) ) | (~spl3_140 | ~spl3_141)),
% 38.78/5.23    inference(superposition,[],[f4456,f4460])).
% 38.78/5.23  fof(f4456,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(sK1,sK1),X7))) ) | ~spl3_140),
% 38.78/5.23    inference(avatar_component_clause,[],[f4455])).
% 38.78/5.23  fof(f13909,plain,(
% 38.78/5.23    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(sK1,X64),X65) = k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189)),
% 38.78/5.23    inference(forward_demodulation,[],[f13908,f9126])).
% 38.78/5.23  fof(f13908,plain,(
% 38.78/5.23    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,sK1),X64)),X65)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_160 | ~spl3_166 | ~spl3_189)),
% 38.78/5.23    inference(forward_demodulation,[],[f13907,f7268])).
% 38.78/5.23  fof(f7268,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1))) ) | ~spl3_166),
% 38.78/5.23    inference(avatar_component_clause,[],[f7267])).
% 38.78/5.23  fof(f13907,plain,(
% 38.78/5.23    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X64,sK1))),X65)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_160 | ~spl3_189)),
% 38.78/5.23    inference(forward_demodulation,[],[f13271,f5423])).
% 38.78/5.23  fof(f5423,plain,(
% 38.78/5.23    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X5,X6))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(backward_demodulation,[],[f4757,f5418])).
% 38.78/5.23  fof(f5418,plain,(
% 38.78/5.23    ( ! [X30,X31] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X30),X31),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(forward_demodulation,[],[f5417,f3803])).
% 38.78/5.23  fof(f5417,plain,(
% 38.78/5.23    ( ! [X30,X31] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X30),X31),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(forward_demodulation,[],[f5416,f4757])).
% 38.78/5.23  fof(f5416,plain,(
% 38.78/5.23    ( ! [X30,X31] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X30),X31))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(forward_demodulation,[],[f5415,f5133])).
% 38.78/5.23  fof(f5415,plain,(
% 38.78/5.23    ( ! [X30,X31] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,sK1),X31)))) ) | (~spl3_23 | ~spl3_113 | ~spl3_145)),
% 38.78/5.23    inference(forward_demodulation,[],[f5207,f206])).
% 38.78/5.23  fof(f5207,plain,(
% 38.78/5.23    ( ! [X30,X31] : (k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,X30),k4_xboole_0(k4_xboole_0(sK1,sK1),X31))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X30)),X31)) ) | (~spl3_113 | ~spl3_145)),
% 38.78/5.23    inference(superposition,[],[f2729,f5018])).
% 38.78/5.23  fof(f13271,plain,(
% 38.78/5.23    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(sK1,sK1)),X65))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X64),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X64),sK1))),X65)) ) | (~spl3_160 | ~spl3_189)),
% 38.78/5.23    inference(superposition,[],[f9793,f5959])).
% 38.78/5.23  fof(f5959,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9))) ) | ~spl3_160),
% 38.78/5.23    inference(avatar_component_clause,[],[f5958])).
% 38.78/5.23  fof(f9793,plain,(
% 38.78/5.23    ( ! [X2,X3,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3)) ) | ~spl3_189),
% 38.78/5.23    inference(avatar_component_clause,[],[f9792])).
% 38.78/5.23  fof(f60561,plain,(
% 38.78/5.23    ( ! [X1] : (k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X1,sK2),X1))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_202 | ~spl3_238 | ~spl3_248 | ~spl3_285 | ~spl3_300 | ~spl3_303 | ~spl3_307 | ~spl3_310 | ~spl3_336 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60560,f46878])).
% 38.78/5.23  fof(f46878,plain,(
% 38.78/5.23    ( ! [X57,X58] : (k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,X58)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_300 | ~spl3_303 | ~spl3_307 | ~spl3_310 | ~spl3_336)),
% 38.78/5.23    inference(forward_demodulation,[],[f46876,f40787])).
% 38.78/5.23  fof(f40787,plain,(
% 38.78/5.23    ( ! [X94,X93] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X93,k4_xboole_0(sK1,sK1)),X94))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X93,X94)))) ) | (~spl3_23 | ~spl3_303)),
% 38.78/5.23    inference(forward_demodulation,[],[f40679,f206])).
% 38.78/5.23  fof(f40679,plain,(
% 38.78/5.23    ( ! [X94,X93] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X93,k4_xboole_0(sK1,sK1)),X94))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X93)),X94)) ) | (~spl3_23 | ~spl3_303)),
% 38.78/5.23    inference(superposition,[],[f206,f40537])).
% 38.78/5.23  fof(f40537,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))) ) | ~spl3_303),
% 38.78/5.23    inference(avatar_component_clause,[],[f40536])).
% 38.78/5.23  fof(f46876,plain,(
% 38.78/5.23    ( ! [X57,X58] : (k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(sK1,sK1)),X58)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_300 | ~spl3_307 | ~spl3_310 | ~spl3_336)),
% 38.78/5.23    inference(backward_demodulation,[],[f44697,f46875])).
% 38.78/5.23  fof(f46875,plain,(
% 38.78/5.23    ( ! [X28,X29] : (k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(sK1,sK1)),X29) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X28,sK1),X28)),X29)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_310 | ~spl3_336)),
% 38.78/5.23    inference(forward_demodulation,[],[f46625,f46197])).
% 38.78/5.23  fof(f46197,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_310)),
% 38.78/5.23    inference(backward_demodulation,[],[f3829,f46193])).
% 38.78/5.23  fof(f46193,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_310)),
% 38.78/5.23    inference(forward_demodulation,[],[f46192,f4456])).
% 38.78/5.23  fof(f46192,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9)) = k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_310)),
% 38.78/5.23    inference(forward_demodulation,[],[f46068,f4812])).
% 38.78/5.23  fof(f4812,plain,(
% 38.78/5.23    ( ! [X10] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X10),k4_xboole_0(k4_xboole_0(sK1,sK1),X10))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(backward_demodulation,[],[f1742,f4809])).
% 38.78/5.23  fof(f1742,plain,(
% 38.78/5.23    ( ! [X10] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X10),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X10),sK1))) ) | (~spl3_87 | ~spl3_89)),
% 38.78/5.23    inference(superposition,[],[f1664,f1719])).
% 38.78/5.23  fof(f1664,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1))) ) | ~spl3_87),
% 38.78/5.23    inference(avatar_component_clause,[],[f1663])).
% 38.78/5.23  fof(f46068,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(sK1,sK1),X9)) = k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9)))) ) | (~spl3_67 | ~spl3_310)),
% 38.78/5.23    inference(superposition,[],[f1026,f42804])).
% 38.78/5.23  fof(f42804,plain,(
% 38.78/5.23    ( ! [X18] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X18) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X18)) ) | ~spl3_310),
% 38.78/5.23    inference(avatar_component_clause,[],[f42803])).
% 38.78/5.23  fof(f3829,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(sK1,sK1),X11)),X12)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.23    inference(forward_demodulation,[],[f3712,f3772])).
% 38.78/5.23  fof(f3712,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK1,sK1)),X12))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X11,sK1)))),X12)) ) | (~spl3_23 | ~spl3_134)),
% 38.78/5.23    inference(superposition,[],[f206,f3689])).
% 38.78/5.23  fof(f46625,plain,(
% 38.78/5.23    ( ! [X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(sK1,sK1)),X29))) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X28,sK1),X28)),X29)) ) | (~spl3_23 | ~spl3_336)),
% 38.78/5.23    inference(superposition,[],[f206,f46546])).
% 38.78/5.23  fof(f46546,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)) ) | ~spl3_336),
% 38.78/5.23    inference(avatar_component_clause,[],[f46545])).
% 38.78/5.23  fof(f44697,plain,(
% 38.78/5.23    ( ! [X57,X58] : (k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(k4_xboole_0(X57,sK1),X57)),X58)))) ) | (~spl3_112 | ~spl3_300 | ~spl3_307)),
% 38.78/5.23    inference(forward_demodulation,[],[f43193,f2725])).
% 38.78/5.23  fof(f43193,plain,(
% 38.78/5.23    ( ! [X57,X58] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X58),k4_xboole_0(sK1,X57)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(k4_xboole_0(X57,sK1),X57)),X58)))) ) | (~spl3_300 | ~spl3_307)),
% 38.78/5.23    inference(superposition,[],[f41936,f36587])).
% 38.78/5.23  fof(f36587,plain,(
% 38.78/5.23    ( ! [X17] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X17,sK1))) = k4_xboole_0(k4_xboole_0(X17,sK1),X17)) ) | ~spl3_300),
% 38.78/5.23    inference(avatar_component_clause,[],[f36586])).
% 38.78/5.23  fof(f41936,plain,(
% 38.78/5.23    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X8,X9))))) ) | ~spl3_307),
% 38.78/5.23    inference(avatar_component_clause,[],[f41935])).
% 38.78/5.23  fof(f60560,plain,(
% 38.78/5.23    ( ! [X1] : (k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_202 | ~spl3_238 | ~spl3_248 | ~spl3_285 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60559,f694])).
% 38.78/5.23  fof(f60559,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))),k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_202 | ~spl3_238 | ~spl3_248 | ~spl3_285 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60558,f68])).
% 38.78/5.23  fof(f60558,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_202 | ~spl3_238 | ~spl3_248 | ~spl3_285 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60557,f12102])).
% 38.78/5.23  fof(f12102,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))) ) | ~spl3_202),
% 38.78/5.23    inference(avatar_component_clause,[],[f12101])).
% 38.78/5.23  fof(f60557,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X1,sK2)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238 | ~spl3_248 | ~spl3_285 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60556,f20388])).
% 38.78/5.23  fof(f20388,plain,(
% 38.78/5.23    ( ! [X19,X18] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X18,X19)) = k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(k4_xboole_0(sK1,X18),X19)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238 | ~spl3_248)),
% 38.78/5.23    inference(forward_demodulation,[],[f20387,f5128])).
% 38.78/5.23  fof(f20387,plain,(
% 38.78/5.23    ( ! [X19,X18] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X18),X19) = k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(k4_xboole_0(sK1,X18),X19)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238 | ~spl3_248)),
% 38.78/5.23    inference(forward_demodulation,[],[f20296,f19302])).
% 38.78/5.23  fof(f20296,plain,(
% 38.78/5.23    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(k4_xboole_0(sK1,X18),X19))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X18),k4_xboole_0(sK1,X18)),X19)) ) | (~spl3_113 | ~spl3_248)),
% 38.78/5.23    inference(superposition,[],[f2729,f20228])).
% 38.78/5.23  fof(f20228,plain,(
% 38.78/5.23    ( ! [X66] : (k4_xboole_0(sK1,X66) = k4_xboole_0(k4_xboole_0(sK1,X66),X66)) ) | ~spl3_248),
% 38.78/5.23    inference(avatar_component_clause,[],[f20227])).
% 38.78/5.23  fof(f60556,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(sK1,X1),sK2))))) ) | (~spl3_23 | ~spl3_113 | ~spl3_285 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60555,f206])).
% 38.78/5.23  fof(f60555,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,X1))),sK2))) ) | (~spl3_113 | ~spl3_285 | ~spl3_377)),
% 38.78/5.23    inference(forward_demodulation,[],[f60404,f2729])).
% 38.78/5.23  fof(f60404,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),sK1)),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(X1,sK2))))) ) | (~spl3_285 | ~spl3_377)),
% 38.78/5.23    inference(superposition,[],[f35497,f60294])).
% 38.78/5.23  fof(f60294,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))) ) | ~spl3_377),
% 38.78/5.23    inference(avatar_component_clause,[],[f60293])).
% 38.78/5.23  fof(f35497,plain,(
% 38.78/5.23    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7)))))) ) | ~spl3_285),
% 38.78/5.23    inference(avatar_component_clause,[],[f35496])).
% 38.78/5.23  fof(f60295,plain,(
% 38.78/5.23    spl3_377 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_89 | ~spl3_95 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_120 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_177 | ~spl3_337 | ~spl3_375 | ~spl3_376),
% 38.78/5.23    inference(avatar_split_clause,[],[f60290,f60048,f59745,f48074,f7312,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f3184,f2740,f2724,f2085,f2049,f2045,f1718,f1231,f953,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f60293])).
% 38.78/5.23  fof(f953,plain,(
% 38.78/5.23    spl3_66 <=> ! [X4] : k4_xboole_0(sK2,X4) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 38.78/5.23  fof(f2045,plain,(
% 38.78/5.23    spl3_95 <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(X1,sK2))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).
% 38.78/5.23  fof(f7312,plain,(
% 38.78/5.23    spl3_177 <=> ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_177])])).
% 38.78/5.23  fof(f60048,plain,(
% 38.78/5.23    spl3_376 <=> ! [X1] : k4_xboole_0(X1,sK2) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,X1),sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_376])])).
% 38.78/5.23  fof(f60290,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_89 | ~spl3_95 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_120 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_177 | ~spl3_337 | ~spl3_375 | ~spl3_376)),
% 38.78/5.23    inference(forward_demodulation,[],[f60289,f59746])).
% 38.78/5.23  fof(f60289,plain,(
% 38.78/5.23    ( ! [X0] : (k5_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_89 | ~spl3_95 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_120 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_177 | ~spl3_337 | ~spl3_376)),
% 38.78/5.23    inference(forward_demodulation,[],[f60288,f4755])).
% 38.78/5.23  fof(f4755,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))) ) | (~spl3_61 | ~spl3_66 | ~spl3_95 | ~spl3_120 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4754,f4452])).
% 38.78/5.23  fof(f4754,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X2,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))) ) | (~spl3_61 | ~spl3_66 | ~spl3_95 | ~spl3_120 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4753,f3185])).
% 38.78/5.23  fof(f4753,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X2)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))) ) | (~spl3_61 | ~spl3_66 | ~spl3_95 | ~spl3_141)),
% 38.78/5.23    inference(forward_demodulation,[],[f4722,f1068])).
% 38.78/5.23  fof(f1068,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))) ) | (~spl3_61 | ~spl3_66)),
% 38.78/5.23    inference(forward_demodulation,[],[f1042,f808])).
% 38.78/5.23  fof(f1042,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))) ) | (~spl3_61 | ~spl3_66)),
% 38.78/5.23    inference(superposition,[],[f808,f954])).
% 38.78/5.23  fof(f954,plain,(
% 38.78/5.23    ( ! [X4] : (k4_xboole_0(sK2,X4) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2)))) ) | ~spl3_66),
% 38.78/5.23    inference(avatar_component_clause,[],[f953])).
% 38.78/5.23  fof(f4722,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK2)))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,k4_xboole_0(X2,sK2)))) ) | (~spl3_95 | ~spl3_141)),
% 38.78/5.23    inference(superposition,[],[f4460,f2046])).
% 38.78/5.23  fof(f2046,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(X1,sK2))))) ) | ~spl3_95),
% 38.78/5.23    inference(avatar_component_clause,[],[f2045])).
% 38.78/5.23  fof(f60288,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k5_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,sK2))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_177 | ~spl3_337 | ~spl3_376)),
% 38.78/5.23    inference(forward_demodulation,[],[f60151,f8593])).
% 38.78/5.23  fof(f8593,plain,(
% 38.78/5.23    ( ! [X43,X44] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X43,X44))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_177)),
% 38.78/5.23    inference(forward_demodulation,[],[f8592,f5128])).
% 38.78/5.23  fof(f8592,plain,(
% 38.78/5.23    ( ! [X43,X44] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X43),X44)) ) | (~spl3_23 | ~spl3_112 | ~spl3_158 | ~spl3_177)),
% 38.78/5.23    inference(forward_demodulation,[],[f8591,f5951])).
% 38.78/5.23  fof(f8591,plain,(
% 38.78/5.23    ( ! [X43,X44] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X43,sK1))),X44) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44)) ) | (~spl3_23 | ~spl3_112 | ~spl3_177)),
% 38.78/5.23    inference(forward_demodulation,[],[f8518,f2902])).
% 38.78/5.23  fof(f2902,plain,(
% 38.78/5.23    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X10),X11),X12) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X10),X11),X12)))) ) | ~spl3_112),
% 38.78/5.23    inference(superposition,[],[f2725,f2725])).
% 38.78/5.23  fof(f8518,plain,(
% 38.78/5.23    ( ! [X43,X44] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X43,sK1))),X44) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X43),sK1),X44)))) ) | (~spl3_23 | ~spl3_177)),
% 38.78/5.23    inference(superposition,[],[f206,f7313])).
% 38.78/5.23  fof(f7313,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK1,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1))) ) | ~spl3_177),
% 38.78/5.23    inference(avatar_component_clause,[],[f7312])).
% 38.78/5.23  fof(f60151,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k5_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),sK1),k4_xboole_0(X0,sK2)))) ) | (~spl3_337 | ~spl3_376)),
% 38.78/5.23    inference(superposition,[],[f48075,f60049])).
% 38.78/5.23  fof(f60049,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(X1,sK2) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,X1),sK1))) ) | ~spl3_376),
% 38.78/5.23    inference(avatar_component_clause,[],[f60048])).
% 38.78/5.23  fof(f60050,plain,(
% 38.78/5.23    spl3_376 | ~spl3_149 | ~spl3_375),
% 38.78/5.23    inference(avatar_split_clause,[],[f59780,f59745,f5770,f60048])).
% 38.78/5.23  fof(f5770,plain,(
% 38.78/5.23    spl3_149 <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),sK1)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).
% 38.78/5.23  fof(f59780,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(X1,sK2) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,X1),sK1))) ) | (~spl3_149 | ~spl3_375)),
% 38.78/5.23    inference(superposition,[],[f59746,f5771])).
% 38.78/5.23  fof(f5771,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),sK1)) ) | ~spl3_149),
% 38.78/5.23    inference(avatar_component_clause,[],[f5770])).
% 38.78/5.23  fof(f59747,plain,(
% 38.78/5.23    spl3_375 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_49 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_153 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_190 | ~spl3_191 | ~spl3_198 | ~spl3_207 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_232 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348),
% 38.78/5.23    inference(avatar_split_clause,[],[f59388,f57538,f35496,f28193,f23461,f20432,f17963,f15045,f14837,f14382,f12888,f9828,f9800,f9796,f7263,f5950,f5946,f5930,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f2045,f1771,f1718,f1667,f1663,f1231,f953,f949,f945,f807,f697,f693,f681,f584,f579,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f59745])).
% 38.78/5.23  fof(f579,plain,(
% 38.78/5.23    spl3_49 <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 38.78/5.23  fof(f1771,plain,(
% 38.78/5.23    spl3_91 <=> ! [X1,X2] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X1),X2))) = k4_xboole_0(k4_xboole_0(sK2,X1),X2)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 38.78/5.23  fof(f4923,plain,(
% 38.78/5.23    spl3_143 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_143])])).
% 38.78/5.23  fof(f5930,plain,(
% 38.78/5.23    spl3_153 <=> ! [X16] : k4_xboole_0(sK2,X16) = k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).
% 38.78/5.23  fof(f5946,plain,(
% 38.78/5.23    spl3_157 <=> ! [X7] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X7)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).
% 38.78/5.23  fof(f7263,plain,(
% 38.78/5.23    spl3_165 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).
% 38.78/5.23  fof(f9796,plain,(
% 38.78/5.23    spl3_190 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_190])])).
% 38.78/5.23  fof(f9800,plain,(
% 38.78/5.23    spl3_191 <=> ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,sK1),X2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_191])])).
% 38.78/5.23  fof(f9828,plain,(
% 38.78/5.23    spl3_198 <=> ! [X13] : k4_xboole_0(k4_xboole_0(sK1,X13),sK1) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_198])])).
% 38.78/5.23  fof(f12888,plain,(
% 38.78/5.23    spl3_207 <=> ! [X36] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X36)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X36,k4_xboole_0(X36,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_207])])).
% 38.78/5.23  fof(f14382,plain,(
% 38.78/5.23    spl3_212 <=> ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_212])])).
% 38.78/5.23  fof(f14837,plain,(
% 38.78/5.23    spl3_215 <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_215])])).
% 38.78/5.23  fof(f15045,plain,(
% 38.78/5.23    spl3_217 <=> ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),X7)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_217])])).
% 38.78/5.23  fof(f17963,plain,(
% 38.78/5.23    spl3_232 <=> ! [X8] : k4_xboole_0(X8,sK2) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_232])])).
% 38.78/5.23  fof(f20432,plain,(
% 38.78/5.23    spl3_249 <=> ! [X14] : k4_xboole_0(k4_xboole_0(sK1,sK1),X14) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_249])])).
% 38.78/5.23  fof(f23461,plain,(
% 38.78/5.23    spl3_264 <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X1,k4_xboole_0(sK1,X1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_264])])).
% 38.78/5.23  fof(f28193,plain,(
% 38.78/5.23    spl3_269 <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_269])])).
% 38.78/5.23  fof(f57538,plain,(
% 38.78/5.23    spl3_348 <=> ! [X2] : k4_xboole_0(sK1,k4_xboole_0(X2,sK2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X2,sK2),sK2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_348])])).
% 38.78/5.23  fof(f59388,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X8))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_49 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_153 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_190 | ~spl3_191 | ~spl3_198 | ~spl3_207 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_232 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(backward_demodulation,[],[f18164,f59385])).
% 38.78/5.23  fof(f59385,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X93) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_49 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_190 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59384,f9797])).
% 38.78/5.23  fof(f9797,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) ) | ~spl3_190),
% 38.78/5.23    inference(avatar_component_clause,[],[f9796])).
% 38.78/5.23  fof(f59384,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_49 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59383,f808])).
% 38.78/5.23  fof(f59383,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_49 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59382,f581])).
% 38.78/5.23  fof(f581,plain,(
% 38.78/5.23    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | ~spl3_49),
% 38.78/5.23    inference(avatar_component_clause,[],[f579])).
% 38.78/5.23  fof(f59382,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59381,f30370])).
% 38.78/5.23  fof(f30370,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_264 | ~spl3_269)),
% 38.78/5.23    inference(forward_demodulation,[],[f30369,f64])).
% 38.78/5.23  fof(f30369,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(sK1,sK1))))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_264 | ~spl3_269)),
% 38.78/5.23    inference(forward_demodulation,[],[f30368,f206])).
% 38.78/5.23  fof(f30368,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_264 | ~spl3_269)),
% 38.78/5.23    inference(forward_demodulation,[],[f30367,f23462])).
% 38.78/5.23  fof(f23462,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X1,k4_xboole_0(sK1,X1))) ) | ~spl3_264),
% 38.78/5.23    inference(avatar_component_clause,[],[f23461])).
% 38.78/5.23  fof(f30367,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(sK1,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_269)),
% 38.78/5.23    inference(forward_demodulation,[],[f30366,f4456])).
% 38.78/5.23  fof(f30366,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X7,X8)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_269)),
% 38.78/5.23    inference(forward_demodulation,[],[f30194,f14677])).
% 38.78/5.23  fof(f14677,plain,(
% 38.78/5.23    ( ! [X14,X15] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X14,X15))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212)),
% 38.78/5.23    inference(backward_demodulation,[],[f12021,f14622])).
% 38.78/5.23  fof(f14622,plain,(
% 38.78/5.23    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X7)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X6)))),sK1)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_212)),
% 38.78/5.23    inference(backward_demodulation,[],[f6649,f14610])).
% 38.78/5.23  fof(f14610,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_212)),
% 38.78/5.23    inference(forward_demodulation,[],[f14591,f5128])).
% 38.78/5.23  fof(f14591,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X11),X12) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_212)),
% 38.78/5.23    inference(backward_demodulation,[],[f10639,f14584])).
% 38.78/5.23  fof(f14584,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X6) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_191 | ~spl3_212)),
% 38.78/5.23    inference(backward_demodulation,[],[f10632,f14583])).
% 38.78/5.23  fof(f14583,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8))) ) | (~spl3_36 | ~spl3_113 | ~spl3_143 | ~spl3_212)),
% 38.78/5.23    inference(forward_demodulation,[],[f14582,f4924])).
% 38.78/5.23  fof(f4924,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)) ) | ~spl3_143),
% 38.78/5.23    inference(avatar_component_clause,[],[f4923])).
% 38.78/5.23  fof(f14582,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK2,X8),sK2) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8))) ) | (~spl3_36 | ~spl3_113 | ~spl3_212)),
% 38.78/5.23    inference(forward_demodulation,[],[f14555,f385])).
% 38.78/5.23  fof(f14555,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X8))),sK2)) ) | (~spl3_113 | ~spl3_212)),
% 38.78/5.23    inference(superposition,[],[f2729,f14383])).
% 38.78/5.23  fof(f14383,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))) ) | ~spl3_212),
% 38.78/5.23    inference(avatar_component_clause,[],[f14382])).
% 38.78/5.23  fof(f10632,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,X6))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_191)),
% 38.78/5.23    inference(forward_demodulation,[],[f10631,f5128])).
% 38.78/5.23  fof(f10631,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X6),X6)) ) | (~spl3_23 | ~spl3_50 | ~spl3_91 | ~spl3_113 | ~spl3_191)),
% 38.78/5.23    inference(forward_demodulation,[],[f10630,f586])).
% 38.78/5.23  fof(f10630,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK1),X6),X6)) ) | (~spl3_23 | ~spl3_91 | ~spl3_113 | ~spl3_191)),
% 38.78/5.23    inference(forward_demodulation,[],[f10629,f1772])).
% 38.78/5.23  fof(f1772,plain,(
% 38.78/5.23    ( ! [X2,X1] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X1),X2))) = k4_xboole_0(k4_xboole_0(sK2,X1),X2)) ) | ~spl3_91),
% 38.78/5.23    inference(avatar_component_clause,[],[f1771])).
% 38.78/5.23  fof(f10629,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X6))),X6)) ) | (~spl3_23 | ~spl3_113 | ~spl3_191)),
% 38.78/5.23    inference(forward_demodulation,[],[f10628,f206])).
% 38.78/5.23  fof(f10628,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),X6),X6)) ) | (~spl3_113 | ~spl3_191)),
% 38.78/5.23    inference(forward_demodulation,[],[f10542,f2729])).
% 38.78/5.23  fof(f10542,plain,(
% 38.78/5.23    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X6))),X6)) ) | (~spl3_113 | ~spl3_191)),
% 38.78/5.23    inference(superposition,[],[f2729,f9801])).
% 38.78/5.23  fof(f9801,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,sK1),X2))) ) | ~spl3_191),
% 38.78/5.23    inference(avatar_component_clause,[],[f9800])).
% 38.78/5.23  fof(f10639,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,X11)),X12)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_165 | ~spl3_191)),
% 38.78/5.23    inference(backward_demodulation,[],[f7410,f10632])).
% 38.78/5.23  fof(f7410,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,k4_xboole_0(X11,X12)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_165)),
% 38.78/5.23    inference(backward_demodulation,[],[f5137,f7409])).
% 38.78/5.23  fof(f7409,plain,(
% 38.78/5.23    ( ! [X21,X22] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_158 | ~spl3_165)),
% 38.78/5.23    inference(forward_demodulation,[],[f7408,f5951])).
% 38.78/5.23  fof(f7408,plain,(
% 38.78/5.23    ( ! [X21,X22] : (k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X21,X22),sK1)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_165)),
% 38.78/5.23    inference(forward_demodulation,[],[f7407,f5372])).
% 38.78/5.23  fof(f7407,plain,(
% 38.78/5.23    ( ! [X21,X22] : (k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X21,X22)))) ) | (~spl3_23 | ~spl3_113 | ~spl3_165)),
% 38.78/5.23    inference(forward_demodulation,[],[f7358,f206])).
% 38.78/5.23  fof(f7358,plain,(
% 38.78/5.23    ( ! [X21,X22] : (k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK2,X21),k4_xboole_0(k4_xboole_0(sK1,sK1),X22))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X21)),X22)) ) | (~spl3_113 | ~spl3_165)),
% 38.78/5.23    inference(superposition,[],[f2729,f7264])).
% 38.78/5.23  fof(f7264,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))) ) | ~spl3_165),
% 38.78/5.23    inference(avatar_component_clause,[],[f7263])).
% 38.78/5.23  fof(f5137,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12) = k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,X12))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145)),
% 38.78/5.23    inference(backward_demodulation,[],[f4797,f5128])).
% 38.78/5.23  fof(f4797,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12) = k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X11),X12)))) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_87 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.23    inference(backward_demodulation,[],[f1697,f4791])).
% 38.78/5.23  fof(f1697,plain,(
% 38.78/5.23    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),sK1),X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(sK2,X11)),X12)) ) | (~spl3_23 | ~spl3_87)),
% 38.78/5.23    inference(superposition,[],[f206,f1664])).
% 38.78/5.23  fof(f6649,plain,(
% 38.78/5.23    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X6)))),sK1)) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_157)),
% 38.78/5.23    inference(forward_demodulation,[],[f6648,f5454])).
% 38.78/5.23  fof(f5454,plain,(
% 38.78/5.23    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10))))))) ) | (~spl3_8 | ~spl3_23 | ~spl3_113)),
% 38.78/5.23    inference(forward_demodulation,[],[f5231,f206])).
% 38.78/5.23  fof(f5231,plain,(
% 38.78/5.23    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10))))) ) | (~spl3_8 | ~spl3_113)),
% 38.78/5.23    inference(superposition,[],[f2729,f68])).
% 38.78/5.23  fof(f6648,plain,(
% 38.78/5.23    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,sK1)))))),sK1)) ) | (~spl3_23 | ~spl3_113 | ~spl3_157)),
% 38.78/5.23    inference(forward_demodulation,[],[f6588,f206])).
% 38.78/5.23  fof(f6588,plain,(
% 38.78/5.23    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,sK1)))),sK1)) ) | (~spl3_113 | ~spl3_157)),
% 38.78/5.23    inference(superposition,[],[f5947,f2729])).
% 38.78/5.23  fof(f5947,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) ) | ~spl3_157),
% 38.78/5.23    inference(avatar_component_clause,[],[f5946])).
% 38.78/5.23  fof(f12021,plain,(
% 38.78/5.23    ( ! [X14,X15] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X15,k4_xboole_0(X15,X14)))),sK1)) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_198)),
% 38.78/5.23    inference(forward_demodulation,[],[f12020,f5454])).
% 38.78/5.23  fof(f12020,plain,(
% 38.78/5.23    ( ! [X14,X15] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X14,sK1)))))),sK1)) ) | (~spl3_23 | ~spl3_113 | ~spl3_198)),
% 38.78/5.23    inference(forward_demodulation,[],[f11910,f206])).
% 38.78/5.23  fof(f11910,plain,(
% 38.78/5.23    ( ! [X14,X15] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,X15))),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X14,sK1)))),sK1)) ) | (~spl3_113 | ~spl3_198)),
% 38.78/5.23    inference(superposition,[],[f9829,f2729])).
% 38.78/5.23  fof(f9829,plain,(
% 38.78/5.23    ( ! [X13] : (k4_xboole_0(k4_xboole_0(sK1,X13),sK1) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1)) ) | ~spl3_198),
% 38.78/5.23    inference(avatar_component_clause,[],[f9828])).
% 38.78/5.23  fof(f30194,plain,(
% 38.78/5.23    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X7,k4_xboole_0(X7,X8))),sK1))) ) | (~spl3_88 | ~spl3_269)),
% 38.78/5.23    inference(superposition,[],[f1668,f28194])).
% 38.78/5.23  fof(f28194,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK1))) ) | ~spl3_269),
% 38.78/5.23    inference(avatar_component_clause,[],[f28193])).
% 38.78/5.23  fof(f59381,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK1,sK1)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_66 | ~spl3_95 | ~spl3_103 | ~spl3_113 | ~spl3_215 | ~spl3_217 | ~spl3_249 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59380,f586])).
% 38.78/5.23  fof(f59380,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X93,sK2))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_66 | ~spl3_95 | ~spl3_103 | ~spl3_113 | ~spl3_215 | ~spl3_217 | ~spl3_249 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59379,f68])).
% 38.78/5.23  fof(f59379,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2))) ) | (~spl3_8 | ~spl3_23 | ~spl3_66 | ~spl3_95 | ~spl3_103 | ~spl3_113 | ~spl3_215 | ~spl3_217 | ~spl3_249 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59378,f15156])).
% 38.78/5.23  fof(f15156,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))) ) | (~spl3_8 | ~spl3_23 | ~spl3_66 | ~spl3_95 | ~spl3_103 | ~spl3_215 | ~spl3_217)),
% 38.78/5.23    inference(backward_demodulation,[],[f4121,f15155])).
% 38.78/5.23  fof(f15155,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,X9)))) ) | (~spl3_8 | ~spl3_215 | ~spl3_217)),
% 38.78/5.23    inference(forward_demodulation,[],[f15092,f14838])).
% 38.78/5.23  fof(f14838,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK2,X8),k4_xboole_0(sK2,X8))) ) | ~spl3_215),
% 38.78/5.23    inference(avatar_component_clause,[],[f14837])).
% 38.78/5.23  fof(f15092,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK2,X9),k4_xboole_0(sK2,X9)) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,X9)))) ) | (~spl3_8 | ~spl3_217)),
% 38.78/5.23    inference(superposition,[],[f68,f15046])).
% 38.78/5.23  fof(f15046,plain,(
% 38.78/5.23    ( ! [X7] : (k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),X7)) ) | ~spl3_217),
% 38.78/5.23    inference(avatar_component_clause,[],[f15045])).
% 38.78/5.23  fof(f4121,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,X9))))) ) | (~spl3_23 | ~spl3_66 | ~spl3_95 | ~spl3_103)),
% 38.78/5.23    inference(forward_demodulation,[],[f4120,f954])).
% 38.78/5.23  fof(f4120,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(X9,k4_xboole_0(X9,sK2))))))) ) | (~spl3_23 | ~spl3_95 | ~spl3_103)),
% 38.78/5.23    inference(forward_demodulation,[],[f4034,f206])).
% 38.78/5.23  fof(f4034,plain,(
% 38.78/5.23    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k5_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,k4_xboole_0(X9,sK2))))) ) | (~spl3_95 | ~spl3_103)),
% 38.78/5.23    inference(superposition,[],[f2078,f2046])).
% 38.78/5.23  fof(f59378,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X93,sK2)))) ) | (~spl3_23 | ~spl3_113 | ~spl3_249 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59377,f20433])).
% 38.78/5.23  fof(f20433,plain,(
% 38.78/5.23    ( ! [X14] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X14) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14)))) ) | ~spl3_249),
% 38.78/5.23    inference(avatar_component_clause,[],[f20432])).
% 38.78/5.23  fof(f59377,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(X93,sK2)))))) ) | (~spl3_23 | ~spl3_113 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59376,f206])).
% 38.78/5.23  fof(f59376,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X93,sK2))),k4_xboole_0(X93,sK2)))) ) | (~spl3_113 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(forward_demodulation,[],[f59230,f2729])).
% 38.78/5.23  fof(f59230,plain,(
% 38.78/5.23    ( ! [X93] : (k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),sK2)),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(k4_xboole_0(X93,sK2),k4_xboole_0(sK1,k4_xboole_0(X93,sK2)))))) ) | (~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(superposition,[],[f35497,f57539])).
% 38.78/5.23  fof(f57539,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK1,k4_xboole_0(X2,sK2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X2,sK2),sK2))) ) | ~spl3_348),
% 38.78/5.23    inference(avatar_component_clause,[],[f57538])).
% 38.78/5.23  fof(f18164,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(X8,sK2) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(X8,sK2)))) ) | (~spl3_23 | ~spl3_58 | ~spl3_64 | ~spl3_103 | ~spl3_153 | ~spl3_207 | ~spl3_232)),
% 38.78/5.23    inference(backward_demodulation,[],[f3990,f18159])).
% 38.78/5.23  fof(f18159,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))) ) | (~spl3_23 | ~spl3_58 | ~spl3_153 | ~spl3_207 | ~spl3_232)),
% 38.78/5.23    inference(forward_demodulation,[],[f18158,f13007])).
% 38.78/5.23  fof(f13007,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK2))))) ) | (~spl3_23 | ~spl3_58 | ~spl3_153 | ~spl3_207)),
% 38.78/5.23    inference(forward_demodulation,[],[f13006,f5931])).
% 38.78/5.23  fof(f5931,plain,(
% 38.78/5.23    ( ! [X16] : (k4_xboole_0(sK2,X16) = k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2))) ) | ~spl3_153),
% 38.78/5.23    inference(avatar_component_clause,[],[f5930])).
% 38.78/5.23  fof(f13006,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK2))))) ) | (~spl3_23 | ~spl3_58 | ~spl3_207)),
% 38.78/5.23    inference(forward_demodulation,[],[f12905,f206])).
% 38.78/5.23  fof(f12905,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),k4_xboole_0(sK1,sK2))) ) | (~spl3_58 | ~spl3_207)),
% 38.78/5.23    inference(superposition,[],[f12889,f694])).
% 38.78/5.23  fof(f12889,plain,(
% 38.78/5.23    ( ! [X36] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X36)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X36,k4_xboole_0(X36,sK2))) ) | ~spl3_207),
% 38.78/5.23    inference(avatar_component_clause,[],[f12888])).
% 38.78/5.23  fof(f18158,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))))) ) | (~spl3_23 | ~spl3_207 | ~spl3_232)),
% 38.78/5.23    inference(forward_demodulation,[],[f17983,f206])).
% 38.78/5.23  fof(f17983,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,sK2)))) ) | (~spl3_207 | ~spl3_232)),
% 38.78/5.23    inference(superposition,[],[f17964,f12889])).
% 38.78/5.23  fof(f17964,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(X8,sK2) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2)))) ) | ~spl3_232),
% 38.78/5.23    inference(avatar_component_clause,[],[f17963])).
% 38.78/5.23  fof(f3990,plain,(
% 38.78/5.23    ( ! [X8] : (k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK1,X8))) = k5_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(k4_xboole_0(X8,sK2),k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK1,X8)))))) ) | (~spl3_64 | ~spl3_103)),
% 38.78/5.23    inference(superposition,[],[f2078,f946])).
% 38.78/5.23  fof(f59430,plain,(
% 38.78/5.23    spl3_373 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_49 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_69 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_153 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_190 | ~spl3_191 | ~spl3_198 | ~spl3_207 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_232 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348),
% 38.78/5.23    inference(avatar_split_clause,[],[f59389,f57538,f35496,f28193,f23461,f20432,f17963,f15045,f14837,f14382,f12888,f9828,f9800,f9796,f7263,f5950,f5946,f5930,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f2045,f1771,f1718,f1667,f1663,f1231,f1139,f953,f949,f945,f807,f697,f693,f681,f584,f579,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f59428])).
% 38.78/5.23  fof(f59389,plain,(
% 38.78/5.23    ( ! [X4] : (k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),sK2)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_49 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_66 | ~spl3_69 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_95 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_153 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_190 | ~spl3_191 | ~spl3_198 | ~spl3_207 | ~spl3_212 | ~spl3_215 | ~spl3_217 | ~spl3_232 | ~spl3_249 | ~spl3_264 | ~spl3_269 | ~spl3_285 | ~spl3_348)),
% 38.78/5.23    inference(backward_demodulation,[],[f10213,f59388])).
% 38.78/5.23  fof(f10213,plain,(
% 38.78/5.23    ( ! [X4] : (k4_xboole_0(k4_xboole_0(X4,sK2),sK2) = k5_xboole_0(k4_xboole_0(X4,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) ) | (~spl3_69 | ~spl3_190)),
% 38.78/5.23    inference(superposition,[],[f1140,f9797])).
% 38.78/5.23  fof(f57845,plain,(
% 38.78/5.23    spl3_370 | ~spl3_23 | ~spl3_113),
% 38.78/5.23    inference(avatar_split_clause,[],[f5228,f2728,f205,f57843])).
% 38.78/5.23  fof(f5228,plain,(
% 38.78/5.23    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5)))) ) | (~spl3_23 | ~spl3_113)),
% 38.78/5.23    inference(superposition,[],[f2729,f206])).
% 38.78/5.23  fof(f57548,plain,(
% 38.78/5.23    spl3_350 | ~spl3_6 | ~spl3_67),
% 38.78/5.23    inference(avatar_split_clause,[],[f1355,f1025,f59,f57546])).
% 38.78/5.23  fof(f59,plain,(
% 38.78/5.23    spl3_6 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 38.78/5.23  fof(f1355,plain,(
% 38.78/5.23    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)) ) | (~spl3_6 | ~spl3_67)),
% 38.78/5.23    inference(superposition,[],[f60,f1026])).
% 38.78/5.23  fof(f60,plain,(
% 38.78/5.23    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl3_6),
% 38.78/5.23    inference(avatar_component_clause,[],[f59])).
% 38.78/5.23  fof(f57540,plain,(
% 38.78/5.23    spl3_348 | ~spl3_205 | ~spl3_303),
% 38.78/5.23    inference(avatar_split_clause,[],[f40543,f40536,f12480,f57538])).
% 38.78/5.23  fof(f12480,plain,(
% 38.78/5.23    spl3_205 <=> ! [X1] : k4_xboole_0(k4_xboole_0(X1,sK2),sK2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_205])])).
% 38.78/5.23  fof(f40543,plain,(
% 38.78/5.23    ( ! [X2] : (k4_xboole_0(sK1,k4_xboole_0(X2,sK2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X2,sK2),sK2))) ) | (~spl3_205 | ~spl3_303)),
% 38.78/5.23    inference(superposition,[],[f40537,f12481])).
% 38.78/5.23  fof(f12481,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,sK2),sK2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1))) ) | ~spl3_205),
% 38.78/5.23    inference(avatar_component_clause,[],[f12480])).
% 38.78/5.23  fof(f48076,plain,(
% 38.78/5.23    spl3_337 | ~spl3_67 | ~spl3_162),
% 38.78/5.23    inference(avatar_split_clause,[],[f11575,f5966,f1025,f48074])).
% 38.78/5.23  fof(f5966,plain,(
% 38.78/5.23    spl3_162 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_162])])).
% 38.78/5.23  fof(f11575,plain,(
% 38.78/5.23    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X1,X0)))) ) | (~spl3_67 | ~spl3_162)),
% 38.78/5.23    inference(superposition,[],[f5967,f1026])).
% 38.78/5.23  fof(f5967,plain,(
% 38.78/5.23    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2))))) ) | ~spl3_162),
% 38.78/5.23    inference(avatar_component_clause,[],[f5966])).
% 38.78/5.23  fof(f46547,plain,(
% 38.78/5.23    spl3_336 | ~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_189 | ~spl3_271 | ~spl3_284 | ~spl3_310),
% 38.78/5.23    inference(avatar_split_clause,[],[f46218,f42803,f35246,f28952,f9792,f4459,f4455,f4451,f4268,f3544,f2740,f2085,f2049,f1718,f1663,f1231,f1025,f945,f697,f584,f205,f67,f63,f46545])).
% 38.78/5.23  fof(f28952,plain,(
% 38.78/5.23    spl3_271 <=> ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_271])])).
% 38.78/5.23  fof(f35246,plain,(
% 38.78/5.23    spl3_284 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(X1,sK1),X1)),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_284])])).
% 38.78/5.23  fof(f46218,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_189 | ~spl3_271 | ~spl3_284 | ~spl3_310)),
% 38.78/5.23    inference(backward_demodulation,[],[f35428,f46193])).
% 38.78/5.23  fof(f35428,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)) ) | (~spl3_189 | ~spl3_271 | ~spl3_284)),
% 38.78/5.23    inference(forward_demodulation,[],[f35314,f28953])).
% 38.78/5.23  fof(f28953,plain,(
% 38.78/5.23    ( ! [X11] : (k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) ) | ~spl3_271),
% 38.78/5.23    inference(avatar_component_clause,[],[f28952])).
% 38.78/5.23  fof(f35314,plain,(
% 38.78/5.23    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK1),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0)) ) | (~spl3_189 | ~spl3_284)),
% 38.78/5.23    inference(superposition,[],[f9793,f35247])).
% 38.78/5.23  fof(f35247,plain,(
% 38.78/5.23    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(X1,sK1),X1)) ) | ~spl3_284),
% 38.78/5.23    inference(avatar_component_clause,[],[f35246])).
% 38.78/5.23  fof(f42805,plain,(
% 38.78/5.23    spl3_310 | ~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_137 | ~spl3_158 | ~spl3_238),
% 38.78/5.23    inference(avatar_split_clause,[],[f19301,f19203,f5950,f4268,f2728,f205,f67,f42803])).
% 38.78/5.23  fof(f41937,plain,(
% 38.78/5.23    spl3_307 | ~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_223),
% 38.78/5.23    inference(avatar_split_clause,[],[f26001,f15989,f2728,f205,f67,f41935])).
% 38.78/5.23  fof(f15989,plain,(
% 38.78/5.23    spl3_223 <=> ! [X1,X0,X2] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 38.78/5.23    introduced(avatar_definition,[new_symbols(naming,[spl3_223])])).
% 38.78/5.23  fof(f26001,plain,(
% 38.78/5.23    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X8,X9))))) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_223)),
% 38.78/5.23    inference(backward_demodulation,[],[f359,f26000])).
% 38.78/5.23  fof(f26000,plain,(
% 38.78/5.23    ( ! [X12,X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10)))))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X11,X12))))) ) | (~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_223)),
% 38.78/5.23    inference(forward_demodulation,[],[f25999,f5372])).
% 38.78/5.23  fof(f25999,plain,(
% 38.78/5.23    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X10)) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10))))))) ) | (~spl3_8 | ~spl3_23 | ~spl3_223)),
% 38.78/5.23    inference(forward_demodulation,[],[f25418,f206])).
% 38.78/5.23  fof(f25418,plain,(
% 38.78/5.23    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X10)) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10))))) ) | (~spl3_8 | ~spl3_223)),
% 38.78/5.23    inference(superposition,[],[f15990,f68])).
% 38.78/5.23  fof(f15990,plain,(
% 38.78/5.23    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) ) | ~spl3_223),
% 38.78/5.23    inference(avatar_component_clause,[],[f15989])).
% 38.78/5.23  fof(f359,plain,(
% 38.78/5.23    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X10,X11)))))))) ) | ~spl3_23),
% 38.78/5.23    inference(forward_demodulation,[],[f358,f206])).
% 38.78/5.23  fof(f358,plain,(
% 38.78/5.23    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11)))))) ) | ~spl3_23),
% 38.78/5.23    inference(forward_demodulation,[],[f357,f206])).
% 38.78/5.23  fof(f357,plain,(
% 38.78/5.23    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11)))) ) | ~spl3_23),
% 38.78/5.23    inference(forward_demodulation,[],[f356,f206])).
% 38.78/5.24  fof(f356,plain,(
% 38.78/5.24    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))),X11)) ) | ~spl3_23),
% 38.78/5.24    inference(forward_demodulation,[],[f342,f206])).
% 38.78/5.24  fof(f342,plain,(
% 38.78/5.24    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))),X11)) ) | ~spl3_23),
% 38.78/5.24    inference(superposition,[],[f206,f206])).
% 38.78/5.24  fof(f40538,plain,(
% 38.78/5.24    spl3_303 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_264 | ~spl3_269 | ~spl3_290 | ~spl3_296),
% 38.78/5.24    inference(avatar_split_clause,[],[f40532,f36570,f36546,f28193,f23461,f14382,f9828,f9800,f7263,f5950,f5946,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1771,f1718,f1667,f1663,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f40536])).
% 38.78/5.24  fof(f36546,plain,(
% 38.78/5.24    spl3_290 <=> ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,sK1),X1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_290])])).
% 38.78/5.24  fof(f36570,plain,(
% 38.78/5.24    spl3_296 <=> ! [X13] : k4_xboole_0(sK1,X13) = k5_xboole_0(k4_xboole_0(sK1,X13),k4_xboole_0(k4_xboole_0(X13,sK1),X13))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_296])])).
% 38.78/5.24  fof(f40532,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_264 | ~spl3_269 | ~spl3_290 | ~spl3_296)),
% 38.78/5.24    inference(forward_demodulation,[],[f40531,f64])).
% 38.78/5.24  fof(f40531,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))) = k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_264 | ~spl3_269 | ~spl3_290 | ~spl3_296)),
% 38.78/5.24    inference(forward_demodulation,[],[f40530,f30370])).
% 38.78/5.24  fof(f40530,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))) = k4_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,sK1))) ) | (~spl3_88 | ~spl3_290 | ~spl3_296)),
% 38.78/5.24    inference(forward_demodulation,[],[f40373,f36547])).
% 38.78/5.24  fof(f36547,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,sK1),X1))) ) | ~spl3_290),
% 38.78/5.24    inference(avatar_component_clause,[],[f36546])).
% 38.78/5.24  fof(f40373,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))) = k5_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),sK1),k4_xboole_0(sK1,X1)))) ) | (~spl3_88 | ~spl3_296)),
% 38.78/5.24    inference(superposition,[],[f1668,f36571])).
% 38.78/5.24  fof(f36571,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(sK1,X13) = k5_xboole_0(k4_xboole_0(sK1,X13),k4_xboole_0(k4_xboole_0(X13,sK1),X13))) ) | ~spl3_296),
% 38.78/5.24    inference(avatar_component_clause,[],[f36570])).
% 38.78/5.24  fof(f36588,plain,(
% 38.78/5.24    spl3_300 | ~spl3_112 | ~spl3_166 | ~spl3_173 | ~spl3_253 | ~spl3_283 | ~spl3_284),
% 38.78/5.24    inference(avatar_split_clause,[],[f35388,f35246,f34678,f20834,f7296,f7267,f2724,f36586])).
% 38.78/5.24  fof(f7296,plain,(
% 38.78/5.24    spl3_173 <=> ! [X4] : k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_173])])).
% 38.78/5.24  fof(f20834,plain,(
% 38.78/5.24    spl3_253 <=> ! [X7] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) = k4_xboole_0(sK1,k4_xboole_0(X7,X7))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_253])])).
% 38.78/5.24  fof(f34678,plain,(
% 38.78/5.24    spl3_283 <=> ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_283])])).
% 38.78/5.24  fof(f35388,plain,(
% 38.78/5.24    ( ! [X17] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X17,sK1))) = k4_xboole_0(k4_xboole_0(X17,sK1),X17)) ) | (~spl3_112 | ~spl3_166 | ~spl3_173 | ~spl3_253 | ~spl3_283 | ~spl3_284)),
% 38.78/5.24    inference(forward_demodulation,[],[f35294,f35213])).
% 38.78/5.24  fof(f35213,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(sK1,k4_xboole_0(X11,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X11,sK1),X11))) ) | (~spl3_166 | ~spl3_173 | ~spl3_253 | ~spl3_283)),
% 38.78/5.24    inference(forward_demodulation,[],[f35212,f7297])).
% 38.78/5.24  fof(f7297,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) ) | ~spl3_173),
% 38.78/5.24    inference(avatar_component_clause,[],[f7296])).
% 38.78/5.24  fof(f35212,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X11)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X11,sK1),X11))) ) | (~spl3_166 | ~spl3_253 | ~spl3_283)),
% 38.78/5.24    inference(forward_demodulation,[],[f35134,f7268])).
% 38.78/5.24  fof(f35134,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X11,sK1))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X11,sK1),X11))) ) | (~spl3_253 | ~spl3_283)),
% 38.78/5.24    inference(superposition,[],[f20835,f34679])).
% 38.78/5.24  fof(f34679,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)) ) | ~spl3_283),
% 38.78/5.24    inference(avatar_component_clause,[],[f34678])).
% 38.78/5.24  fof(f20835,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) = k4_xboole_0(sK1,k4_xboole_0(X7,X7))) ) | ~spl3_253),
% 38.78/5.24    inference(avatar_component_clause,[],[f20834])).
% 38.78/5.24  fof(f35294,plain,(
% 38.78/5.24    ( ! [X17] : (k4_xboole_0(k4_xboole_0(X17,sK1),X17) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X17,sK1),X17)))) ) | (~spl3_112 | ~spl3_284)),
% 38.78/5.24    inference(superposition,[],[f2725,f35247])).
% 38.78/5.24  fof(f36572,plain,(
% 38.78/5.24    spl3_296 | ~spl3_244 | ~spl3_284),
% 38.78/5.24    inference(avatar_split_clause,[],[f35290,f35246,f19505,f36570])).
% 38.78/5.24  fof(f35290,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(sK1,X13) = k5_xboole_0(k4_xboole_0(sK1,X13),k4_xboole_0(k4_xboole_0(X13,sK1),X13))) ) | (~spl3_244 | ~spl3_284)),
% 38.78/5.24    inference(superposition,[],[f19506,f35247])).
% 38.78/5.24  fof(f36548,plain,(
% 38.78/5.24    spl3_290 | ~spl3_140 | ~spl3_284),
% 38.78/5.24    inference(avatar_split_clause,[],[f35278,f35246,f4455,f36546])).
% 38.78/5.24  fof(f35278,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,sK1),X1))) ) | (~spl3_140 | ~spl3_284)),
% 38.78/5.24    inference(superposition,[],[f4456,f35247])).
% 38.78/5.24  fof(f35498,plain,(
% 38.78/5.24    spl3_285 | ~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_223),
% 38.78/5.24    inference(avatar_split_clause,[],[f26002,f15989,f2728,f205,f67,f63,f35496])).
% 38.78/5.24  fof(f26002,plain,(
% 38.78/5.24    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7)))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_113 | ~spl3_223)),
% 38.78/5.24    inference(backward_demodulation,[],[f366,f26000])).
% 38.78/5.24  fof(f366,plain,(
% 38.78/5.24    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8)))))))) ) | (~spl3_7 | ~spl3_23)),
% 38.78/5.24    inference(forward_demodulation,[],[f352,f206])).
% 38.78/5.24  fof(f352,plain,(
% 38.78/5.24    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8)))))) ) | (~spl3_7 | ~spl3_23)),
% 38.78/5.24    inference(superposition,[],[f64,f206])).
% 38.78/5.24  fof(f35248,plain,(
% 38.78/5.24    spl3_284 | ~spl3_280 | ~spl3_283),
% 38.78/5.24    inference(avatar_split_clause,[],[f35093,f34678,f34666,f35246])).
% 38.78/5.24  fof(f34666,plain,(
% 38.78/5.24    spl3_280 <=> ! [X57] : k4_xboole_0(k4_xboole_0(sK1,sK1),X57) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_280])])).
% 38.78/5.24  fof(f35093,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(X1,sK1),X1)) ) | (~spl3_280 | ~spl3_283)),
% 38.78/5.24    inference(superposition,[],[f34679,f34667])).
% 38.78/5.24  fof(f34667,plain,(
% 38.78/5.24    ( ! [X57] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X57) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1))) ) | ~spl3_280),
% 38.78/5.24    inference(avatar_component_clause,[],[f34666])).
% 38.78/5.24  fof(f34680,plain,(
% 38.78/5.24    spl3_283 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_163 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_237 | ~spl3_264 | ~spl3_269 | ~spl3_272),
% 38.78/5.24    inference(avatar_split_clause,[],[f32860,f29424,f28193,f23461,f18989,f18339,f14382,f9828,f9800,f8725,f7263,f6833,f5950,f5946,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1771,f1718,f1667,f1663,f1231,f1025,f949,f945,f811,f807,f697,f681,f584,f555,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f34678])).
% 38.78/5.24  fof(f555,plain,(
% 38.78/5.24    spl3_47 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 38.78/5.24  fof(f811,plain,(
% 38.78/5.24    spl3_62 <=> ! [X2] : k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 38.78/5.24  fof(f6833,plain,(
% 38.78/5.24    spl3_163 <=> ! [X29] : k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k4_xboole_0(k4_xboole_0(X29,sK1),sK1)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).
% 38.78/5.24  fof(f8725,plain,(
% 38.78/5.24    spl3_179 <=> ! [X4] : k4_xboole_0(k4_xboole_0(X4,sK1),sK1) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).
% 38.78/5.24  fof(f18339,plain,(
% 38.78/5.24    spl3_233 <=> ! [X1,X0,X2] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_233])])).
% 38.78/5.24  fof(f18989,plain,(
% 38.78/5.24    spl3_237 <=> ! [X7] : k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,sK2))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_237])])).
% 38.78/5.24  fof(f29424,plain,(
% 38.78/5.24    spl3_272 <=> ! [X11] : k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,sK1)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_272])])).
% 38.78/5.24  fof(f32860,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_163 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_237 | ~spl3_264 | ~spl3_269 | ~spl3_272)),
% 38.78/5.24    inference(forward_demodulation,[],[f32830,f29488])).
% 38.78/5.24  fof(f29488,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(X7,sK1),X7) = k5_xboole_0(k4_xboole_0(X7,sK1),k4_xboole_0(X7,sK1))) ) | (~spl3_67 | ~spl3_272)),
% 38.78/5.24    inference(superposition,[],[f1026,f29425])).
% 38.78/5.24  fof(f29425,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,sK1)))) ) | ~spl3_272),
% 38.78/5.24    inference(avatar_component_clause,[],[f29424])).
% 38.78/5.24  fof(f32830,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_163 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_237 | ~spl3_264 | ~spl3_269 | ~spl3_272)),
% 38.78/5.24    inference(backward_demodulation,[],[f18993,f32809])).
% 38.78/5.24  fof(f32809,plain,(
% 38.78/5.24    ( ! [X39] : (k4_xboole_0(X39,sK1) = k4_xboole_0(k4_xboole_0(X39,sK1),sK1)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_264 | ~spl3_269 | ~spl3_272)),
% 38.78/5.24    inference(backward_demodulation,[],[f6744,f32806])).
% 38.78/5.24  fof(f32806,plain,(
% 38.78/5.24    ( ! [X10] : (k4_xboole_0(X10,sK1) = k5_xboole_0(k4_xboole_0(X10,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X10))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_264 | ~spl3_269 | ~spl3_272)),
% 38.78/5.24    inference(backward_demodulation,[],[f29490,f32805])).
% 38.78/5.24  fof(f32805,plain,(
% 38.78/5.24    ( ! [X57] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X57) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_264 | ~spl3_269)),
% 38.78/5.24    inference(forward_demodulation,[],[f32804,f5951])).
% 38.78/5.24  fof(f32804,plain,(
% 38.78/5.24    ( ! [X57] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_264 | ~spl3_269)),
% 38.78/5.24    inference(forward_demodulation,[],[f32803,f557])).
% 38.78/5.24  fof(f557,plain,(
% 38.78/5.24    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | ~spl3_47),
% 38.78/5.24    inference(avatar_component_clause,[],[f555])).
% 38.78/5.24  fof(f32803,plain,(
% 38.78/5.24    ( ! [X57] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(X57,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_264 | ~spl3_269)),
% 38.78/5.24    inference(forward_demodulation,[],[f32802,f30370])).
% 38.78/5.24  fof(f32802,plain,(
% 38.78/5.24    ( ! [X57] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(sK1,sK1)))) ) | (~spl3_62 | ~spl3_179 | ~spl3_233 | ~spl3_264)),
% 38.78/5.24    inference(forward_demodulation,[],[f32801,f23462])).
% 38.78/5.24  fof(f32801,plain,(
% 38.78/5.24    ( ! [X57] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X57,sK1))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(sK1,k4_xboole_0(X57,sK1))))) ) | (~spl3_62 | ~spl3_179 | ~spl3_233)),
% 38.78/5.24    inference(forward_demodulation,[],[f30842,f812])).
% 38.78/5.24  fof(f812,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))) ) | ~spl3_62),
% 38.78/5.24    inference(avatar_component_clause,[],[f811])).
% 38.78/5.24  fof(f30842,plain,(
% 38.78/5.24    ( ! [X57] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X57,sK1),k4_xboole_0(k4_xboole_0(X57,sK1),sK1)))))) ) | (~spl3_179 | ~spl3_233)),
% 38.78/5.24    inference(superposition,[],[f18340,f8726])).
% 38.78/5.24  fof(f8726,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(k4_xboole_0(X4,sK1),sK1) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1))) ) | ~spl3_179),
% 38.78/5.24    inference(avatar_component_clause,[],[f8725])).
% 38.78/5.24  fof(f18340,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))) ) | ~spl3_233),
% 38.78/5.24    inference(avatar_component_clause,[],[f18339])).
% 38.78/5.24  fof(f29490,plain,(
% 38.78/5.24    ( ! [X10] : (k4_xboole_0(X10,sK1) = k5_xboole_0(k4_xboole_0(X10,sK1),k4_xboole_0(k4_xboole_0(X10,sK1),k4_xboole_0(X10,sK1)))) ) | (~spl3_103 | ~spl3_272)),
% 38.78/5.24    inference(superposition,[],[f2078,f29425])).
% 38.78/5.24  fof(f6744,plain,(
% 38.78/5.24    ( ! [X39] : (k4_xboole_0(k4_xboole_0(X39,sK1),sK1) = k5_xboole_0(k4_xboole_0(X39,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X39))) ) | (~spl3_67 | ~spl3_158)),
% 38.78/5.24    inference(superposition,[],[f1026,f5951])).
% 38.78/5.24  fof(f18993,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK1))) ) | (~spl3_163 | ~spl3_237)),
% 38.78/5.24    inference(superposition,[],[f18990,f6834])).
% 38.78/5.24  fof(f6834,plain,(
% 38.78/5.24    ( ! [X29] : (k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k4_xboole_0(k4_xboole_0(X29,sK1),sK1)) ) | ~spl3_163),
% 38.78/5.24    inference(avatar_component_clause,[],[f6833])).
% 38.78/5.24  fof(f18990,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,sK2))) ) | ~spl3_237),
% 38.78/5.24    inference(avatar_component_clause,[],[f18989])).
% 38.78/5.24  fof(f34668,plain,(
% 38.78/5.24    spl3_280 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_47 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_62 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_87 | ~spl3_88 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_157 | ~spl3_158 | ~spl3_165 | ~spl3_179 | ~spl3_191 | ~spl3_198 | ~spl3_212 | ~spl3_233 | ~spl3_264 | ~spl3_269),
% 38.78/5.24    inference(avatar_split_clause,[],[f32805,f28193,f23461,f18339,f14382,f9828,f9800,f8725,f7263,f5950,f5946,f5017,f4923,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1771,f1718,f1667,f1663,f1231,f949,f945,f811,f807,f697,f681,f584,f555,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f34666])).
% 38.78/5.24  fof(f29426,plain,(
% 38.78/5.24    spl3_272 | ~spl3_8 | ~spl3_271),
% 38.78/5.24    inference(avatar_split_clause,[],[f29000,f28952,f67,f29424])).
% 38.78/5.24  fof(f29000,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,sK1)))) ) | (~spl3_8 | ~spl3_271)),
% 38.78/5.24    inference(superposition,[],[f28953,f68])).
% 38.78/5.24  fof(f28954,plain,(
% 38.78/5.24    spl3_271 | ~spl3_23 | ~spl3_67 | ~spl3_145 | ~spl3_183 | ~spl3_268),
% 38.78/5.24    inference(avatar_split_clause,[],[f28800,f28189,f9125,f5017,f1025,f205,f28952])).
% 38.78/5.24  fof(f28189,plain,(
% 38.78/5.24    spl3_268 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),X1)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_268])])).
% 38.78/5.24  fof(f28800,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(X11,sK1) = k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) ) | (~spl3_23 | ~spl3_67 | ~spl3_145 | ~spl3_183 | ~spl3_268)),
% 38.78/5.24    inference(forward_demodulation,[],[f28799,f1026])).
% 38.78/5.24  fof(f28799,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11))) = k5_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) ) | (~spl3_23 | ~spl3_67 | ~spl3_145 | ~spl3_183 | ~spl3_268)),
% 38.78/5.24    inference(forward_demodulation,[],[f28798,f9393])).
% 38.78/5.24  fof(f9393,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(sK1,sK1),X2))))) ) | (~spl3_23 | ~spl3_145 | ~spl3_183)),
% 38.78/5.24    inference(forward_demodulation,[],[f9306,f5018])).
% 38.78/5.24  fof(f9306,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X2)))))) ) | (~spl3_23 | ~spl3_183)),
% 38.78/5.24    inference(superposition,[],[f9126,f206])).
% 38.78/5.24  fof(f28798,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11))) = k5_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(sK1,sK1),X11)))))) ) | (~spl3_23 | ~spl3_67 | ~spl3_268)),
% 38.78/5.24    inference(forward_demodulation,[],[f28635,f206])).
% 38.78/5.24  fof(f28635,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(X11,k4_xboole_0(sK1,k4_xboole_0(sK1,X11))) = k5_xboole_0(X11,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X11)),k4_xboole_0(k4_xboole_0(sK1,sK1),X11)))) ) | (~spl3_67 | ~spl3_268)),
% 38.78/5.24    inference(superposition,[],[f1026,f28190])).
% 38.78/5.24  fof(f28190,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),X1)) ) | ~spl3_268),
% 38.78/5.24    inference(avatar_component_clause,[],[f28189])).
% 38.78/5.24  fof(f28195,plain,(
% 38.78/5.24    spl3_269 | ~spl3_149 | ~spl3_260),
% 38.78/5.24    inference(avatar_split_clause,[],[f23221,f22207,f5770,f28193])).
% 38.78/5.24  fof(f22207,plain,(
% 38.78/5.24    spl3_260 <=> ! [X12] : k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,sK1),X12)) = k4_xboole_0(X12,k4_xboole_0(sK1,X12))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_260])])).
% 38.78/5.24  fof(f23221,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK1))) ) | (~spl3_149 | ~spl3_260)),
% 38.78/5.24    inference(superposition,[],[f22208,f5771])).
% 38.78/5.24  fof(f22208,plain,(
% 38.78/5.24    ( ! [X12] : (k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,sK1),X12)) = k4_xboole_0(X12,k4_xboole_0(sK1,X12))) ) | ~spl3_260),
% 38.78/5.24    inference(avatar_component_clause,[],[f22207])).
% 38.78/5.24  fof(f28191,plain,(
% 38.78/5.24    spl3_268 | ~spl3_113 | ~spl3_259),
% 38.78/5.24    inference(avatar_split_clause,[],[f22781,f22203,f2728,f28189])).
% 38.78/5.24  fof(f22203,plain,(
% 38.78/5.24    spl3_259 <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_259])])).
% 38.78/5.24  fof(f22781,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1)),X1)) ) | (~spl3_113 | ~spl3_259)),
% 38.78/5.24    inference(superposition,[],[f22204,f2729])).
% 38.78/5.24  fof(f22204,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8)))) ) | ~spl3_259),
% 38.78/5.24    inference(avatar_component_clause,[],[f22203])).
% 38.78/5.24  fof(f27686,plain,(
% 38.78/5.24    spl3_265 | ~spl3_138 | ~spl3_241),
% 38.78/5.24    inference(avatar_split_clause,[],[f25158,f19215,f4447,f27684])).
% 38.78/5.24  fof(f4447,plain,(
% 38.78/5.24    spl3_138 <=> ! [X0] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(sK2,k4_xboole_0(X0,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).
% 38.78/5.24  fof(f19215,plain,(
% 38.78/5.24    spl3_241 <=> ! [X1] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_241])])).
% 38.78/5.24  fof(f25158,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(X1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))) ) | (~spl3_138 | ~spl3_241)),
% 38.78/5.24    inference(superposition,[],[f19216,f4448])).
% 38.78/5.24  fof(f4448,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) = k4_xboole_0(sK2,k4_xboole_0(X0,sK1))) ) | ~spl3_138),
% 38.78/5.24    inference(avatar_component_clause,[],[f4447])).
% 38.78/5.24  fof(f19216,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))) ) | ~spl3_241),
% 38.78/5.24    inference(avatar_component_clause,[],[f19215])).
% 38.78/5.24  fof(f23463,plain,(
% 38.78/5.24    spl3_264 | ~spl3_140 | ~spl3_260),
% 38.78/5.24    inference(avatar_split_clause,[],[f23261,f22207,f4455,f23461])).
% 38.78/5.24  fof(f23261,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X1,k4_xboole_0(sK1,X1))) ) | (~spl3_140 | ~spl3_260)),
% 38.78/5.24    inference(superposition,[],[f22208,f4456])).
% 38.78/5.24  fof(f22209,plain,(
% 38.78/5.24    spl3_260 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238 | ~spl3_248),
% 38.78/5.24    inference(avatar_split_clause,[],[f20383,f20227,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f1025,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f22207])).
% 38.78/5.24  fof(f20383,plain,(
% 38.78/5.24    ( ! [X12] : (k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,sK1),X12)) = k4_xboole_0(X12,k4_xboole_0(sK1,X12))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_67 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238 | ~spl3_248)),
% 38.78/5.24    inference(forward_demodulation,[],[f20292,f19302])).
% 38.78/5.24  fof(f20292,plain,(
% 38.78/5.24    ( ! [X12] : (k4_xboole_0(X12,k4_xboole_0(sK1,X12)) = k5_xboole_0(X12,k4_xboole_0(k4_xboole_0(sK1,X12),k4_xboole_0(sK1,X12)))) ) | (~spl3_67 | ~spl3_248)),
% 38.78/5.24    inference(superposition,[],[f1026,f20228])).
% 38.78/5.24  fof(f22205,plain,(
% 38.78/5.24    spl3_259 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238 | ~spl3_248),
% 38.78/5.24    inference(avatar_split_clause,[],[f20377,f20227,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f22203])).
% 38.78/5.24  fof(f20377,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238 | ~spl3_248)),
% 38.78/5.24    inference(forward_demodulation,[],[f20289,f19302])).
% 38.78/5.24  fof(f20289,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK1,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK1,X8)))) ) | (~spl3_8 | ~spl3_248)),
% 38.78/5.24    inference(superposition,[],[f68,f20228])).
% 38.78/5.24  fof(f22193,plain,(
% 38.78/5.24    spl3_256 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238),
% 38.78/5.24    inference(avatar_split_clause,[],[f19302,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f22191])).
% 38.78/5.24  fof(f20836,plain,(
% 38.78/5.24    spl3_253 | ~spl3_58 | ~spl3_249),
% 38.78/5.24    inference(avatar_split_clause,[],[f20466,f20432,f693,f20834])).
% 38.78/5.24  fof(f20466,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) = k4_xboole_0(sK1,k4_xboole_0(X7,X7))) ) | (~spl3_58 | ~spl3_249)),
% 38.78/5.24    inference(superposition,[],[f694,f20433])).
% 38.78/5.24  fof(f20434,plain,(
% 38.78/5.24    spl3_249 | ~spl3_8 | ~spl3_23 | ~spl3_112 | ~spl3_113 | ~spl3_120 | ~spl3_137 | ~spl3_139 | ~spl3_142 | ~spl3_227 | ~spl3_243 | ~spl3_247),
% 38.78/5.24    inference(avatar_split_clause,[],[f19952,f19676,f19372,f16005,f4831,f4451,f4268,f3184,f2728,f2724,f205,f67,f20432])).
% 38.78/5.24  fof(f4831,plain,(
% 38.78/5.24    spl3_142 <=> ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_142])])).
% 38.78/5.24  fof(f16005,plain,(
% 38.78/5.24    spl3_227 <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_227])])).
% 38.78/5.24  fof(f19372,plain,(
% 38.78/5.24    spl3_243 <=> ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_243])])).
% 38.78/5.24  fof(f19676,plain,(
% 38.78/5.24    spl3_247 <=> ! [X23,X24] : k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),X23),X24)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_247])])).
% 38.78/5.24  fof(f19952,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X14) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_112 | ~spl3_113 | ~spl3_120 | ~spl3_137 | ~spl3_139 | ~spl3_142 | ~spl3_227 | ~spl3_243 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f19951,f17133])).
% 38.78/5.24  fof(f17133,plain,(
% 38.78/5.24    ( ! [X25] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X25) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X25),X25))) ) | (~spl3_120 | ~spl3_139 | ~spl3_142 | ~spl3_227)),
% 38.78/5.24    inference(forward_demodulation,[],[f17132,f4452])).
% 38.78/5.24  fof(f17132,plain,(
% 38.78/5.24    ( ! [X25] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X25,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X25),X25))) ) | (~spl3_120 | ~spl3_142 | ~spl3_227)),
% 38.78/5.24    inference(forward_demodulation,[],[f17058,f3185])).
% 38.78/5.24  fof(f17058,plain,(
% 38.78/5.24    ( ! [X25] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X25),X25)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X25)),sK1)) ) | (~spl3_142 | ~spl3_227)),
% 38.78/5.24    inference(superposition,[],[f4832,f16006])).
% 38.78/5.24  fof(f16006,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2))) ) | ~spl3_227),
% 38.78/5.24    inference(avatar_component_clause,[],[f16005])).
% 38.78/5.24  fof(f4832,plain,(
% 38.78/5.24    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6)) ) | ~spl3_142),
% 38.78/5.24    inference(avatar_component_clause,[],[f4831])).
% 38.78/5.24  fof(f19951,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X14,X14))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X14),X14))) ) | (~spl3_8 | ~spl3_23 | ~spl3_112 | ~spl3_113 | ~spl3_137 | ~spl3_243 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f19950,f5372])).
% 38.78/5.24  fof(f19950,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X14),X14)) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(sK1,X14),X14))) ) | (~spl3_112 | ~spl3_137 | ~spl3_243 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f19788,f19379])).
% 38.78/5.24  fof(f19379,plain,(
% 38.78/5.24    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(sK1,X4),X5) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X4),X5),k4_xboole_0(sK1,sK1))) ) | (~spl3_112 | ~spl3_243)),
% 38.78/5.24    inference(superposition,[],[f19373,f2725])).
% 38.78/5.24  fof(f19373,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1))) ) | ~spl3_243),
% 38.78/5.24    inference(avatar_component_clause,[],[f19372])).
% 38.78/5.24  fof(f19788,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X14),X14)) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X14),X14),k4_xboole_0(sK1,sK1)))) ) | (~spl3_137 | ~spl3_247)),
% 38.78/5.24    inference(superposition,[],[f19677,f4269])).
% 38.78/5.24  fof(f19677,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),X23),X24)) ) | ~spl3_247),
% 38.78/5.24    inference(avatar_component_clause,[],[f19676])).
% 38.78/5.24  fof(f20229,plain,(
% 38.78/5.24    spl3_248 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_33 | ~spl3_34 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_147 | ~spl3_183 | ~spl3_238 | ~spl3_247),
% 38.78/5.24    inference(avatar_split_clause,[],[f20095,f19676,f19203,f9125,f5632,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f335,f331,f205,f100,f93,f88,f67,f63,f20227])).
% 38.78/5.24  fof(f331,plain,(
% 38.78/5.24    spl3_33 <=> ! [X0] : k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 38.78/5.24  fof(f335,plain,(
% 38.78/5.24    spl3_34 <=> ! [X0] : k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 38.78/5.24  fof(f5632,plain,(
% 38.78/5.24    spl3_147 <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK1)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).
% 38.78/5.24  fof(f20095,plain,(
% 38.78/5.24    ( ! [X66] : (k4_xboole_0(sK1,X66) = k4_xboole_0(k4_xboole_0(sK1,X66),X66)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_33 | ~spl3_34 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_147 | ~spl3_183 | ~spl3_238 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f20094,f9126])).
% 38.78/5.24  fof(f20094,plain,(
% 38.78/5.24    ( ! [X66] : (k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(sK1,sK1),X66)) = k4_xboole_0(k4_xboole_0(sK1,X66),X66)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_33 | ~spl3_34 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_147 | ~spl3_238 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f20093,f19204])).
% 38.78/5.24  fof(f20093,plain,(
% 38.78/5.24    ( ! [X66] : (k4_xboole_0(k4_xboole_0(sK1,X66),X66) = k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X66,X66)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_33 | ~spl3_34 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_147 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f20092,f5723])).
% 38.78/5.24  fof(f5723,plain,(
% 38.78/5.24    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X5),X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X5,X6))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_147)),
% 38.78/5.24    inference(forward_demodulation,[],[f5655,f5423])).
% 38.78/5.24  fof(f5655,plain,(
% 38.78/5.24    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X5),X6),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X5),X6))) ) | (~spl3_112 | ~spl3_147)),
% 38.78/5.24    inference(superposition,[],[f5633,f2725])).
% 38.78/5.24  fof(f5633,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK1)) ) | ~spl3_147),
% 38.78/5.24    inference(avatar_component_clause,[],[f5632])).
% 38.78/5.24  fof(f20092,plain,(
% 38.78/5.24    ( ! [X66] : (k4_xboole_0(k4_xboole_0(sK1,X66),X66) = k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X66),X66),sK1))) ) | (~spl3_33 | ~spl3_34 | ~spl3_112 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f20091,f2725])).
% 38.78/5.24  fof(f20091,plain,(
% 38.78/5.24    ( ! [X66] : (k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X66),X66),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X66),X66)))) ) | (~spl3_33 | ~spl3_34 | ~spl3_247)),
% 38.78/5.24    inference(forward_demodulation,[],[f19836,f332])).
% 38.78/5.24  fof(f332,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0))) ) | ~spl3_33),
% 38.78/5.24    inference(avatar_component_clause,[],[f331])).
% 38.78/5.24  fof(f19836,plain,(
% 38.78/5.24    ( ! [X66] : (k4_xboole_0(k4_xboole_0(sK1,X66),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X66),X66),sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X66),X66)))) ) | (~spl3_34 | ~spl3_247)),
% 38.78/5.24    inference(superposition,[],[f336,f19677])).
% 38.78/5.24  fof(f336,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))) ) | ~spl3_34),
% 38.78/5.24    inference(avatar_component_clause,[],[f335])).
% 38.78/5.24  fof(f19678,plain,(
% 38.78/5.24    spl3_247 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_238 | ~spl3_243),
% 38.78/5.24    inference(avatar_split_clause,[],[f19491,f19372,f19203,f9792,f9125,f7267,f5958,f5950,f5017,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19676])).
% 38.78/5.24  fof(f19491,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),X23),X24)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_238 | ~spl3_243)),
% 38.78/5.24    inference(forward_demodulation,[],[f19490,f2725])).
% 38.78/5.24  fof(f19490,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(sK1,X23),X24) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_238 | ~spl3_243)),
% 38.78/5.24    inference(forward_demodulation,[],[f19489,f19373])).
% 38.78/5.24  fof(f19489,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(sK1,sK1)),X24)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_160 | ~spl3_166 | ~spl3_183 | ~spl3_189 | ~spl3_238 | ~spl3_243)),
% 38.78/5.24    inference(forward_demodulation,[],[f19488,f19328])).
% 38.78/5.24  fof(f19488,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X23)))),X24)) ) | (~spl3_23 | ~spl3_113 | ~spl3_189 | ~spl3_243)),
% 38.78/5.24    inference(forward_demodulation,[],[f19487,f206])).
% 38.78/5.24  fof(f19487,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),X23)),X24)) ) | (~spl3_23 | ~spl3_113 | ~spl3_189 | ~spl3_243)),
% 38.78/5.24    inference(forward_demodulation,[],[f19486,f2729])).
% 38.78/5.24  fof(f19486,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X23),X23))),X24) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X23)))),X24)) ) | (~spl3_23 | ~spl3_113 | ~spl3_189 | ~spl3_243)),
% 38.78/5.24    inference(forward_demodulation,[],[f19445,f5472])).
% 38.78/5.24  fof(f5472,plain,(
% 38.78/5.24    ( ! [X12,X10,X13,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X11,X12),X13))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X12))),X13)) ) | (~spl3_23 | ~spl3_113)),
% 38.78/5.24    inference(forward_demodulation,[],[f5244,f206])).
% 38.78/5.24  fof(f5244,plain,(
% 38.78/5.24    ( ! [X12,X10,X13,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X11,X12),X13))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X10)),X12),X13)) ) | (~spl3_23 | ~spl3_113)),
% 38.78/5.24    inference(superposition,[],[f206,f2729])).
% 38.78/5.24  fof(f19445,plain,(
% 38.78/5.24    ( ! [X24,X23] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X23)))),X24) = k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,X23),k4_xboole_0(k4_xboole_0(sK1,X23),X24)))) ) | (~spl3_189 | ~spl3_243)),
% 38.78/5.24    inference(superposition,[],[f9793,f19373])).
% 38.78/5.24  fof(f19674,plain,(
% 38.78/5.24    ~spl3_246 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_92 | ~spl3_134 | ~spl3_158 | spl3_169 | ~spl3_173 | ~spl3_231),
% 38.78/5.24    inference(avatar_split_clause,[],[f19161,f17611,f7296,f7279,f5950,f3688,f1775,f1718,f949,f807,f697,f693,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f19671])).
% 38.78/5.24  fof(f1775,plain,(
% 38.78/5.24    spl3_92 <=> ! [X1] : k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,X1)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 38.78/5.24  fof(f7279,plain,(
% 38.78/5.24    spl3_169 <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))))))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_169])])).
% 38.78/5.24  fof(f17611,plain,(
% 38.78/5.24    spl3_231 <=> ! [X11] : k4_xboole_0(k4_xboole_0(sK1,sK1),X11) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_231])])).
% 38.78/5.24  fof(f19161,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK0)))))) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_92 | ~spl3_134 | ~spl3_158 | spl3_169 | ~spl3_173 | ~spl3_231)),
% 38.78/5.24    inference(backward_demodulation,[],[f7281,f19160])).
% 38.78/5.24  fof(f19160,plain,(
% 38.78/5.24    ( ! [X21] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X21,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X21,X21)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_92 | ~spl3_134 | ~spl3_158 | ~spl3_173 | ~spl3_231)),
% 38.78/5.24    inference(forward_demodulation,[],[f19159,f698])).
% 38.78/5.24  fof(f19159,plain,(
% 38.78/5.24    ( ! [X21] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X21,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X21,X21)))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_58 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_92 | ~spl3_134 | ~spl3_158 | ~spl3_173 | ~spl3_231)),
% 38.78/5.24    inference(forward_demodulation,[],[f19158,f6773])).
% 38.78/5.24  fof(f6773,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X1,sK1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_58 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_92 | ~spl3_134 | ~spl3_158)),
% 38.78/5.24    inference(backward_demodulation,[],[f3774,f6718])).
% 38.78/5.24  fof(f6718,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X4))) ) | (~spl3_58 | ~spl3_158)),
% 38.78/5.24    inference(superposition,[],[f694,f5951])).
% 38.78/5.24  fof(f3774,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X1,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_92 | ~spl3_134)),
% 38.78/5.24    inference(backward_demodulation,[],[f1957,f3771])).
% 38.78/5.24  fof(f1957,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))) ) | (~spl3_55 | ~spl3_89 | ~spl3_92)),
% 38.78/5.24    inference(forward_demodulation,[],[f1936,f682])).
% 38.78/5.24  fof(f1936,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))) ) | (~spl3_89 | ~spl3_92)),
% 38.78/5.24    inference(superposition,[],[f1776,f1719])).
% 38.78/5.24  fof(f1776,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,X1)))) ) | ~spl3_92),
% 38.78/5.24    inference(avatar_component_clause,[],[f1775])).
% 38.78/5.24  fof(f19158,plain,(
% 38.78/5.24    ( ! [X21] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X21,X21))))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X21,sK1)))) ) | (~spl3_92 | ~spl3_173 | ~spl3_231)),
% 38.78/5.24    inference(forward_demodulation,[],[f19084,f7297])).
% 38.78/5.24  fof(f19084,plain,(
% 38.78/5.24    ( ! [X21] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X21,X21))))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X21)))) ) | (~spl3_92 | ~spl3_231)),
% 38.78/5.24    inference(superposition,[],[f1776,f17612])).
% 38.78/5.24  fof(f17612,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X11) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11)))) ) | ~spl3_231),
% 38.78/5.24    inference(avatar_component_clause,[],[f17611])).
% 38.78/5.24  fof(f7281,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))))) | spl3_169),
% 38.78/5.24    inference(avatar_component_clause,[],[f7279])).
% 38.78/5.24  fof(f19507,plain,(
% 38.78/5.24    spl3_244 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238),
% 38.78/5.24    inference(avatar_split_clause,[],[f19303,f19203,f9125,f5950,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19505])).
% 38.78/5.24  fof(f19374,plain,(
% 38.78/5.24    spl3_243 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_103 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_140 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_183 | ~spl3_238),
% 38.78/5.24    inference(avatar_split_clause,[],[f19317,f19203,f9125,f5950,f5017,f4459,f4455,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2077,f2049,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19372])).
% 38.78/5.24  fof(f19217,plain,(
% 38.78/5.24    spl3_241 | ~spl3_35 | ~spl3_231),
% 38.78/5.24    inference(avatar_split_clause,[],[f19065,f17611,f371,f19215])).
% 38.78/5.24  fof(f371,plain,(
% 38.78/5.24    spl3_35 <=> ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 38.78/5.24  fof(f19065,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) = k4_xboole_0(sK2,k4_xboole_0(X1,X1))) ) | (~spl3_35 | ~spl3_231)),
% 38.78/5.24    inference(superposition,[],[f372,f17612])).
% 38.78/5.24  fof(f372,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))) ) | ~spl3_35),
% 38.78/5.24    inference(avatar_component_clause,[],[f371])).
% 38.78/5.24  fof(f19205,plain,(
% 38.78/5.24    spl3_238 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_91 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_143 | ~spl3_145 | ~spl3_191 | ~spl3_212),
% 38.78/5.24    inference(avatar_split_clause,[],[f14584,f14382,f9800,f5017,f4923,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1771,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f19203])).
% 38.78/5.24  fof(f18991,plain,(
% 38.78/5.24    spl3_237 | ~spl3_23 | ~spl3_58 | ~spl3_64 | ~spl3_67 | ~spl3_153 | ~spl3_207 | ~spl3_232),
% 38.78/5.24    inference(avatar_split_clause,[],[f18162,f17963,f12888,f5930,f1025,f945,f693,f205,f18989])).
% 38.78/5.24  fof(f18162,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,sK2))) ) | (~spl3_23 | ~spl3_58 | ~spl3_64 | ~spl3_67 | ~spl3_153 | ~spl3_207 | ~spl3_232)),
% 38.78/5.24    inference(backward_demodulation,[],[f1313,f18159])).
% 38.78/5.24  fof(f1313,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(X7,sK2),X7) = k5_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK1,X7))))) ) | (~spl3_64 | ~spl3_67)),
% 38.78/5.24    inference(superposition,[],[f1026,f946])).
% 38.78/5.24  fof(f18463,plain,(
% 38.78/5.24    spl3_235 | ~spl3_7 | ~spl3_232),
% 38.78/5.24    inference(avatar_split_clause,[],[f18000,f17963,f63,f18461])).
% 38.78/5.24  fof(f18000,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k5_xboole_0(X1,k4_xboole_0(X1,sK2))) ) | (~spl3_7 | ~spl3_232)),
% 38.78/5.24    inference(superposition,[],[f64,f17964])).
% 38.78/5.24  fof(f18345,plain,(
% 38.78/5.24    spl3_234 | ~spl3_7 | ~spl3_23 | ~spl3_58 | ~spl3_64 | ~spl3_153 | ~spl3_207 | ~spl3_232),
% 38.78/5.24    inference(avatar_split_clause,[],[f18161,f17963,f12888,f5930,f945,f693,f205,f63,f18343])).
% 38.78/5.24  fof(f18161,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,sK2))) ) | (~spl3_7 | ~spl3_23 | ~spl3_58 | ~spl3_64 | ~spl3_153 | ~spl3_207 | ~spl3_232)),
% 38.78/5.24    inference(backward_demodulation,[],[f977,f18159])).
% 38.78/5.24  fof(f977,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X9)) = k5_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(sK2,k4_xboole_0(sK1,X9))))) ) | (~spl3_7 | ~spl3_64)),
% 38.78/5.24    inference(superposition,[],[f64,f946])).
% 38.78/5.24  fof(f18341,plain,(
% 38.78/5.24    spl3_233 | ~spl3_8 | ~spl3_23),
% 38.78/5.24    inference(avatar_split_clause,[],[f364,f205,f67,f18339])).
% 38.78/5.24  fof(f364,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))) ) | (~spl3_8 | ~spl3_23)),
% 38.78/5.24    inference(forward_demodulation,[],[f348,f206])).
% 38.78/5.24  fof(f348,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) ) | (~spl3_8 | ~spl3_23)),
% 38.78/5.24    inference(superposition,[],[f206,f68])).
% 38.78/5.24  fof(f17965,plain,(
% 38.78/5.24    spl3_232 | ~spl3_23 | ~spl3_61 | ~spl3_67 | ~spl3_69 | ~spl3_94 | ~spl3_113 | ~spl3_125 | ~spl3_138 | ~spl3_230),
% 38.78/5.24    inference(avatar_split_clause,[],[f17820,f17607,f4447,f3204,f2728,f1875,f1139,f1025,f807,f205,f17963])).
% 38.78/5.24  fof(f1875,plain,(
% 38.78/5.24    spl3_94 <=> ! [X7] : k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 38.78/5.24  fof(f3204,plain,(
% 38.78/5.24    spl3_125 <=> ! [X7,X8] : k4_xboole_0(sK2,k4_xboole_0(X7,X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 38.78/5.24  fof(f17607,plain,(
% 38.78/5.24    spl3_230 <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_230])])).
% 38.78/5.24  fof(f17820,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(X8,sK2) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2)))) ) | (~spl3_23 | ~spl3_61 | ~spl3_67 | ~spl3_69 | ~spl3_94 | ~spl3_113 | ~spl3_125 | ~spl3_138 | ~spl3_230)),
% 38.78/5.24    inference(forward_demodulation,[],[f17819,f1140])).
% 38.78/5.24  fof(f17819,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(sK1,X8)))) ) | (~spl3_23 | ~spl3_61 | ~spl3_67 | ~spl3_94 | ~spl3_113 | ~spl3_125 | ~spl3_138 | ~spl3_230)),
% 38.78/5.24    inference(forward_demodulation,[],[f17818,f5451])).
% 38.78/5.24  fof(f5451,plain,(
% 38.78/5.24    ( ! [X6] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X6)) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(sK2,k4_xboole_0(X6,sK1))))) ) | (~spl3_61 | ~spl3_94 | ~spl3_113 | ~spl3_125)),
% 38.78/5.24    inference(forward_demodulation,[],[f5450,f808])).
% 38.78/5.24  fof(f5450,plain,(
% 38.78/5.24    ( ! [X6] : (k4_xboole_0(sK2,k4_xboole_0(sK2,X6)) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(sK2,k4_xboole_0(X6,sK1))))) ) | (~spl3_94 | ~spl3_113 | ~spl3_125)),
% 38.78/5.24    inference(forward_demodulation,[],[f5229,f3205])).
% 38.78/5.24  fof(f3205,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(X7,X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8))) ) | ~spl3_125),
% 38.78/5.24    inference(avatar_component_clause,[],[f3204])).
% 38.78/5.24  fof(f5229,plain,(
% 38.78/5.24    ( ! [X6] : (k4_xboole_0(sK2,k4_xboole_0(sK2,X6)) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X6)),sK1))))) ) | (~spl3_94 | ~spl3_113)),
% 38.78/5.24    inference(superposition,[],[f2729,f1876])).
% 38.78/5.24  fof(f1876,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1))) ) | ~spl3_94),
% 38.78/5.24    inference(avatar_component_clause,[],[f1875])).
% 38.78/5.24  fof(f17818,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(X8,sK1)))))) ) | (~spl3_23 | ~spl3_67 | ~spl3_138 | ~spl3_230)),
% 38.78/5.24    inference(forward_demodulation,[],[f17817,f4448])).
% 38.78/5.24  fof(f17817,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X8)))))) ) | (~spl3_23 | ~spl3_67 | ~spl3_230)),
% 38.78/5.24    inference(forward_demodulation,[],[f17679,f206])).
% 38.78/5.24  fof(f17679,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,sK2))) = k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK1),X8)))) ) | (~spl3_67 | ~spl3_230)),
% 38.78/5.24    inference(superposition,[],[f1026,f17608])).
% 38.78/5.24  fof(f17608,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0)) ) | ~spl3_230),
% 38.78/5.24    inference(avatar_component_clause,[],[f17607])).
% 38.78/5.24  fof(f17613,plain,(
% 38.78/5.24    spl3_231 | ~spl3_8 | ~spl3_23 | ~spl3_61 | ~spl3_63 | ~spl3_91 | ~spl3_120 | ~spl3_139 | ~spl3_142 | ~spl3_227 | ~spl3_228 | ~spl3_229),
% 38.78/5.24    inference(avatar_split_clause,[],[f17557,f17162,f17158,f16005,f4831,f4451,f3184,f1771,f815,f807,f205,f67,f17611])).
% 38.78/5.24  fof(f815,plain,(
% 38.78/5.24    spl3_63 <=> ! [X2] : k4_xboole_0(sK2,X2) = k4_xboole_0(sK2,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 38.78/5.24  fof(f17158,plain,(
% 38.78/5.24    spl3_228 <=> ! [X4] : k4_xboole_0(k4_xboole_0(sK1,sK1),X4) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_228])])).
% 38.78/5.24  fof(f17162,plain,(
% 38.78/5.24    spl3_229 <=> ! [X3] : k4_xboole_0(sK2,X3) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_229])])).
% 38.78/5.24  fof(f17557,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X11) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_61 | ~spl3_63 | ~spl3_91 | ~spl3_120 | ~spl3_139 | ~spl3_142 | ~spl3_227 | ~spl3_228 | ~spl3_229)),
% 38.78/5.24    inference(forward_demodulation,[],[f17556,f17133])).
% 38.78/5.24  fof(f17556,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X11),X11)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X11,X11)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_61 | ~spl3_63 | ~spl3_91 | ~spl3_228 | ~spl3_229)),
% 38.78/5.24    inference(forward_demodulation,[],[f17468,f1845])).
% 38.78/5.24  fof(f1845,plain,(
% 38.78/5.24    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,X2),X3)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X3,X2)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_61 | ~spl3_63 | ~spl3_91)),
% 38.78/5.24    inference(forward_demodulation,[],[f1794,f943])).
% 38.78/5.24  fof(f943,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,X8))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(sK1,X8)))))) ) | (~spl3_23 | ~spl3_61 | ~spl3_63)),
% 38.78/5.24    inference(forward_demodulation,[],[f942,f206])).
% 38.78/5.24  fof(f942,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),X8))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X7,X8)))) ) | (~spl3_23 | ~spl3_61 | ~spl3_63)),
% 38.78/5.24    inference(forward_demodulation,[],[f941,f808])).
% 38.78/5.24  fof(f941,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),X8))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,X8)))) ) | (~spl3_23 | ~spl3_63)),
% 38.78/5.24    inference(forward_demodulation,[],[f920,f206])).
% 38.78/5.24  fof(f920,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),X8))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X7)),X8)) ) | (~spl3_23 | ~spl3_63)),
% 38.78/5.24    inference(superposition,[],[f206,f816])).
% 38.78/5.24  fof(f816,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,X2) = k4_xboole_0(sK2,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))) ) | ~spl3_63),
% 38.78/5.24    inference(avatar_component_clause,[],[f815])).
% 38.78/5.24  fof(f1794,plain,(
% 38.78/5.24    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,X2),X3)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK1,X2)))))) ) | (~spl3_8 | ~spl3_91)),
% 38.78/5.24    inference(superposition,[],[f1772,f68])).
% 38.78/5.24  fof(f17468,plain,(
% 38.78/5.24    ( ! [X11] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,X11),X11)) = k4_xboole_0(k4_xboole_0(sK2,X11),k4_xboole_0(k4_xboole_0(sK1,X11),X11))) ) | (~spl3_228 | ~spl3_229)),
% 38.78/5.24    inference(superposition,[],[f17159,f17163])).
% 38.78/5.24  fof(f17163,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK2,X3) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))) ) | ~spl3_229),
% 38.78/5.24    inference(avatar_component_clause,[],[f17162])).
% 38.78/5.24  fof(f17159,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X4) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4)) ) | ~spl3_228),
% 38.78/5.24    inference(avatar_component_clause,[],[f17158])).
% 38.78/5.24  fof(f17609,plain,(
% 38.78/5.24    spl3_230 | ~spl3_64 | ~spl3_228),
% 38.78/5.24    inference(avatar_split_clause,[],[f17184,f17158,f945,f17607])).
% 38.78/5.24  fof(f17184,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0)) ) | (~spl3_64 | ~spl3_228)),
% 38.78/5.24    inference(superposition,[],[f17159,f946])).
% 38.78/5.24  fof(f17164,plain,(
% 38.78/5.24    spl3_229 | ~spl3_38 | ~spl3_59 | ~spl3_227),
% 38.78/5.24    inference(avatar_split_clause,[],[f17117,f16005,f697,f393,f17162])).
% 38.78/5.24  fof(f17117,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK2,X3) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))) ) | (~spl3_38 | ~spl3_59 | ~spl3_227)),
% 38.78/5.24    inference(forward_demodulation,[],[f17116,f698])).
% 38.78/5.24  fof(f17116,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X3))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))) ) | (~spl3_38 | ~spl3_227)),
% 38.78/5.24    inference(forward_demodulation,[],[f17042,f394])).
% 38.78/5.24  fof(f17042,plain,(
% 38.78/5.24    ( ! [X3] : (k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X3))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X3)))) ) | (~spl3_38 | ~spl3_227)),
% 38.78/5.24    inference(superposition,[],[f394,f16006])).
% 38.78/5.24  fof(f17160,plain,(
% 38.78/5.24    spl3_228 | ~spl3_61 | ~spl3_113 | ~spl3_137 | ~spl3_218),
% 38.78/5.24    inference(avatar_split_clause,[],[f15464,f15237,f4268,f2728,f807,f17158])).
% 38.78/5.24  fof(f15237,plain,(
% 38.78/5.24    spl3_218 <=> ! [X13] : k4_xboole_0(X13,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X13,k4_xboole_0(sK2,X13))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_218])])).
% 38.78/5.24  fof(f15464,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X4) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4)) ) | (~spl3_61 | ~spl3_113 | ~spl3_137 | ~spl3_218)),
% 38.78/5.24    inference(forward_demodulation,[],[f15463,f4269])).
% 38.78/5.24  fof(f15463,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X4)),X4)) ) | (~spl3_61 | ~spl3_113 | ~spl3_218)),
% 38.78/5.24    inference(forward_demodulation,[],[f15290,f808])).
% 38.78/5.24  fof(f15290,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X4)),X4)) ) | (~spl3_113 | ~spl3_218)),
% 38.78/5.24    inference(superposition,[],[f2729,f15238])).
% 38.78/5.24  fof(f15238,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(X13,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X13,k4_xboole_0(sK2,X13))) ) | ~spl3_218),
% 38.78/5.24    inference(avatar_component_clause,[],[f15237])).
% 38.78/5.24  fof(f16007,plain,(
% 38.78/5.24    spl3_227 | ~spl3_38 | ~spl3_106 | ~spl3_217),
% 38.78/5.24    inference(avatar_split_clause,[],[f15147,f15045,f2089,f393,f16005])).
% 38.78/5.24  fof(f2089,plain,(
% 38.78/5.24    spl3_106 <=> ! [X5,X6] : k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).
% 38.78/5.24  fof(f15147,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2))) ) | (~spl3_38 | ~spl3_106 | ~spl3_217)),
% 38.78/5.24    inference(forward_demodulation,[],[f15084,f394])).
% 38.78/5.24  fof(f15084,plain,(
% 38.78/5.24    ( ! [X2] : (k5_xboole_0(sK2,k4_xboole_0(sK2,X2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X2),X2))) ) | (~spl3_106 | ~spl3_217)),
% 38.78/5.24    inference(superposition,[],[f2090,f15046])).
% 38.78/5.24  fof(f2090,plain,(
% 38.78/5.24    ( ! [X6,X5] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6))) ) | ~spl3_106),
% 38.78/5.24    inference(avatar_component_clause,[],[f2089])).
% 38.78/5.24  fof(f15991,plain,(
% 38.78/5.24    spl3_223 | ~spl3_8 | ~spl3_23),
% 38.78/5.24    inference(avatar_split_clause,[],[f350,f205,f67,f15989])).
% 38.78/5.24  fof(f350,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) ) | (~spl3_8 | ~spl3_23)),
% 38.78/5.24    inference(superposition,[],[f68,f206])).
% 38.78/5.24  fof(f15979,plain,(
% 38.78/5.24    spl3_220 | ~spl3_58 | ~spl3_64 | ~spl3_66 | ~spl3_103 | ~spl3_113 | ~spl3_211),
% 38.78/5.24    inference(avatar_split_clause,[],[f14497,f14378,f2728,f2077,f953,f945,f693,f15977])).
% 38.78/5.24  fof(f14378,plain,(
% 38.78/5.24    spl3_211 <=> ! [X14] : k4_xboole_0(sK2,X14) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_211])])).
% 38.78/5.24  fof(f14497,plain,(
% 38.78/5.24    ( ! [X22] : (k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),sK2))) ) | (~spl3_58 | ~spl3_64 | ~spl3_66 | ~spl3_103 | ~spl3_113 | ~spl3_211)),
% 38.78/5.24    inference(backward_demodulation,[],[f4100,f14492])).
% 38.78/5.24  fof(f14492,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8))) ) | (~spl3_58 | ~spl3_113 | ~spl3_211)),
% 38.78/5.24    inference(forward_demodulation,[],[f14434,f694])).
% 38.78/5.24  fof(f14434,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X8))),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8))) ) | (~spl3_113 | ~spl3_211)),
% 38.78/5.24    inference(superposition,[],[f2729,f14379])).
% 38.78/5.24  fof(f14379,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(sK2,X14) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))) ) | ~spl3_211),
% 38.78/5.24    inference(avatar_component_clause,[],[f14378])).
% 38.78/5.24  fof(f4100,plain,(
% 38.78/5.24    ( ! [X22] : (k4_xboole_0(sK2,X22) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(sK2,X22)))) ) | (~spl3_64 | ~spl3_66 | ~spl3_103)),
% 38.78/5.24    inference(forward_demodulation,[],[f4008,f954])).
% 38.78/5.24  fof(f4008,plain,(
% 38.78/5.24    ( ! [X22] : (k4_xboole_0(sK2,k4_xboole_0(X22,k4_xboole_0(X22,sK2))) = k5_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(k4_xboole_0(sK1,X22),k4_xboole_0(sK2,k4_xboole_0(X22,k4_xboole_0(X22,sK2)))))) ) | (~spl3_64 | ~spl3_103)),
% 38.78/5.24    inference(superposition,[],[f2078,f946])).
% 38.78/5.24  fof(f15239,plain,(
% 38.78/5.24    spl3_218 | ~spl3_67 | ~spl3_140 | ~spl3_215 | ~spl3_217),
% 38.78/5.24    inference(avatar_split_clause,[],[f15164,f15045,f14837,f4455,f1025,f15237])).
% 38.78/5.24  fof(f15164,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(X13,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X13,k4_xboole_0(sK2,X13))) ) | (~spl3_67 | ~spl3_140 | ~spl3_215 | ~spl3_217)),
% 38.78/5.24    inference(forward_demodulation,[],[f15163,f4456])).
% 38.78/5.24  fof(f15163,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(X13,k4_xboole_0(sK2,X13)) = k5_xboole_0(X13,k4_xboole_0(k4_xboole_0(sK1,sK1),X13))) ) | (~spl3_67 | ~spl3_215 | ~spl3_217)),
% 38.78/5.24    inference(forward_demodulation,[],[f15095,f14838])).
% 38.78/5.24  fof(f15095,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(X13,k4_xboole_0(sK2,X13)) = k5_xboole_0(X13,k4_xboole_0(k4_xboole_0(sK2,X13),k4_xboole_0(sK2,X13)))) ) | (~spl3_67 | ~spl3_217)),
% 38.78/5.24    inference(superposition,[],[f1026,f15046])).
% 38.78/5.24  fof(f15047,plain,(
% 38.78/5.24    spl3_217 | ~spl3_23 | ~spl3_91 | ~spl3_113 | ~spl3_153 | ~spl3_214),
% 38.78/5.24    inference(avatar_split_clause,[],[f15018,f14833,f5930,f2728,f1771,f205,f15045])).
% 38.78/5.24  fof(f14833,plain,(
% 38.78/5.24    spl3_214 <=> ! [X8] : k4_xboole_0(k4_xboole_0(sK1,X8),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_214])])).
% 38.78/5.24  fof(f15018,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),X7)) ) | (~spl3_23 | ~spl3_91 | ~spl3_113 | ~spl3_153 | ~spl3_214)),
% 38.78/5.24    inference(forward_demodulation,[],[f15017,f5931])).
% 38.78/5.24  fof(f15017,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK2)) = k4_xboole_0(k4_xboole_0(sK2,X7),X7)) ) | (~spl3_23 | ~spl3_91 | ~spl3_113 | ~spl3_214)),
% 38.78/5.24    inference(forward_demodulation,[],[f15016,f1772])).
% 38.78/5.24  fof(f15016,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X7),X7)))) ) | (~spl3_23 | ~spl3_113 | ~spl3_214)),
% 38.78/5.24    inference(forward_demodulation,[],[f14913,f206])).
% 38.78/5.24  fof(f14913,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK1,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK2)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X7))),X7)) ) | (~spl3_113 | ~spl3_214)),
% 38.78/5.24    inference(superposition,[],[f2729,f14834])).
% 38.78/5.24  fof(f14834,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,X8),sK2) = k4_xboole_0(k4_xboole_0(sK1,X8),k4_xboole_0(sK2,X8))) ) | ~spl3_214),
% 38.78/5.24    inference(avatar_component_clause,[],[f14833])).
% 38.78/5.24  fof(f14839,plain,(
% 38.78/5.24    spl3_215 | ~spl3_36 | ~spl3_113 | ~spl3_143 | ~spl3_212),
% 38.78/5.24    inference(avatar_split_clause,[],[f14583,f14382,f4923,f2728,f384,f14837])).
% 38.78/5.24  fof(f14835,plain,(
% 38.78/5.24    spl3_214 | ~spl3_58 | ~spl3_113 | ~spl3_211),
% 38.78/5.24    inference(avatar_split_clause,[],[f14492,f14378,f2728,f693,f14833])).
% 38.78/5.24  fof(f14384,plain,(
% 38.78/5.24    spl3_212 | ~spl3_8 | ~spl3_36 | ~spl3_55 | ~spl3_61 | ~spl3_207),
% 38.78/5.24    inference(avatar_split_clause,[],[f13047,f12888,f807,f681,f384,f67,f14382])).
% 38.78/5.24  fof(f13047,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))) ) | (~spl3_8 | ~spl3_36 | ~spl3_55 | ~spl3_61 | ~spl3_207)),
% 38.78/5.24    inference(forward_demodulation,[],[f13046,f682])).
% 38.78/5.24  fof(f13046,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))) ) | (~spl3_8 | ~spl3_36 | ~spl3_61 | ~spl3_207)),
% 38.78/5.24    inference(forward_demodulation,[],[f13045,f808])).
% 38.78/5.24  fof(f13045,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))) ) | (~spl3_8 | ~spl3_36 | ~spl3_207)),
% 38.78/5.24    inference(forward_demodulation,[],[f12919,f68])).
% 38.78/5.24  fof(f12919,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(sK2,X0),sK2)) = k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK2))) ) | (~spl3_36 | ~spl3_207)),
% 38.78/5.24    inference(superposition,[],[f12889,f385])).
% 38.78/5.24  fof(f14380,plain,(
% 38.78/5.24    spl3_211 | ~spl3_8 | ~spl3_35 | ~spl3_62 | ~spl3_207),
% 38.78/5.24    inference(avatar_split_clause,[],[f13037,f12888,f811,f371,f67,f14378])).
% 38.78/5.24  fof(f13037,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(sK2,X14) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))) ) | (~spl3_8 | ~spl3_35 | ~spl3_62 | ~spl3_207)),
% 38.78/5.24    inference(forward_demodulation,[],[f13036,f372])).
% 38.78/5.24  fof(f13036,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X14))) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))) ) | (~spl3_8 | ~spl3_62 | ~spl3_207)),
% 38.78/5.24    inference(forward_demodulation,[],[f13035,f68])).
% 38.78/5.24  fof(f13035,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(sK1,X14),sK2)) = k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(sK1,sK2))) ) | (~spl3_8 | ~spl3_62 | ~spl3_207)),
% 38.78/5.24    inference(forward_demodulation,[],[f12914,f812])).
% 38.78/5.24  fof(f12914,plain,(
% 38.78/5.24    ( ! [X14] : (k4_xboole_0(k4_xboole_0(sK1,X14),k4_xboole_0(k4_xboole_0(sK1,X14),sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X14,k4_xboole_0(X14,sK1))),k4_xboole_0(sK1,sK2))) ) | (~spl3_8 | ~spl3_207)),
% 38.78/5.24    inference(superposition,[],[f12889,f68])).
% 38.78/5.24  fof(f12890,plain,(
% 38.78/5.24    spl3_207 | ~spl3_13 | ~spl3_113),
% 38.78/5.24    inference(avatar_split_clause,[],[f5158,f2728,f112,f12888])).
% 38.78/5.24  fof(f112,plain,(
% 38.78/5.24    spl3_13 <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 38.78/5.24  fof(f5158,plain,(
% 38.78/5.24    ( ! [X36] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X36)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X36,k4_xboole_0(X36,sK2))) ) | (~spl3_13 | ~spl3_113)),
% 38.78/5.24    inference(superposition,[],[f2729,f114])).
% 38.78/5.24  fof(f114,plain,(
% 38.78/5.24    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_13),
% 38.78/5.24    inference(avatar_component_clause,[],[f112])).
% 38.78/5.24  fof(f12482,plain,(
% 38.78/5.24    spl3_205 | ~spl3_69 | ~spl3_140 | ~spl3_190 | ~spl3_202),
% 38.78/5.24    inference(avatar_split_clause,[],[f12300,f12101,f9796,f4455,f1139,f12480])).
% 38.78/5.24  fof(f12300,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,sK2),sK2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1))) ) | (~spl3_69 | ~spl3_140 | ~spl3_190 | ~spl3_202)),
% 38.78/5.24    inference(forward_demodulation,[],[f12245,f10213])).
% 38.78/5.24  fof(f12245,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) ) | (~spl3_140 | ~spl3_202)),
% 38.78/5.24    inference(superposition,[],[f4456,f12102])).
% 38.78/5.24  fof(f12103,plain,(
% 38.78/5.24    spl3_202 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_155 | ~spl3_166 | ~spl3_190),
% 38.78/5.24    inference(avatar_split_clause,[],[f10285,f9796,f7267,f5938,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2724,f2085,f2049,f1718,f1231,f949,f945,f807,f697,f681,f584,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f12101])).
% 38.78/5.24  fof(f5938,plain,(
% 38.78/5.24    spl3_155 <=> ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).
% 38.78/5.24  fof(f10285,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_155 | ~spl3_166 | ~spl3_190)),
% 38.78/5.24    inference(forward_demodulation,[],[f10284,f7268])).
% 38.78/5.24  fof(f10284,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_155 | ~spl3_190)),
% 38.78/5.24    inference(forward_demodulation,[],[f10217,f5128])).
% 38.78/5.24  fof(f10217,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,sK2))) ) | (~spl3_155 | ~spl3_190)),
% 38.78/5.24    inference(superposition,[],[f5939,f9797])).
% 38.78/5.24  fof(f5939,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1)) ) | ~spl3_155),
% 38.78/5.24    inference(avatar_component_clause,[],[f5938])).
% 38.78/5.24  fof(f10331,plain,(
% 38.78/5.24    spl3_199 | ~spl3_35 | ~spl3_138 | ~spl3_190),
% 38.78/5.24    inference(avatar_split_clause,[],[f10275,f9796,f4447,f371,f10329])).
% 38.78/5.24  fof(f10275,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(X1,sK1))) ) | (~spl3_35 | ~spl3_138 | ~spl3_190)),
% 38.78/5.24    inference(forward_demodulation,[],[f10211,f4448])).
% 38.78/5.24  fof(f10211,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1))) ) | (~spl3_35 | ~spl3_190)),
% 38.78/5.24    inference(superposition,[],[f372,f9797])).
% 38.78/5.24  fof(f9830,plain,(
% 38.78/5.24    spl3_198 | ~spl3_8 | ~spl3_62 | ~spl3_186),
% 38.78/5.24    inference(avatar_split_clause,[],[f9722,f9137,f811,f67,f9828])).
% 38.78/5.24  fof(f9137,plain,(
% 38.78/5.24    spl3_186 <=> ! [X3] : k4_xboole_0(k4_xboole_0(sK1,X3),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X3)),sK1)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_186])])).
% 38.78/5.24  fof(f9722,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(k4_xboole_0(sK1,X13),sK1) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1)) ) | (~spl3_8 | ~spl3_62 | ~spl3_186)),
% 38.78/5.24    inference(forward_demodulation,[],[f9651,f812])).
% 38.78/5.24  fof(f9651,plain,(
% 38.78/5.24    ( ! [X13] : (k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X13,k4_xboole_0(X13,sK1))),sK1)) ) | (~spl3_8 | ~spl3_186)),
% 38.78/5.24    inference(superposition,[],[f9138,f68])).
% 38.78/5.24  fof(f9138,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(k4_xboole_0(sK1,X3),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X3)),sK1)) ) | ~spl3_186),
% 38.78/5.24    inference(avatar_component_clause,[],[f9137])).
% 38.78/5.24  fof(f9802,plain,(
% 38.78/5.24    spl3_191 | ~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_87 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141),
% 38.78/5.24    inference(avatar_split_clause,[],[f4795,f4459,f4451,f3544,f2740,f2085,f1663,f1231,f945,f697,f584,f205,f63,f9800])).
% 38.78/5.24  fof(f4795,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK1,sK1),X2))) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_87 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.24    inference(backward_demodulation,[],[f1664,f4791])).
% 38.78/5.24  fof(f9798,plain,(
% 38.78/5.24    spl3_190 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_78 | ~spl3_89 | ~spl3_134),
% 38.78/5.24    inference(avatar_split_clause,[],[f3805,f3688,f1718,f1427,f949,f807,f681,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f9796])).
% 38.78/5.24  fof(f1427,plain,(
% 38.78/5.24    spl3_78 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 38.78/5.24  fof(f3805,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_78 | ~spl3_89 | ~spl3_134)),
% 38.78/5.24    inference(backward_demodulation,[],[f1465,f3804])).
% 38.78/5.24  fof(f3804,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.24    inference(backward_demodulation,[],[f3765,f3803])).
% 38.78/5.24  fof(f1465,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK1)))) ) | (~spl3_23 | ~spl3_61 | ~spl3_78)),
% 38.78/5.24    inference(forward_demodulation,[],[f1464,f872])).
% 38.78/5.24  fof(f872,plain,(
% 38.78/5.24    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X6,X7)))) ) | (~spl3_23 | ~spl3_61)),
% 38.78/5.24    inference(forward_demodulation,[],[f856,f808])).
% 38.78/5.24  fof(f856,plain,(
% 38.78/5.24    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X6)),X7) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X6,X7)))) ) | (~spl3_23 | ~spl3_61)),
% 38.78/5.24    inference(superposition,[],[f206,f808])).
% 38.78/5.24  fof(f1464,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X1)),sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) ) | (~spl3_23 | ~spl3_61 | ~spl3_78)),
% 38.78/5.24    inference(forward_demodulation,[],[f1463,f808])).
% 38.78/5.24  fof(f1463,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) ) | (~spl3_23 | ~spl3_61 | ~spl3_78)),
% 38.78/5.24    inference(forward_demodulation,[],[f1444,f808])).
% 38.78/5.24  fof(f1444,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK1) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X1,sK2)))) ) | (~spl3_23 | ~spl3_78)),
% 38.78/5.24    inference(superposition,[],[f1428,f206])).
% 38.78/5.24  fof(f1428,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)) ) | ~spl3_78),
% 38.78/5.24    inference(avatar_component_clause,[],[f1427])).
% 38.78/5.24  fof(f9794,plain,(
% 38.78/5.24    spl3_189 | ~spl3_8 | ~spl3_23),
% 38.78/5.24    inference(avatar_split_clause,[],[f339,f205,f67,f9792])).
% 38.78/5.24  fof(f339,plain,(
% 38.78/5.24    ( ! [X2,X3,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3)) ) | (~spl3_8 | ~spl3_23)),
% 38.78/5.24    inference(superposition,[],[f206,f68])).
% 38.78/5.24  fof(f9139,plain,(
% 38.78/5.24    spl3_186 | ~spl3_112 | ~spl3_180),
% 38.78/5.24    inference(avatar_split_clause,[],[f8837,f8729,f2724,f9137])).
% 38.78/5.24  fof(f8729,plain,(
% 38.78/5.24    spl3_180 <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_180])])).
% 38.78/5.24  fof(f8837,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(k4_xboole_0(sK1,X3),sK1) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X3)),sK1)) ) | (~spl3_112 | ~spl3_180)),
% 38.78/5.24    inference(superposition,[],[f8730,f2725])).
% 38.78/5.24  fof(f8730,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1)))) ) | ~spl3_180),
% 38.78/5.24    inference(avatar_component_clause,[],[f8729])).
% 38.78/5.24  fof(f9127,plain,(
% 38.78/5.24    spl3_183 | ~spl3_7 | ~spl3_34 | ~spl3_149),
% 38.78/5.24    inference(avatar_split_clause,[],[f5871,f5770,f335,f63,f9125])).
% 38.78/5.24  fof(f5871,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(sK1,X9) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))) ) | (~spl3_7 | ~spl3_34 | ~spl3_149)),
% 38.78/5.24    inference(forward_demodulation,[],[f5814,f64])).
% 38.78/5.24  fof(f5814,plain,(
% 38.78/5.24    ( ! [X9] : (k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X9))) = k4_xboole_0(k4_xboole_0(sK1,X9),k4_xboole_0(k4_xboole_0(sK1,sK1),X9))) ) | (~spl3_34 | ~spl3_149)),
% 38.78/5.24    inference(superposition,[],[f336,f5771])).
% 38.78/5.24  fof(f8731,plain,(
% 38.78/5.24    spl3_180 | ~spl3_112 | ~spl3_177),
% 38.78/5.24    inference(avatar_split_clause,[],[f8484,f7312,f2724,f8729])).
% 38.78/5.24  fof(f8484,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1)))) ) | (~spl3_112 | ~spl3_177)),
% 38.78/5.24    inference(superposition,[],[f2725,f7313])).
% 38.78/5.24  fof(f8727,plain,(
% 38.78/5.24    spl3_179 | ~spl3_67 | ~spl3_140 | ~spl3_158 | ~spl3_166),
% 38.78/5.24    inference(avatar_split_clause,[],[f7473,f7267,f5950,f4455,f1025,f8725])).
% 38.78/5.24  fof(f7473,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(k4_xboole_0(X4,sK1),sK1) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1))) ) | (~spl3_67 | ~spl3_140 | ~spl3_158 | ~spl3_166)),
% 38.78/5.24    inference(forward_demodulation,[],[f7433,f6744])).
% 38.78/5.24  fof(f7433,plain,(
% 38.78/5.24    ( ! [X4] : (k5_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X4)) = k4_xboole_0(k4_xboole_0(X4,sK1),k4_xboole_0(sK1,sK1))) ) | (~spl3_140 | ~spl3_166)),
% 38.78/5.24    inference(superposition,[],[f4456,f7268])).
% 38.78/5.24  fof(f7314,plain,(
% 38.78/5.24    spl3_177 | ~spl3_145 | ~spl3_164),
% 38.78/5.24    inference(avatar_split_clause,[],[f7204,f7171,f5017,f7312])).
% 38.78/5.24  fof(f7171,plain,(
% 38.78/5.24    spl3_164 <=> ! [X3] : k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).
% 38.78/5.24  fof(f7204,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK1,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1))) ) | (~spl3_145 | ~spl3_164)),
% 38.78/5.24    inference(forward_demodulation,[],[f7178,f7172])).
% 38.78/5.24  fof(f7172,plain,(
% 38.78/5.24    ( ! [X3] : (k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK1))) ) | ~spl3_164),
% 38.78/5.24    inference(avatar_component_clause,[],[f7171])).
% 38.78/5.24  fof(f7178,plain,(
% 38.78/5.24    ( ! [X2] : (k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X2),sK1))) ) | (~spl3_145 | ~spl3_164)),
% 38.78/5.24    inference(superposition,[],[f7172,f5018])).
% 38.78/5.24  fof(f7298,plain,(
% 38.78/5.24    spl3_173 | ~spl3_58 | ~spl3_158),
% 38.78/5.24    inference(avatar_split_clause,[],[f6718,f5950,f693,f7296])).
% 38.78/5.24  fof(f7282,plain,(
% 38.78/5.24    ~spl3_169 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | spl3_45 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_92 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_148 | ~spl3_158 | ~spl3_163 | ~spl3_164),
% 38.78/5.24    inference(avatar_split_clause,[],[f7220,f7171,f6833,f5950,f5636,f5017,f4459,f4451,f4268,f3688,f3544,f3192,f2740,f2728,f2724,f2085,f2049,f1775,f1718,f1231,f949,f945,f807,f697,f693,f681,f584,f545,f478,f393,f388,f384,f205,f100,f93,f88,f67,f63,f7279])).
% 38.78/5.24  fof(f545,plain,(
% 38.78/5.24    spl3_45 <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 38.78/5.24  fof(f5636,plain,(
% 38.78/5.24    spl3_148 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK2),X1) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).
% 38.78/5.24  fof(f7220,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))))) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | spl3_45 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_92 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_148 | ~spl3_158 | ~spl3_163 | ~spl3_164)),
% 38.78/5.24    inference(backward_demodulation,[],[f547,f7219])).
% 38.78/5.24  fof(f7219,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X8,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(X8,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_92 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_148 | ~spl3_158 | ~spl3_163 | ~spl3_164)),
% 38.78/5.24    inference(forward_demodulation,[],[f7214,f6773])).
% 38.78/5.24  fof(f7214,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X8,sK1)) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X8,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_148 | ~spl3_158 | ~spl3_163 | ~spl3_164)),
% 38.78/5.24    inference(backward_demodulation,[],[f6872,f7213])).
% 38.78/5.24  fof(f7213,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(sK1,k4_xboole_0(X4,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X4,sK1),sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_113 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_164)),
% 38.78/5.24    inference(forward_demodulation,[],[f7212,f5468])).
% 38.78/5.24  fof(f7212,plain,(
% 38.78/5.24    ( ! [X4] : (k5_xboole_0(sK1,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X4,sK1),sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_58 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_158 | ~spl3_164)),
% 38.78/5.24    inference(forward_demodulation,[],[f7211,f6718])).
% 38.78/5.24  fof(f7211,plain,(
% 38.78/5.24    ( ! [X4] : (k5_xboole_0(sK1,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X4,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_50 | ~spl3_55 | ~spl3_59 | ~spl3_61 | ~spl3_64 | ~spl3_65 | ~spl3_71 | ~spl3_89 | ~spl3_96 | ~spl3_105 | ~spl3_112 | ~spl3_116 | ~spl3_122 | ~spl3_128 | ~spl3_134 | ~spl3_137 | ~spl3_139 | ~spl3_141 | ~spl3_145 | ~spl3_164)),
% 38.78/5.24    inference(forward_demodulation,[],[f7181,f5128])).
% 38.78/5.24  fof(f7181,plain,(
% 38.78/5.24    ( ! [X4] : (k5_xboole_0(sK1,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X4),sK1))) ) | (~spl3_8 | ~spl3_164)),
% 38.78/5.24    inference(superposition,[],[f7172,f68])).
% 38.78/5.24  fof(f6872,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X8,sK1)) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X8,sK1),sK1)))) ) | (~spl3_148 | ~spl3_163)),
% 38.78/5.24    inference(superposition,[],[f5637,f6834])).
% 38.78/5.24  fof(f5637,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK2),X1) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) ) | ~spl3_148),
% 38.78/5.24    inference(avatar_component_clause,[],[f5636])).
% 38.78/5.24  fof(f547,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) | spl3_45),
% 38.78/5.24    inference(avatar_component_clause,[],[f545])).
% 38.78/5.24  fof(f7269,plain,(
% 38.78/5.24    spl3_166 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134 | ~spl3_138 | ~spl3_142),
% 38.78/5.24    inference(avatar_split_clause,[],[f4875,f4831,f4447,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f7267])).
% 38.78/5.24  fof(f4875,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134 | ~spl3_138 | ~spl3_142)),
% 38.78/5.24    inference(forward_demodulation,[],[f4874,f3803])).
% 38.78/5.24  fof(f4874,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X2,sK1))) ) | (~spl3_138 | ~spl3_142)),
% 38.78/5.24    inference(forward_demodulation,[],[f4836,f4832])).
% 38.78/5.24  fof(f4836,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(X2,sK1)),sK1)) ) | (~spl3_138 | ~spl3_142)),
% 38.78/5.24    inference(superposition,[],[f4832,f4448])).
% 38.78/5.24  fof(f7265,plain,(
% 38.78/5.24    spl3_165 | ~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141),
% 38.78/5.24    inference(avatar_split_clause,[],[f4803,f4459,f4451,f3544,f2740,f2085,f1231,f945,f697,f584,f205,f63,f7263])).
% 38.78/5.24  fof(f4803,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.24    inference(backward_demodulation,[],[f4553,f4791])).
% 38.78/5.24  fof(f7173,plain,(
% 38.78/5.24    spl3_164 | ~spl3_58 | ~spl3_114 | ~spl3_158),
% 38.78/5.24    inference(avatar_split_clause,[],[f6769,f5950,f2732,f693,f7171])).
% 38.78/5.24  fof(f2732,plain,(
% 38.78/5.24    spl3_114 <=> ! [X3] : k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 38.78/5.24  fof(f6769,plain,(
% 38.78/5.24    ( ! [X3] : (k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK1))) ) | (~spl3_58 | ~spl3_114 | ~spl3_158)),
% 38.78/5.24    inference(backward_demodulation,[],[f2733,f6718])).
% 38.78/5.24  fof(f2733,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3))) ) | ~spl3_114),
% 38.78/5.24    inference(avatar_component_clause,[],[f2732])).
% 38.78/5.24  fof(f6835,plain,(
% 38.78/5.24    spl3_163 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_67 | ~spl3_89 | ~spl3_134 | ~spl3_158),
% 38.78/5.24    inference(avatar_split_clause,[],[f6824,f5950,f3688,f1718,f1025,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f6833])).
% 38.78/5.24  fof(f6824,plain,(
% 38.78/5.24    ( ! [X29] : (k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k4_xboole_0(k4_xboole_0(X29,sK1),sK1)) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_67 | ~spl3_89 | ~spl3_134 | ~spl3_158)),
% 38.78/5.24    inference(backward_demodulation,[],[f3893,f6744])).
% 38.78/5.24  fof(f3893,plain,(
% 38.78/5.24    ( ! [X29] : (k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k5_xboole_0(k4_xboole_0(X29,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X29))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_67 | ~spl3_89 | ~spl3_134)),
% 38.78/5.24    inference(forward_demodulation,[],[f3751,f3787])).
% 38.78/5.24  fof(f3787,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.24    inference(backward_demodulation,[],[f3689,f3772])).
% 38.78/5.24  fof(f3751,plain,(
% 38.78/5.24    ( ! [X29] : (k4_xboole_0(k4_xboole_0(X29,sK1),sK2) = k5_xboole_0(k4_xboole_0(X29,sK1),k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(sK1,sK1))))) ) | (~spl3_67 | ~spl3_134)),
% 38.78/5.24    inference(superposition,[],[f1026,f3689])).
% 38.78/5.24  fof(f5968,plain,(
% 38.78/5.24    spl3_162 | ~spl3_6 | ~spl3_7),
% 38.78/5.24    inference(avatar_split_clause,[],[f83,f63,f59,f5966])).
% 38.78/5.24  fof(f83,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2))))) ) | (~spl3_6 | ~spl3_7)),
% 38.78/5.24    inference(superposition,[],[f64,f60])).
% 38.78/5.24  fof(f5960,plain,(
% 38.78/5.24    spl3_160 | ~spl3_8 | ~spl3_62 | ~spl3_147),
% 38.78/5.24    inference(avatar_split_clause,[],[f5717,f5632,f811,f67,f5958])).
% 38.78/5.24  fof(f5717,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,X9),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9))) ) | (~spl3_8 | ~spl3_62 | ~spl3_147)),
% 38.78/5.24    inference(forward_demodulation,[],[f5648,f812])).
% 38.78/5.24  fof(f5648,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X9)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X9,k4_xboole_0(X9,sK1))),sK1)) ) | (~spl3_8 | ~spl3_147)),
% 38.78/5.24    inference(superposition,[],[f5633,f68])).
% 38.78/5.24  fof(f5952,plain,(
% 38.78/5.24    spl3_158 | ~spl3_23 | ~spl3_147),
% 38.78/5.24    inference(avatar_split_clause,[],[f5662,f5632,f205,f5950])).
% 38.78/5.24  fof(f5662,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X2,sK1)))) ) | (~spl3_23 | ~spl3_147)),
% 38.78/5.24    inference(superposition,[],[f5633,f206])).
% 38.78/5.24  fof(f5948,plain,(
% 38.78/5.24    spl3_157 | ~spl3_8 | ~spl3_147),
% 38.78/5.24    inference(avatar_split_clause,[],[f5658,f5632,f67,f5946])).
% 38.78/5.24  fof(f5658,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X7)) ) | (~spl3_8 | ~spl3_147)),
% 38.78/5.24    inference(superposition,[],[f5633,f68])).
% 38.78/5.24  fof(f5940,plain,(
% 38.78/5.24    spl3_155 | ~spl3_8 | ~spl3_120 | ~spl3_139 | ~spl3_141),
% 38.78/5.24    inference(avatar_split_clause,[],[f4769,f4459,f4451,f3184,f67,f5938])).
% 38.78/5.24  fof(f4769,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X9) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1)) ) | (~spl3_8 | ~spl3_120 | ~spl3_139 | ~spl3_141)),
% 38.78/5.24    inference(forward_demodulation,[],[f4728,f4768])).
% 38.78/5.24  fof(f4768,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,k4_xboole_0(X8,sK1)))) ) | (~spl3_8 | ~spl3_120 | ~spl3_139 | ~spl3_141)),
% 38.78/5.24    inference(forward_demodulation,[],[f4767,f4452])).
% 38.78/5.24  fof(f4767,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X8,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,k4_xboole_0(X8,sK1)))) ) | (~spl3_8 | ~spl3_120 | ~spl3_141)),
% 38.78/5.24    inference(forward_demodulation,[],[f4727,f3185])).
% 38.78/5.24  fof(f4727,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X8)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,k4_xboole_0(X8,sK1)))) ) | (~spl3_8 | ~spl3_141)),
% 38.78/5.24    inference(superposition,[],[f4460,f68])).
% 38.78/5.24  fof(f4728,plain,(
% 38.78/5.24    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X9)),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X9,k4_xboole_0(X9,sK1)))) ) | (~spl3_8 | ~spl3_141)),
% 38.78/5.24    inference(superposition,[],[f4460,f68])).
% 38.78/5.24  fof(f5932,plain,(
% 38.78/5.24    spl3_153 | ~spl3_8 | ~spl3_23 | ~spl3_55 | ~spl3_61 | ~spl3_63 | ~spl3_91 | ~spl3_103 | ~spl3_107),
% 38.78/5.24    inference(avatar_split_clause,[],[f4134,f2093,f2077,f1771,f815,f807,f681,f205,f67,f5930])).
% 38.78/5.24  fof(f2093,plain,(
% 38.78/5.24    spl3_107 <=> ! [X44,X43] : k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X43),X44)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_107])])).
% 38.78/5.24  fof(f4134,plain,(
% 38.78/5.24    ( ! [X16] : (k4_xboole_0(sK2,X16) = k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2))) ) | (~spl3_8 | ~spl3_23 | ~spl3_55 | ~spl3_61 | ~spl3_63 | ~spl3_91 | ~spl3_103 | ~spl3_107)),
% 38.78/5.24    inference(forward_demodulation,[],[f4133,f682])).
% 38.78/5.24  fof(f4133,plain,(
% 38.78/5.24    ( ! [X16] : (k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X16)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_61 | ~spl3_63 | ~spl3_91 | ~spl3_103 | ~spl3_107)),
% 38.78/5.24    inference(forward_demodulation,[],[f4060,f1845])).
% 38.78/5.24  fof(f4060,plain,(
% 38.78/5.24    ( ! [X16] : (k4_xboole_0(k4_xboole_0(sK1,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2)) = k4_xboole_0(k4_xboole_0(sK2,X16),k4_xboole_0(k4_xboole_0(sK1,X16),sK2))) ) | (~spl3_103 | ~spl3_107)),
% 38.78/5.24    inference(superposition,[],[f2078,f2094])).
% 38.78/5.24  fof(f2094,plain,(
% 38.78/5.24    ( ! [X43,X44] : (k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X43),X44)))) ) | ~spl3_107),
% 38.78/5.24    inference(avatar_component_clause,[],[f2093])).
% 38.78/5.24  fof(f5772,plain,(
% 38.78/5.24    spl3_149 | ~spl3_8 | ~spl3_62 | ~spl3_145 | ~spl3_147),
% 38.78/5.24    inference(avatar_split_clause,[],[f5716,f5632,f5017,f811,f67,f5770])).
% 38.78/5.24  fof(f5716,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,X8),sK1)) ) | (~spl3_8 | ~spl3_62 | ~spl3_145 | ~spl3_147)),
% 38.78/5.24    inference(forward_demodulation,[],[f5715,f812])).
% 38.78/5.24  fof(f5715,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X8) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X8,k4_xboole_0(X8,sK1))),sK1)) ) | (~spl3_8 | ~spl3_145 | ~spl3_147)),
% 38.78/5.24    inference(forward_demodulation,[],[f5647,f5018])).
% 38.78/5.24  fof(f5647,plain,(
% 38.78/5.24    ( ! [X8] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X8,k4_xboole_0(X8,sK1))),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X8))) ) | (~spl3_8 | ~spl3_147)),
% 38.78/5.24    inference(superposition,[],[f5633,f68])).
% 38.78/5.24  fof(f5638,plain,(
% 38.78/5.24    spl3_148 | ~spl3_7 | ~spl3_33 | ~spl3_53 | ~spl3_112 | ~spl3_146),
% 38.78/5.24    inference(avatar_split_clause,[],[f5622,f5575,f2724,f640,f331,f63,f5636])).
% 38.78/5.24  fof(f640,plain,(
% 38.78/5.24    spl3_53 <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 38.78/5.24  fof(f5575,plain,(
% 38.78/5.24    spl3_146 <=> ! [X3] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK2))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).
% 38.78/5.24  fof(f5622,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK2),X1) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) ) | (~spl3_7 | ~spl3_33 | ~spl3_53 | ~spl3_112 | ~spl3_146)),
% 38.78/5.24    inference(forward_demodulation,[],[f5621,f2939])).
% 38.78/5.24  fof(f2939,plain,(
% 38.78/5.24    ( ! [X61,X60] : (k4_xboole_0(k4_xboole_0(sK1,X60),X61) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X60),X61)))) ) | (~spl3_7 | ~spl3_112)),
% 38.78/5.24    inference(superposition,[],[f64,f2725])).
% 38.78/5.24  fof(f5621,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)))) ) | (~spl3_33 | ~spl3_53 | ~spl3_112 | ~spl3_146)),
% 38.78/5.24    inference(forward_demodulation,[],[f5591,f2921])).
% 38.78/5.24  fof(f2921,plain,(
% 38.78/5.24    ( ! [X6,X5] : (k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X5),X6))) ) | (~spl3_33 | ~spl3_112)),
% 38.78/5.24    inference(superposition,[],[f332,f2725])).
% 38.78/5.24  fof(f5591,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)))) ) | (~spl3_53 | ~spl3_146)),
% 38.78/5.24    inference(superposition,[],[f641,f5576])).
% 38.78/5.24  fof(f5576,plain,(
% 38.78/5.24    ( ! [X3] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK2))) ) | ~spl3_146),
% 38.78/5.24    inference(avatar_component_clause,[],[f5575])).
% 38.78/5.24  fof(f641,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ) | ~spl3_53),
% 38.78/5.24    inference(avatar_component_clause,[],[f640])).
% 38.78/5.24  fof(f5634,plain,(
% 38.78/5.24    spl3_147 | ~spl3_113 | ~spl3_137),
% 38.78/5.24    inference(avatar_split_clause,[],[f5196,f4268,f2728,f5632])).
% 38.78/5.24  fof(f5196,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK1)) ) | (~spl3_113 | ~spl3_137)),
% 38.78/5.24    inference(superposition,[],[f2729,f4269])).
% 38.78/5.24  fof(f5577,plain,(
% 38.78/5.24    spl3_146 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_23 | ~spl3_113),
% 38.78/5.24    inference(avatar_split_clause,[],[f5392,f2728,f205,f75,f67,f63,f5575])).
% 38.78/5.24  fof(f75,plain,(
% 38.78/5.24    spl3_9 <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 38.78/5.24  fof(f5392,plain,(
% 38.78/5.24    ( ! [X3] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(sK1,k4_xboole_0(X3,sK2))) ) | (~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_23 | ~spl3_113)),
% 38.78/5.24    inference(forward_demodulation,[],[f5379,f64])).
% 38.78/5.24  fof(f5379,plain,(
% 38.78/5.24    ( ! [X3] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X3,sK2))))) ) | (~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_23 | ~spl3_113)),
% 38.78/5.24    inference(backward_demodulation,[],[f85,f5372])).
% 38.78/5.24  fof(f85,plain,(
% 38.78/5.24    ( ! [X3] : (k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X3))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),X3))) ) | (~spl3_7 | ~spl3_9)),
% 38.78/5.24    inference(superposition,[],[f76,f64])).
% 38.78/5.24  fof(f76,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0)) ) | ~spl3_9),
% 38.78/5.24    inference(avatar_component_clause,[],[f75])).
% 38.78/5.24  fof(f5019,plain,(
% 38.78/5.24    spl3_145 | ~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141),
% 38.78/5.24    inference(avatar_split_clause,[],[f4802,f4459,f4451,f3544,f2740,f2085,f1231,f945,f697,f584,f205,f63,f5017])).
% 38.78/5.24  fof(f4925,plain,(
% 38.78/5.24    spl3_143 | ~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_78 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141),
% 38.78/5.24    inference(avatar_split_clause,[],[f4792,f4459,f4451,f3544,f2740,f2085,f1427,f1231,f945,f697,f584,f205,f63,f4923])).
% 38.78/5.24  fof(f4792,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)) ) | (~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_78 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141)),
% 38.78/5.24    inference(backward_demodulation,[],[f1428,f4791])).
% 38.78/5.24  fof(f4833,plain,(
% 38.78/5.24    spl3_142 | ~spl3_7 | ~spl3_23 | ~spl3_50 | ~spl3_59 | ~spl3_64 | ~spl3_71 | ~spl3_105 | ~spl3_116 | ~spl3_128 | ~spl3_139 | ~spl3_141),
% 38.78/5.24    inference(avatar_split_clause,[],[f4791,f4459,f4451,f3544,f2740,f2085,f1231,f945,f697,f584,f205,f63,f4831])).
% 38.78/5.24  fof(f4461,plain,(
% 38.78/5.24    spl3_141 | ~spl3_91 | ~spl3_135),
% 38.78/5.24    inference(avatar_split_clause,[],[f3922,f3909,f1771,f4459])).
% 38.78/5.24  fof(f3909,plain,(
% 38.78/5.24    spl3_135 <=> ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).
% 38.78/5.24  fof(f3922,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1))) ) | (~spl3_91 | ~spl3_135)),
% 38.78/5.24    inference(superposition,[],[f3910,f1772])).
% 38.78/5.24  fof(f3910,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))) ) | ~spl3_135),
% 38.78/5.24    inference(avatar_component_clause,[],[f3909])).
% 38.78/5.24  fof(f4457,plain,(
% 38.78/5.24    spl3_140 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134),
% 38.78/5.24    inference(avatar_split_clause,[],[f3826,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4455])).
% 38.78/5.24  fof(f3826,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(sK1,sK1),X7))) ) | (~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134)),
% 38.78/5.24    inference(forward_demodulation,[],[f3709,f3772])).
% 38.78/5.24  fof(f3709,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(X7,k4_xboole_0(sK1,sK1)) = k5_xboole_0(X7,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK1))))) ) | (~spl3_7 | ~spl3_134)),
% 38.78/5.24    inference(superposition,[],[f64,f3689])).
% 38.78/5.24  fof(f4453,plain,(
% 38.78/5.24    spl3_139 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134),
% 38.78/5.24    inference(avatar_split_clause,[],[f3804,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4451])).
% 38.78/5.24  fof(f4449,plain,(
% 38.78/5.24    spl3_138 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134),
% 38.78/5.24    inference(avatar_split_clause,[],[f3771,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4447])).
% 38.78/5.24  fof(f4270,plain,(
% 38.78/5.24    spl3_137 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134),
% 38.78/5.24    inference(avatar_split_clause,[],[f3787,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f4268])).
% 38.78/5.24  fof(f3911,plain,(
% 38.78/5.24    spl3_135 | ~spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_61 | ~spl3_65 | ~spl3_89 | ~spl3_134),
% 38.78/5.24    inference(avatar_split_clause,[],[f3772,f3688,f1718,f949,f807,f681,f478,f393,f388,f384,f100,f93,f88,f67,f63,f3909])).
% 38.78/5.24  fof(f3690,plain,(
% 38.78/5.24    spl3_134 | ~spl3_8 | ~spl3_23 | ~spl3_62 | ~spl3_63 | ~spl3_89 | ~spl3_126),
% 38.78/5.24    inference(avatar_split_clause,[],[f3462,f3412,f1718,f815,f811,f205,f67,f3688])).
% 38.78/5.24  fof(f3412,plain,(
% 38.78/5.24    spl3_126 <=> ! [X2] : k4_xboole_0(sK2,k4_xboole_0(X2,sK1)) = k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK1,X2)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_126])])).
% 38.78/5.24  fof(f3462,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,sK1)))) ) | (~spl3_8 | ~spl3_23 | ~spl3_62 | ~spl3_63 | ~spl3_89 | ~spl3_126)),
% 38.78/5.24    inference(backward_demodulation,[],[f1723,f3459])).
% 38.78/5.24  fof(f3459,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) ) | (~spl3_23 | ~spl3_62 | ~spl3_63 | ~spl3_126)),
% 38.78/5.24    inference(forward_demodulation,[],[f3458,f3413])).
% 38.78/5.24  fof(f3413,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(X2,sK1)) = k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK1,X2)))) ) | ~spl3_126),
% 38.78/5.24    inference(avatar_component_clause,[],[f3412])).
% 38.78/5.24  fof(f3458,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) ) | (~spl3_23 | ~spl3_62 | ~spl3_63 | ~spl3_126)),
% 38.78/5.24    inference(forward_demodulation,[],[f3457,f206])).
% 38.78/5.24  fof(f3457,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK1))) ) | (~spl3_62 | ~spl3_63 | ~spl3_126)),
% 38.78/5.24    inference(forward_demodulation,[],[f3415,f812])).
% 38.78/5.24  fof(f3415,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))))) ) | (~spl3_63 | ~spl3_126)),
% 38.78/5.24    inference(superposition,[],[f3413,f816])).
% 38.78/5.24  fof(f1723,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))))) ) | (~spl3_8 | ~spl3_89)),
% 38.78/5.24    inference(superposition,[],[f1719,f68])).
% 38.78/5.24  fof(f3546,plain,(
% 38.78/5.24    spl3_128 | ~spl3_6 | ~spl3_127),
% 38.78/5.24    inference(avatar_split_clause,[],[f3540,f3534,f59,f3544])).
% 38.78/5.24  fof(f3534,plain,(
% 38.78/5.24    spl3_127 <=> sK2 = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_127])])).
% 38.78/5.24  fof(f3540,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(k4_xboole_0(sK1,sK1),k5_xboole_0(sK2,X0))) ) | (~spl3_6 | ~spl3_127)),
% 38.78/5.24    inference(superposition,[],[f60,f3536])).
% 38.78/5.24  fof(f3536,plain,(
% 38.78/5.24    sK2 = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2) | ~spl3_127),
% 38.78/5.24    inference(avatar_component_clause,[],[f3534])).
% 38.78/5.24  fof(f3537,plain,(
% 38.78/5.24    spl3_127 | ~spl3_48 | ~spl3_49 | ~spl3_51 | ~spl3_61 | ~spl3_126),
% 38.78/5.24    inference(avatar_split_clause,[],[f3504,f3412,f807,f589,f579,f574,f3534])).
% 38.78/5.24  fof(f574,plain,(
% 38.78/5.24    spl3_48 <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 38.78/5.24  fof(f589,plain,(
% 38.78/5.24    spl3_51 <=> k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 38.78/5.24  fof(f3504,plain,(
% 38.78/5.24    sK2 = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2) | (~spl3_48 | ~spl3_49 | ~spl3_51 | ~spl3_61 | ~spl3_126)),
% 38.78/5.24    inference(forward_demodulation,[],[f3503,f581])).
% 38.78/5.24  fof(f3503,plain,(
% 38.78/5.24    k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2) | (~spl3_48 | ~spl3_51 | ~spl3_61 | ~spl3_126)),
% 38.78/5.24    inference(forward_demodulation,[],[f3502,f808])).
% 38.78/5.24  fof(f3502,plain,(
% 38.78/5.24    k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK1),sK2) | (~spl3_48 | ~spl3_51 | ~spl3_126)),
% 38.78/5.24    inference(forward_demodulation,[],[f3433,f576])).
% 38.78/5.24  fof(f576,plain,(
% 38.78/5.24    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_48),
% 38.78/5.24    inference(avatar_component_clause,[],[f574])).
% 38.78/5.24  fof(f3433,plain,(
% 38.78/5.24    k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) | (~spl3_51 | ~spl3_126)),
% 38.78/5.24    inference(superposition,[],[f3413,f591])).
% 38.78/5.24  fof(f591,plain,(
% 38.78/5.24    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1) | ~spl3_51),
% 38.78/5.24    inference(avatar_component_clause,[],[f589])).
% 38.78/5.24  fof(f3414,plain,(
% 38.78/5.24    spl3_126 | ~spl3_61 | ~spl3_80 | ~spl3_88 | ~spl3_106 | ~spl3_125),
% 38.78/5.24    inference(avatar_split_clause,[],[f3365,f3204,f2089,f1667,f1487,f807,f3412])).
% 38.78/5.24  fof(f1487,plain,(
% 38.78/5.24    spl3_80 <=> ! [X6] : k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 38.78/5.24  fof(f3365,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(X2,sK1)) = k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK1,X2)))) ) | (~spl3_61 | ~spl3_80 | ~spl3_88 | ~spl3_106 | ~spl3_125)),
% 38.78/5.24    inference(forward_demodulation,[],[f3364,f808])).
% 38.78/5.24  fof(f3364,plain,(
% 38.78/5.24    ( ! [X2] : (k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) = k4_xboole_0(sK2,k4_xboole_0(X2,sK1))) ) | (~spl3_80 | ~spl3_88 | ~spl3_106 | ~spl3_125)),
% 38.78/5.24    inference(forward_demodulation,[],[f3363,f3205])).
% 38.78/5.24  fof(f3363,plain,(
% 38.78/5.24    ( ! [X2] : (k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X2)),sK1))) ) | (~spl3_80 | ~spl3_88 | ~spl3_106)),
% 38.78/5.24    inference(forward_demodulation,[],[f3270,f2090])).
% 38.78/5.24  fof(f3270,plain,(
% 38.78/5.24    ( ! [X2] : (k5_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X2)),sK1))) ) | (~spl3_80 | ~spl3_88)),
% 38.78/5.24    inference(superposition,[],[f1668,f1488])).
% 38.78/5.24  fof(f1488,plain,(
% 38.78/5.24    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6))) ) | ~spl3_80),
% 38.78/5.24    inference(avatar_component_clause,[],[f1487])).
% 38.78/5.24  fof(f3206,plain,(
% 38.78/5.24    spl3_125 | ~spl3_23 | ~spl3_59 | ~spl3_61 | ~spl3_106),
% 38.78/5.24    inference(avatar_split_clause,[],[f2507,f2089,f807,f697,f205,f3204])).
% 38.78/5.24  fof(f2507,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(X7,X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8))) ) | (~spl3_23 | ~spl3_59 | ~spl3_61 | ~spl3_106)),
% 38.78/5.24    inference(forward_demodulation,[],[f2506,f698])).
% 38.78/5.24  fof(f2506,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X7,X8))))) ) | (~spl3_23 | ~spl3_61 | ~spl3_106)),
% 38.78/5.24    inference(forward_demodulation,[],[f2505,f206])).
% 38.78/5.24  fof(f2505,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X7)),X8))) ) | (~spl3_61 | ~spl3_106)),
% 38.78/5.24    inference(forward_demodulation,[],[f2477,f2090])).
% 38.78/5.24  fof(f2477,plain,(
% 38.78/5.24    ( ! [X8,X7] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,X7)),X8)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,X7)),X8))) ) | (~spl3_61 | ~spl3_106)),
% 38.78/5.24    inference(superposition,[],[f2090,f808])).
% 38.78/5.24  fof(f3194,plain,(
% 38.78/5.24    spl3_122 | ~spl3_61 | ~spl3_91),
% 38.78/5.24    inference(avatar_split_clause,[],[f1805,f1771,f807,f3192])).
% 38.78/5.24  fof(f1805,plain,(
% 38.78/5.24    ( ! [X4,X3] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X3),X4))) = k4_xboole_0(k4_xboole_0(sK2,X3),X4)) ) | (~spl3_61 | ~spl3_91)),
% 38.78/5.24    inference(superposition,[],[f1772,f808])).
% 38.78/5.24  fof(f3186,plain,(
% 38.78/5.24    spl3_120 | ~spl3_23 | ~spl3_61),
% 38.78/5.24    inference(avatar_split_clause,[],[f872,f807,f205,f3184])).
% 38.78/5.24  fof(f2742,plain,(
% 38.78/5.24    spl3_116 | ~spl3_55 | ~spl3_91),
% 38.78/5.24    inference(avatar_split_clause,[],[f1811,f1771,f681,f2740])).
% 38.78/5.24  fof(f1811,plain,(
% 38.78/5.24    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK2,X9),X10) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X9),X10)))) ) | (~spl3_55 | ~spl3_91)),
% 38.78/5.24    inference(superposition,[],[f682,f1772])).
% 38.78/5.24  fof(f2734,plain,(
% 38.78/5.24    spl3_114 | ~spl3_54 | ~spl3_89),
% 38.78/5.24    inference(avatar_split_clause,[],[f1735,f1718,f677,f2732])).
% 38.78/5.24  fof(f677,plain,(
% 38.78/5.24    spl3_54 <=> ! [X5] : k4_xboole_0(sK1,k4_xboole_0(sK2,X5)) = k5_xboole_0(sK1,k4_xboole_0(sK2,X5))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 38.78/5.24  fof(f1735,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),X3))) ) | (~spl3_54 | ~spl3_89)),
% 38.78/5.24    inference(superposition,[],[f678,f1719])).
% 38.78/5.24  fof(f678,plain,(
% 38.78/5.24    ( ! [X5] : (k4_xboole_0(sK1,k4_xboole_0(sK2,X5)) = k5_xboole_0(sK1,k4_xboole_0(sK2,X5))) ) | ~spl3_54),
% 38.78/5.24    inference(avatar_component_clause,[],[f677])).
% 38.78/5.24  fof(f2730,plain,(
% 38.78/5.24    spl3_113 | ~spl3_8 | ~spl3_23),
% 38.78/5.24    inference(avatar_split_clause,[],[f344,f205,f67,f2728])).
% 38.78/5.24  fof(f344,plain,(
% 38.78/5.24    ( ! [X2,X3,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3)) ) | (~spl3_8 | ~spl3_23)),
% 38.78/5.24    inference(superposition,[],[f206,f68])).
% 38.78/5.24  fof(f2726,plain,(
% 38.78/5.24    spl3_112 | ~spl3_23 | ~spl3_58),
% 38.78/5.24    inference(avatar_split_clause,[],[f781,f693,f205,f2724])).
% 38.78/5.24  fof(f781,plain,(
% 38.78/5.24    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(sK1,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X1),X2)))) ) | (~spl3_23 | ~spl3_58)),
% 38.78/5.24    inference(superposition,[],[f206,f694])).
% 38.78/5.24  fof(f2095,plain,(
% 38.78/5.24    spl3_107 | ~spl3_7 | ~spl3_55 | ~spl3_61 | ~spl3_91),
% 38.78/5.24    inference(avatar_split_clause,[],[f1873,f1771,f807,f681,f63,f2093])).
% 38.78/5.24  fof(f1873,plain,(
% 38.78/5.24    ( ! [X43,X44] : (k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X43),X44)))) ) | (~spl3_7 | ~spl3_55 | ~spl3_61 | ~spl3_91)),
% 38.78/5.24    inference(forward_demodulation,[],[f1823,f1867])).
% 38.78/5.24  fof(f1867,plain,(
% 38.78/5.24    ( ! [X14,X13] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X13),X14)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X13),X14))) ) | (~spl3_55 | ~spl3_61 | ~spl3_91)),
% 38.78/5.24    inference(forward_demodulation,[],[f1813,f682])).
% 38.78/5.24  fof(f1813,plain,(
% 38.78/5.24    ( ! [X14,X13] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X13),X14)))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X13),X14))) ) | (~spl3_61 | ~spl3_91)),
% 38.78/5.24    inference(superposition,[],[f808,f1772])).
% 38.78/5.24  fof(f1823,plain,(
% 38.78/5.24    ( ! [X43,X44] : (k4_xboole_0(k4_xboole_0(sK2,X43),X44) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X43),X44)))) ) | (~spl3_7 | ~spl3_91)),
% 38.78/5.24    inference(superposition,[],[f64,f1772])).
% 38.78/5.24  fof(f2091,plain,(
% 38.78/5.24    spl3_106 | ~spl3_38 | ~spl3_55 | ~spl3_91),
% 38.78/5.24    inference(avatar_split_clause,[],[f1866,f1771,f681,f393,f2089])).
% 38.78/5.24  fof(f1866,plain,(
% 38.78/5.24    ( ! [X6,X5] : (k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6))) ) | (~spl3_38 | ~spl3_55 | ~spl3_91)),
% 38.78/5.24    inference(forward_demodulation,[],[f1809,f682])).
% 38.78/5.24  fof(f1809,plain,(
% 38.78/5.24    ( ! [X6,X5] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X5),X6)))) = k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X5),X6))) ) | (~spl3_38 | ~spl3_91)),
% 38.78/5.24    inference(superposition,[],[f394,f1772])).
% 38.78/5.24  fof(f2087,plain,(
% 38.78/5.24    spl3_105 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_20 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_89),
% 38.78/5.24    inference(avatar_split_clause,[],[f1760,f1718,f681,f478,f393,f388,f384,f174,f100,f93,f88,f63,f2085])).
% 38.78/5.24  fof(f174,plain,(
% 38.78/5.24    spl3_20 <=> ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(k4_xboole_0(sK2,sK1),X0)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 38.78/5.24  fof(f1760,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_20 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41 | ~spl3_55 | ~spl3_89)),
% 38.78/5.24    inference(backward_demodulation,[],[f506,f1759])).
% 38.78/5.24  fof(f506,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X1) = k5_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X1)))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_20 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41)),
% 38.78/5.24    inference(backward_demodulation,[],[f450,f495])).
% 38.78/5.24  fof(f450,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,sK1),X1) = k5_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X1)))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_20 | ~spl3_37 | ~spl3_38)),
% 38.78/5.24    inference(backward_demodulation,[],[f192,f443])).
% 38.78/5.24  fof(f192,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,sK1),X1) = k5_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK2,sK1),X1))))) ) | (~spl3_7 | ~spl3_20)),
% 38.78/5.24    inference(superposition,[],[f175,f64])).
% 38.78/5.24  fof(f175,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(k4_xboole_0(sK2,sK1),X0)) ) | ~spl3_20),
% 38.78/5.24    inference(avatar_component_clause,[],[f174])).
% 38.78/5.24  fof(f2079,plain,(
% 38.78/5.24    spl3_103 | ~spl3_7 | ~spl3_8),
% 38.78/5.24    inference(avatar_split_clause,[],[f107,f67,f63,f2077])).
% 38.78/5.24  fof(f107,plain,(
% 38.78/5.24    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) ) | (~spl3_7 | ~spl3_8)),
% 38.78/5.24    inference(superposition,[],[f64,f68])).
% 38.78/5.24  fof(f2051,plain,(
% 38.78/5.24    spl3_96 | ~spl3_23 | ~spl3_36),
% 38.78/5.24    inference(avatar_split_clause,[],[f401,f384,f205,f2049])).
% 38.78/5.24  fof(f401,plain,(
% 38.78/5.24    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,X1),X2)))) ) | (~spl3_23 | ~spl3_36)),
% 38.78/5.24    inference(superposition,[],[f206,f385])).
% 38.78/5.24  fof(f2047,plain,(
% 38.78/5.24    spl3_95 | ~spl3_8 | ~spl3_36),
% 38.78/5.24    inference(avatar_split_clause,[],[f398,f384,f67,f2045])).
% 38.78/5.24  fof(f398,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1,k4_xboole_0(X1,sK2))))) ) | (~spl3_8 | ~spl3_36)),
% 38.78/5.24    inference(superposition,[],[f385,f68])).
% 38.78/5.24  fof(f1877,plain,(
% 38.78/5.24    spl3_94 | ~spl3_7 | ~spl3_34 | ~spl3_35 | ~spl3_91),
% 38.78/5.24    inference(avatar_split_clause,[],[f1851,f1771,f371,f335,f63,f1875])).
% 38.78/5.24  fof(f1851,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(sK2,X7) = k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1))) ) | (~spl3_7 | ~spl3_34 | ~spl3_35 | ~spl3_91)),
% 38.78/5.24    inference(forward_demodulation,[],[f1850,f372])).
% 38.78/5.24  fof(f1850,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X7)))) ) | (~spl3_7 | ~spl3_34 | ~spl3_91)),
% 38.78/5.24    inference(forward_demodulation,[],[f1797,f64])).
% 38.78/5.24  fof(f1797,plain,(
% 38.78/5.24    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK2,X7),k4_xboole_0(k4_xboole_0(sK1,X7),sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X7)))))) ) | (~spl3_34 | ~spl3_91)),
% 38.78/5.24    inference(superposition,[],[f1772,f336])).
% 38.78/5.24  fof(f1777,plain,(
% 38.78/5.24    spl3_92 | ~spl3_7 | ~spl3_16 | ~spl3_36 | ~spl3_38 | ~spl3_55),
% 38.78/5.24    inference(avatar_split_clause,[],[f732,f681,f393,f384,f133,f63,f1775])).
% 38.78/5.24  fof(f133,plain,(
% 38.78/5.24    spl3_16 <=> ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 38.78/5.24  fof(f732,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,X1)))) ) | (~spl3_7 | ~spl3_16 | ~spl3_36 | ~spl3_38 | ~spl3_55)),
% 38.78/5.24    inference(backward_demodulation,[],[f409,f729])).
% 38.78/5.24  fof(f729,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) ) | (~spl3_36 | ~spl3_38 | ~spl3_55)),
% 38.78/5.24    inference(forward_demodulation,[],[f728,f385])).
% 38.78/5.24  fof(f728,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X2))))) ) | (~spl3_38 | ~spl3_55)),
% 38.78/5.24    inference(forward_demodulation,[],[f722,f394])).
% 38.78/5.24  fof(f722,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X2)))) = k5_xboole_0(sK2,k4_xboole_0(sK2,X2))) ) | (~spl3_38 | ~spl3_55)),
% 38.78/5.24    inference(superposition,[],[f394,f682])).
% 38.78/5.24  fof(f409,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))) ) | (~spl3_7 | ~spl3_16 | ~spl3_36)),
% 38.78/5.24    inference(forward_demodulation,[],[f406,f402])).
% 38.78/5.24  fof(f402,plain,(
% 38.78/5.24    ( ! [X5] : (k4_xboole_0(sK1,k4_xboole_0(sK2,X5)) = k5_xboole_0(sK1,k4_xboole_0(sK2,X5))) ) | (~spl3_7 | ~spl3_36)),
% 38.78/5.24    inference(superposition,[],[f64,f385])).
% 38.78/5.24  fof(f406,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))) ) | (~spl3_7 | ~spl3_16 | ~spl3_36)),
% 38.78/5.24    inference(backward_demodulation,[],[f140,f402])).
% 38.78/5.24  fof(f140,plain,(
% 38.78/5.24    ( ! [X1] : (k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k4_xboole_0(sK2,X1)))) ) | (~spl3_7 | ~spl3_16)),
% 38.78/5.24    inference(superposition,[],[f134,f64])).
% 38.78/5.24  fof(f134,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | ~spl3_16),
% 38.78/5.24    inference(avatar_component_clause,[],[f133])).
% 38.78/5.24  fof(f1773,plain,(
% 38.78/5.24    spl3_91 | ~spl3_23 | ~spl3_35),
% 38.78/5.24    inference(avatar_split_clause,[],[f378,f371,f205,f1771])).
% 38.78/5.24  fof(f378,plain,(
% 38.78/5.24    ( ! [X2,X1] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X1),X2))) = k4_xboole_0(k4_xboole_0(sK2,X1),X2)) ) | (~spl3_23 | ~spl3_35)),
% 38.78/5.24    inference(superposition,[],[f206,f372])).
% 38.78/5.24  fof(f1720,plain,(
% 38.78/5.24    spl3_89 | ~spl3_5 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41),
% 38.78/5.24    inference(avatar_split_clause,[],[f505,f478,f393,f388,f384,f205,f93,f88,f63,f54,f1718])).
% 38.78/5.24  fof(f54,plain,(
% 38.78/5.24    spl3_5 <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 38.78/5.24  fof(f505,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41)),
% 38.78/5.24    inference(backward_demodulation,[],[f447,f495])).
% 38.78/5.24  fof(f447,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK2,sK1),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_37 | ~spl3_38)),
% 38.78/5.24    inference(backward_demodulation,[],[f338,f440])).
% 38.78/5.24  fof(f338,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK2,sK2),X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK1),X0)))) ) | (~spl3_5 | ~spl3_23)),
% 38.78/5.24    inference(superposition,[],[f206,f56])).
% 38.78/5.24  fof(f56,plain,(
% 38.78/5.24    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | ~spl3_5),
% 38.78/5.24    inference(avatar_component_clause,[],[f54])).
% 38.78/5.24  fof(f1669,plain,(
% 38.78/5.24    spl3_88 | ~spl3_6 | ~spl3_7),
% 38.78/5.24    inference(avatar_split_clause,[],[f84,f63,f59,f1667])).
% 38.78/5.24  fof(f84,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)) ) | (~spl3_6 | ~spl3_7)),
% 38.78/5.24    inference(superposition,[],[f60,f64])).
% 38.78/5.24  fof(f1665,plain,(
% 38.78/5.24    spl3_87 | ~spl3_55 | ~spl3_64 | ~spl3_78),
% 38.78/5.24    inference(avatar_split_clause,[],[f1469,f1427,f945,f681,f1663])).
% 38.78/5.24  fof(f1469,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,X2) = k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1))) ) | (~spl3_55 | ~spl3_64 | ~spl3_78)),
% 38.78/5.24    inference(forward_demodulation,[],[f1447,f682])).
% 38.78/5.24  fof(f1447,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK2,X2),k4_xboole_0(k4_xboole_0(sK2,X2),sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X2)))) ) | (~spl3_64 | ~spl3_78)),
% 38.78/5.24    inference(superposition,[],[f946,f1428])).
% 38.78/5.24  fof(f1489,plain,(
% 38.78/5.24    spl3_80 | ~spl3_36 | ~spl3_67),
% 38.78/5.24    inference(avatar_split_clause,[],[f1340,f1025,f384,f1487])).
% 38.78/5.24  fof(f1340,plain,(
% 38.78/5.24    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK2,X6),sK1) = k5_xboole_0(k4_xboole_0(sK2,X6),k4_xboole_0(sK2,X6))) ) | (~spl3_36 | ~spl3_67)),
% 38.78/5.24    inference(superposition,[],[f1026,f385])).
% 38.78/5.24  fof(f1429,plain,(
% 38.78/5.24    spl3_78 | ~spl3_36 | ~spl3_67 | ~spl3_76),
% 38.78/5.24    inference(avatar_split_clause,[],[f1392,f1307,f1025,f384,f1427])).
% 38.78/5.24  fof(f1307,plain,(
% 38.78/5.24    spl3_76 <=> ! [X1] : k4_xboole_0(k4_xboole_0(sK2,X1),sK2) = k5_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(sK2,X1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 38.78/5.24  fof(f1392,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),sK1) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2)) ) | (~spl3_36 | ~spl3_67 | ~spl3_76)),
% 38.78/5.24    inference(backward_demodulation,[],[f1308,f1340])).
% 38.78/5.24  fof(f1308,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),sK2) = k5_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(sK2,X1))) ) | ~spl3_76),
% 38.78/5.24    inference(avatar_component_clause,[],[f1307])).
% 38.78/5.24  fof(f1309,plain,(
% 38.78/5.24    spl3_76 | ~spl3_55 | ~spl3_69),
% 38.78/5.24    inference(avatar_split_clause,[],[f1156,f1139,f681,f1307])).
% 38.78/5.24  fof(f1156,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK2,X1),sK2) = k5_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(sK2,X1))) ) | (~spl3_55 | ~spl3_69)),
% 38.78/5.24    inference(superposition,[],[f1140,f682])).
% 38.78/5.24  fof(f1234,plain,(
% 38.78/5.24    spl3_71 | ~spl3_50 | ~spl3_54 | ~spl3_59 | ~spl3_60 | ~spl3_68 | ~spl3_69),
% 38.78/5.24    inference(avatar_split_clause,[],[f1196,f1139,f1135,f803,f697,f677,f584,f1231])).
% 38.78/5.24  fof(f803,plain,(
% 38.78/5.24    spl3_60 <=> ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X3)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 38.78/5.24  fof(f1135,plain,(
% 38.78/5.24    spl3_68 <=> ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK1,sK1),X0)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 38.78/5.24  fof(f1196,plain,(
% 38.78/5.24    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) | (~spl3_50 | ~spl3_54 | ~spl3_59 | ~spl3_60 | ~spl3_68 | ~spl3_69)),
% 38.78/5.24    inference(forward_demodulation,[],[f1195,f586])).
% 38.78/5.24  fof(f1195,plain,(
% 38.78/5.24    k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) | (~spl3_54 | ~spl3_59 | ~spl3_60 | ~spl3_68 | ~spl3_69)),
% 38.78/5.24    inference(forward_demodulation,[],[f1194,f804])).
% 38.78/5.24  fof(f804,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X3)))) ) | ~spl3_60),
% 38.78/5.24    inference(avatar_component_clause,[],[f803])).
% 38.78/5.24  fof(f1194,plain,(
% 38.78/5.24    k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) | (~spl3_54 | ~spl3_59 | ~spl3_68 | ~spl3_69)),
% 38.78/5.24    inference(forward_demodulation,[],[f1193,f698])).
% 38.78/5.24  fof(f1193,plain,(
% 38.78/5.24    k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))))) | (~spl3_54 | ~spl3_68 | ~spl3_69)),
% 38.78/5.24    inference(forward_demodulation,[],[f1163,f678])).
% 38.78/5.24  fof(f1163,plain,(
% 38.78/5.24    k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))))) | (~spl3_68 | ~spl3_69)),
% 38.78/5.24    inference(superposition,[],[f1140,f1136])).
% 38.78/5.24  fof(f1136,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK1,sK1),X0)) ) | ~spl3_68),
% 38.78/5.24    inference(avatar_component_clause,[],[f1135])).
% 38.78/5.24  fof(f1141,plain,(
% 38.78/5.24    spl3_69 | ~spl3_7 | ~spl3_64),
% 38.78/5.24    inference(avatar_split_clause,[],[f975,f945,f63,f1139])).
% 38.78/5.24  fof(f975,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(X4,sK2) = k5_xboole_0(X4,k4_xboole_0(sK2,k4_xboole_0(sK1,X4)))) ) | (~spl3_7 | ~spl3_64)),
% 38.78/5.24    inference(superposition,[],[f64,f946])).
% 38.78/5.24  fof(f1137,plain,(
% 38.78/5.24    spl3_68 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_32 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41),
% 38.78/5.24    inference(avatar_split_clause,[],[f504,f478,f393,f388,f384,f327,f93,f88,f63,f1135])).
% 38.78/5.24  fof(f327,plain,(
% 38.78/5.24    spl3_32 <=> ! [X0] : k5_xboole_0(k4_xboole_0(sK2,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 38.78/5.24  fof(f504,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK1,sK1),X0)) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_32 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41)),
% 38.78/5.24    inference(backward_demodulation,[],[f446,f495])).
% 38.78/5.24  fof(f446,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK2,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_32 | ~spl3_37 | ~spl3_38)),
% 38.78/5.24    inference(backward_demodulation,[],[f328,f440])).
% 38.78/5.24  fof(f328,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK2,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ) | ~spl3_32),
% 38.78/5.24    inference(avatar_component_clause,[],[f327])).
% 38.78/5.24  fof(f1027,plain,(
% 38.78/5.24    spl3_67 | ~spl3_7 | ~spl3_8),
% 38.78/5.24    inference(avatar_split_clause,[],[f106,f67,f63,f1025])).
% 38.78/5.24  fof(f106,plain,(
% 38.78/5.24    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl3_7 | ~spl3_8)),
% 38.78/5.24    inference(superposition,[],[f64,f68])).
% 38.78/5.24  fof(f955,plain,(
% 38.78/5.24    spl3_66 | ~spl3_8 | ~spl3_55 | ~spl3_61),
% 38.78/5.24    inference(avatar_split_clause,[],[f867,f807,f681,f67,f953])).
% 38.78/5.24  fof(f867,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(sK2,X4) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2)))) ) | (~spl3_8 | ~spl3_55 | ~spl3_61)),
% 38.78/5.24    inference(forward_demodulation,[],[f844,f682])).
% 38.78/5.24  fof(f844,plain,(
% 38.78/5.24    ( ! [X4] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X4))) = k4_xboole_0(sK2,k4_xboole_0(X4,k4_xboole_0(X4,sK2)))) ) | (~spl3_8 | ~spl3_61)),
% 38.78/5.24    inference(superposition,[],[f808,f68])).
% 38.78/5.24  fof(f951,plain,(
% 38.78/5.24    spl3_65 | ~spl3_7 | ~spl3_61),
% 38.78/5.24    inference(avatar_split_clause,[],[f859,f807,f63,f949])).
% 38.78/5.24  fof(f859,plain,(
% 38.78/5.24    ( ! [X10] : (k4_xboole_0(sK2,X10) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X10)))) ) | (~spl3_7 | ~spl3_61)),
% 38.78/5.24    inference(superposition,[],[f64,f808])).
% 38.78/5.24  fof(f947,plain,(
% 38.78/5.24    spl3_64 | ~spl3_8 | ~spl3_61),
% 38.78/5.24    inference(avatar_split_clause,[],[f848,f807,f67,f945])).
% 38.78/5.24  fof(f848,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sK2))) ) | (~spl3_8 | ~spl3_61)),
% 38.78/5.24    inference(superposition,[],[f808,f68])).
% 38.78/5.24  fof(f817,plain,(
% 38.78/5.24    spl3_63 | ~spl3_8 | ~spl3_59),
% 38.78/5.24    inference(avatar_split_clause,[],[f788,f697,f67,f815])).
% 38.78/5.24  fof(f788,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK2,X2) = k4_xboole_0(sK2,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))) ) | (~spl3_8 | ~spl3_59)),
% 38.78/5.24    inference(superposition,[],[f698,f68])).
% 38.78/5.24  fof(f813,plain,(
% 38.78/5.24    spl3_62 | ~spl3_8 | ~spl3_58),
% 38.78/5.24    inference(avatar_split_clause,[],[f778,f693,f67,f811])).
% 38.78/5.24  fof(f778,plain,(
% 38.78/5.24    ( ! [X2] : (k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k4_xboole_0(X2,k4_xboole_0(X2,sK1)))) ) | (~spl3_8 | ~spl3_58)),
% 38.78/5.24    inference(superposition,[],[f694,f68])).
% 38.78/5.24  fof(f809,plain,(
% 38.78/5.24    spl3_61 | ~spl3_36 | ~spl3_38 | ~spl3_55),
% 38.78/5.24    inference(avatar_split_clause,[],[f729,f681,f393,f384,f807])).
% 38.78/5.24  fof(f805,plain,(
% 38.78/5.24    spl3_60 | ~spl3_7 | ~spl3_29 | ~spl3_36),
% 38.78/5.24    inference(avatar_split_clause,[],[f405,f384,f271,f63,f803])).
% 38.78/5.24  fof(f271,plain,(
% 38.78/5.24    spl3_29 <=> ! [X3] : k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X3)))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 38.78/5.24  fof(f405,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X3)))) ) | (~spl3_7 | ~spl3_29 | ~spl3_36)),
% 38.78/5.24    inference(backward_demodulation,[],[f272,f402])).
% 38.78/5.24  fof(f272,plain,(
% 38.78/5.24    ( ! [X3] : (k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X3)))) ) | ~spl3_29),
% 38.78/5.24    inference(avatar_component_clause,[],[f271])).
% 38.78/5.24  fof(f699,plain,(
% 38.78/5.24    spl3_59 | ~spl3_7 | ~spl3_33 | ~spl3_36 | ~spl3_38 | ~spl3_53),
% 38.78/5.24    inference(avatar_split_clause,[],[f660,f640,f393,f384,f331,f63,f697])).
% 38.78/5.24  fof(f660,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) | (~spl3_7 | ~spl3_33 | ~spl3_36 | ~spl3_38 | ~spl3_53)),
% 38.78/5.24    inference(forward_demodulation,[],[f659,f385])).
% 38.78/5.24  fof(f659,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) | (~spl3_7 | ~spl3_33 | ~spl3_36 | ~spl3_38 | ~spl3_53)),
% 38.78/5.24    inference(forward_demodulation,[],[f658,f332])).
% 38.78/5.24  fof(f658,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))) ) | (~spl3_7 | ~spl3_36 | ~spl3_38 | ~spl3_53)),
% 38.78/5.24    inference(forward_demodulation,[],[f657,f402])).
% 38.78/5.24  fof(f657,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) | (~spl3_38 | ~spl3_53)),
% 38.78/5.24    inference(forward_demodulation,[],[f644,f394])).
% 38.78/5.24  fof(f644,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))) ) | (~spl3_38 | ~spl3_53)),
% 38.78/5.24    inference(superposition,[],[f641,f394])).
% 38.78/5.24  fof(f695,plain,(
% 38.78/5.24    spl3_58 | ~spl3_23 | ~spl3_47),
% 38.78/5.24    inference(avatar_split_clause,[],[f567,f555,f205,f693])).
% 38.78/5.24  fof(f567,plain,(
% 38.78/5.24    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) | (~spl3_23 | ~spl3_47)),
% 38.78/5.24    inference(superposition,[],[f206,f557])).
% 38.78/5.24  fof(f683,plain,(
% 38.78/5.24    spl3_55 | ~spl3_7 | ~spl3_8 | ~spl3_38),
% 38.78/5.24    inference(avatar_split_clause,[],[f434,f393,f67,f63,f681])).
% 38.78/5.24  fof(f434,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,X1) = k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1)))) ) | (~spl3_7 | ~spl3_8 | ~spl3_38)),
% 38.78/5.24    inference(forward_demodulation,[],[f421,f106])).
% 38.78/5.24  fof(f421,plain,(
% 38.78/5.24    ( ! [X1] : (k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK2,X1))) = k5_xboole_0(sK2,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))) ) | (~spl3_8 | ~spl3_38)),
% 38.78/5.24    inference(superposition,[],[f394,f68])).
% 38.78/5.24  fof(f679,plain,(
% 38.78/5.24    spl3_54 | ~spl3_7 | ~spl3_36),
% 38.78/5.24    inference(avatar_split_clause,[],[f402,f384,f63,f677])).
% 38.78/5.24  fof(f642,plain,(
% 38.78/5.24    spl3_53 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_20 | ~spl3_32 | ~spl3_37 | ~spl3_38),
% 38.78/5.24    inference(avatar_split_clause,[],[f451,f393,f388,f327,f174,f93,f88,f63,f640])).
% 38.78/5.24  fof(f451,plain,(
% 38.78/5.24    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_20 | ~spl3_32 | ~spl3_37 | ~spl3_38)),
% 38.78/5.24    inference(backward_demodulation,[],[f175,f446])).
% 38.78/5.24  fof(f592,plain,(
% 38.78/5.24    spl3_51 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41),
% 38.78/5.24    inference(avatar_split_clause,[],[f500,f478,f393,f388,f384,f93,f88,f63,f589])).
% 38.78/5.24  fof(f500,plain,(
% 38.78/5.24    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_36 | ~spl3_37 | ~spl3_38 | ~spl3_41)),
% 38.78/5.24    inference(backward_demodulation,[],[f440,f495])).
% 38.78/5.24  fof(f587,plain,(
% 38.78/5.24    spl3_50 | ~spl3_36 | ~spl3_41),
% 38.78/5.24    inference(avatar_split_clause,[],[f495,f478,f384,f584])).
% 38.78/5.24  fof(f582,plain,(
% 38.78/5.24    spl3_49 | ~spl3_38 | ~spl3_39),
% 38.78/5.24    inference(avatar_split_clause,[],[f461,f457,f393,f579])).
% 38.78/5.24  fof(f457,plain,(
% 38.78/5.24    spl3_39 <=> sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 38.78/5.24  fof(f461,plain,(
% 38.78/5.24    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | (~spl3_38 | ~spl3_39)),
% 38.78/5.24    inference(superposition,[],[f459,f394])).
% 38.78/5.24  fof(f459,plain,(
% 38.78/5.24    sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | ~spl3_39),
% 38.78/5.24    inference(avatar_component_clause,[],[f457])).
% 38.78/5.24  fof(f577,plain,(
% 38.78/5.24    spl3_48 | ~spl3_10 | ~spl3_38),
% 38.78/5.24    inference(avatar_split_clause,[],[f423,f393,f88,f574])).
% 38.78/5.24  fof(f558,plain,(
% 38.78/5.24    spl3_47 | ~spl3_36 | ~spl3_41),
% 38.78/5.24    inference(avatar_split_clause,[],[f509,f478,f384,f555])).
% 38.78/5.24  fof(f509,plain,(
% 38.78/5.24    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | (~spl3_36 | ~spl3_41)),
% 38.78/5.24    inference(backward_demodulation,[],[f480,f495])).
% 38.78/5.24  fof(f548,plain,(
% 38.78/5.24    ~spl3_45),
% 38.78/5.24    inference(avatar_split_clause,[],[f32,f545])).
% 38.78/5.24  fof(f32,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))),
% 38.78/5.24    inference(backward_demodulation,[],[f27,f31])).
% 38.78/5.24  fof(f31,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 38.78/5.24    inference(definition_unfolding,[],[f25,f20,f20])).
% 38.78/5.24  fof(f20,plain,(
% 38.78/5.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 38.78/5.24    inference(cnf_transformation,[],[f5])).
% 38.78/5.24  fof(f5,axiom,(
% 38.78/5.24    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 38.78/5.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 38.78/5.24  fof(f25,plain,(
% 38.78/5.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 38.78/5.24    inference(cnf_transformation,[],[f6])).
% 38.78/5.24  fof(f6,axiom,(
% 38.78/5.24    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 38.78/5.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 38.78/5.24  fof(f27,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 38.78/5.24    inference(definition_unfolding,[],[f17,f19,f20])).
% 38.78/5.24  fof(f19,plain,(
% 38.78/5.24    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 38.78/5.24    inference(cnf_transformation,[],[f8])).
% 38.78/5.24  fof(f8,axiom,(
% 38.78/5.24    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 38.78/5.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 38.78/5.24  fof(f17,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 38.78/5.24    inference(cnf_transformation,[],[f15])).
% 38.78/5.24  fof(f15,plain,(
% 38.78/5.24    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 38.78/5.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 38.78/5.24  fof(f14,plain,(
% 38.78/5.24    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 38.78/5.24    introduced(choice_axiom,[])).
% 38.78/5.24  fof(f11,plain,(
% 38.78/5.24    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 38.78/5.24    inference(ennf_transformation,[],[f10])).
% 38.78/5.24  fof(f10,negated_conjecture,(
% 38.78/5.24    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 38.78/5.24    inference(negated_conjecture,[],[f9])).
% 38.78/5.24  fof(f9,conjecture,(
% 38.78/5.24    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 38.78/5.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 38.78/5.24  fof(f481,plain,(
% 38.78/5.24    spl3_41 | ~spl3_4 | ~spl3_7 | ~spl3_14 | ~spl3_16 | ~spl3_36 | ~spl3_39),
% 38.78/5.24    inference(avatar_split_clause,[],[f469,f457,f384,f133,f119,f63,f48,f478])).
% 38.78/5.24  fof(f48,plain,(
% 38.78/5.24    spl3_4 <=> sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 38.78/5.24  fof(f119,plain,(
% 38.78/5.24    spl3_14 <=> k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2)),
% 38.78/5.24    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 38.78/5.24  fof(f469,plain,(
% 38.78/5.24    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | (~spl3_4 | ~spl3_7 | ~spl3_14 | ~spl3_16 | ~spl3_36 | ~spl3_39)),
% 38.78/5.24    inference(forward_demodulation,[],[f468,f50])).
% 38.78/5.24  fof(f50,plain,(
% 38.78/5.24    sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_4),
% 38.78/5.24    inference(avatar_component_clause,[],[f48])).
% 38.78/5.24  fof(f468,plain,(
% 38.78/5.24    k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | (~spl3_7 | ~spl3_14 | ~spl3_16 | ~spl3_36 | ~spl3_39)),
% 38.78/5.24    inference(forward_demodulation,[],[f467,f121])).
% 38.78/5.24  fof(f121,plain,(
% 38.78/5.24    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2) | ~spl3_14),
% 38.78/5.24    inference(avatar_component_clause,[],[f119])).
% 38.78/5.24  fof(f467,plain,(
% 38.78/5.24    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | (~spl3_7 | ~spl3_16 | ~spl3_36 | ~spl3_39)),
% 38.78/5.24    inference(forward_demodulation,[],[f464,f402])).
% 38.78/5.25  fof(f464,plain,(
% 38.78/5.25    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | (~spl3_16 | ~spl3_39)),
% 38.78/5.25    inference(superposition,[],[f134,f459])).
% 38.78/5.25  fof(f460,plain,(
% 38.78/5.25    spl3_39 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_37 | ~spl3_38),
% 38.78/5.25    inference(avatar_split_clause,[],[f441,f393,f388,f93,f88,f63,f457])).
% 38.78/5.25  fof(f441,plain,(
% 38.78/5.25    sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | (~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_37 | ~spl3_38)),
% 38.78/5.25    inference(backward_demodulation,[],[f90,f440])).
% 38.78/5.25  fof(f395,plain,(
% 38.78/5.25    spl3_38 | ~spl3_7 | ~spl3_35),
% 38.78/5.25    inference(avatar_split_clause,[],[f379,f371,f63,f393])).
% 38.78/5.25  fof(f379,plain,(
% 38.78/5.25    ( ! [X5] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X5))) ) | (~spl3_7 | ~spl3_35)),
% 38.78/5.25    inference(superposition,[],[f64,f372])).
% 38.78/5.25  fof(f391,plain,(
% 38.78/5.25    spl3_37 | ~spl3_13 | ~spl3_35),
% 38.78/5.25    inference(avatar_split_clause,[],[f374,f371,f112,f388])).
% 38.78/5.25  fof(f374,plain,(
% 38.78/5.25    k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | (~spl3_13 | ~spl3_35)),
% 38.78/5.25    inference(superposition,[],[f372,f114])).
% 38.78/5.25  fof(f386,plain,(
% 38.78/5.25    spl3_36 | ~spl3_13 | ~spl3_23),
% 38.78/5.25    inference(avatar_split_clause,[],[f346,f205,f112,f384])).
% 38.78/5.25  fof(f346,plain,(
% 38.78/5.25    ( ! [X7] : (k4_xboole_0(sK2,X7) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X7)))) ) | (~spl3_13 | ~spl3_23)),
% 38.78/5.25    inference(superposition,[],[f206,f114])).
% 38.78/5.25  fof(f373,plain,(
% 38.78/5.25    spl3_35 | ~spl3_5 | ~spl3_23),
% 38.78/5.25    inference(avatar_split_clause,[],[f343,f205,f54,f371])).
% 38.78/5.25  fof(f343,plain,(
% 38.78/5.25    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,X0)))) ) | (~spl3_5 | ~spl3_23)),
% 38.78/5.25    inference(superposition,[],[f206,f56])).
% 38.78/5.25  fof(f337,plain,(
% 38.78/5.25    spl3_34 | ~spl3_7 | ~spl3_8 | ~spl3_31),
% 38.78/5.25    inference(avatar_split_clause,[],[f321,f310,f67,f63,f335])).
% 38.78/5.25  fof(f310,plain,(
% 38.78/5.25    spl3_31 <=> ! [X3] : k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X3)))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 38.78/5.25  fof(f321,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_31)),
% 38.78/5.25    inference(forward_demodulation,[],[f314,f106])).
% 38.78/5.25  fof(f314,plain,(
% 38.78/5.25    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1))))) ) | (~spl3_8 | ~spl3_31)),
% 38.78/5.25    inference(superposition,[],[f311,f68])).
% 38.78/5.25  fof(f311,plain,(
% 38.78/5.25    ( ! [X3] : (k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X3)))) ) | ~spl3_31),
% 38.78/5.25    inference(avatar_component_clause,[],[f310])).
% 38.78/5.25  fof(f333,plain,(
% 38.78/5.25    spl3_33 | ~spl3_7 | ~spl3_31),
% 38.78/5.25    inference(avatar_split_clause,[],[f317,f310,f63,f331])).
% 38.78/5.25  fof(f317,plain,(
% 38.78/5.25    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0))) ) | (~spl3_7 | ~spl3_31)),
% 38.78/5.25    inference(superposition,[],[f311,f64])).
% 38.78/5.25  fof(f329,plain,(
% 38.78/5.25    spl3_32 | ~spl3_6 | ~spl3_30),
% 38.78/5.25    inference(avatar_split_clause,[],[f306,f300,f59,f327])).
% 38.78/5.25  fof(f300,plain,(
% 38.78/5.25    spl3_30 <=> k4_xboole_0(sK2,sK2) = k5_xboole_0(sK1,sK1)),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 38.78/5.25  fof(f306,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK2,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ) | (~spl3_6 | ~spl3_30)),
% 38.78/5.25    inference(superposition,[],[f60,f302])).
% 38.78/5.25  fof(f302,plain,(
% 38.78/5.25    k4_xboole_0(sK2,sK2) = k5_xboole_0(sK1,sK1) | ~spl3_30),
% 38.78/5.25    inference(avatar_component_clause,[],[f300])).
% 38.78/5.25  fof(f312,plain,(
% 38.78/5.25    spl3_31 | ~spl3_7 | ~spl3_28),
% 38.78/5.25    inference(avatar_split_clause,[],[f282,f267,f63,f310])).
% 38.78/5.25  fof(f267,plain,(
% 38.78/5.25    spl3_28 <=> ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 38.78/5.25  fof(f282,plain,(
% 38.78/5.25    ( ! [X3] : (k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X3)))) ) | (~spl3_7 | ~spl3_28)),
% 38.78/5.25    inference(superposition,[],[f268,f64])).
% 38.78/5.25  fof(f268,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) ) | ~spl3_28),
% 38.78/5.25    inference(avatar_component_clause,[],[f267])).
% 38.78/5.25  fof(f303,plain,(
% 38.78/5.25    spl3_30 | ~spl3_18 | ~spl3_29),
% 38.78/5.25    inference(avatar_split_clause,[],[f292,f271,f156,f300])).
% 38.78/5.25  fof(f156,plain,(
% 38.78/5.25    spl3_18 <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 38.78/5.25  fof(f292,plain,(
% 38.78/5.25    k4_xboole_0(sK2,sK2) = k5_xboole_0(sK1,sK1) | (~spl3_18 | ~spl3_29)),
% 38.78/5.25    inference(superposition,[],[f272,f158])).
% 38.78/5.25  fof(f158,plain,(
% 38.78/5.25    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) | ~spl3_18),
% 38.78/5.25    inference(avatar_component_clause,[],[f156])).
% 38.78/5.25  fof(f273,plain,(
% 38.78/5.25    spl3_29 | ~spl3_7 | ~spl3_25),
% 38.78/5.25    inference(avatar_split_clause,[],[f249,f224,f63,f271])).
% 38.78/5.25  fof(f224,plain,(
% 38.78/5.25    spl3_25 <=> ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 38.78/5.25  fof(f249,plain,(
% 38.78/5.25    ( ! [X3] : (k4_xboole_0(sK2,X3) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,X3)))) ) | (~spl3_7 | ~spl3_25)),
% 38.78/5.25    inference(superposition,[],[f225,f64])).
% 38.78/5.25  fof(f225,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | ~spl3_25),
% 38.78/5.25    inference(avatar_component_clause,[],[f224])).
% 38.78/5.25  fof(f269,plain,(
% 38.78/5.25    spl3_28 | ~spl3_6 | ~spl3_19),
% 38.78/5.25    inference(avatar_split_clause,[],[f172,f167,f59,f267])).
% 38.78/5.25  fof(f167,plain,(
% 38.78/5.25    spl3_19 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 38.78/5.25  fof(f172,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) ) | (~spl3_6 | ~spl3_19)),
% 38.78/5.25    inference(forward_demodulation,[],[f171,f60])).
% 38.78/5.25  fof(f171,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK1),X0))) ) | (~spl3_6 | ~spl3_19)),
% 38.78/5.25    inference(superposition,[],[f60,f169])).
% 38.78/5.25  fof(f169,plain,(
% 38.78/5.25    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) | ~spl3_19),
% 38.78/5.25    inference(avatar_component_clause,[],[f167])).
% 38.78/5.25  fof(f226,plain,(
% 38.78/5.25    spl3_25 | ~spl3_6 | ~spl3_14 | ~spl3_15),
% 38.78/5.25    inference(avatar_split_clause,[],[f131,f124,f119,f59,f224])).
% 38.78/5.25  fof(f124,plain,(
% 38.78/5.25    spl3_15 <=> sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 38.78/5.25  fof(f131,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | (~spl3_6 | ~spl3_14 | ~spl3_15)),
% 38.78/5.25    inference(forward_demodulation,[],[f130,f128])).
% 38.78/5.25  fof(f128,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK1,sK2),X0) = k5_xboole_0(sK1,k5_xboole_0(sK2,X0))) ) | (~spl3_6 | ~spl3_14)),
% 38.78/5.25    inference(superposition,[],[f60,f121])).
% 38.78/5.25  fof(f130,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,sK2),X0))) ) | (~spl3_6 | ~spl3_15)),
% 38.78/5.25    inference(superposition,[],[f60,f126])).
% 38.78/5.25  fof(f126,plain,(
% 38.78/5.25    sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_15),
% 38.78/5.25    inference(avatar_component_clause,[],[f124])).
% 38.78/5.25  fof(f207,plain,(
% 38.78/5.25    spl3_23),
% 38.78/5.25    inference(avatar_split_clause,[],[f31,f205])).
% 38.78/5.25  fof(f176,plain,(
% 38.78/5.25    spl3_20 | ~spl3_6 | ~spl3_11),
% 38.78/5.25    inference(avatar_split_clause,[],[f98,f93,f59,f174])).
% 38.78/5.25  fof(f98,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = k5_xboole_0(k4_xboole_0(sK2,sK1),X0)) ) | (~spl3_6 | ~spl3_11)),
% 38.78/5.25    inference(superposition,[],[f60,f95])).
% 38.78/5.25  fof(f170,plain,(
% 38.78/5.25    spl3_19 | ~spl3_4 | ~spl3_14 | ~spl3_16 | ~spl3_17),
% 38.78/5.25    inference(avatar_split_clause,[],[f163,f151,f133,f119,f48,f167])).
% 38.78/5.25  fof(f151,plain,(
% 38.78/5.25    spl3_17 <=> sK2 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 38.78/5.25  fof(f163,plain,(
% 38.78/5.25    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) | (~spl3_4 | ~spl3_14 | ~spl3_16 | ~spl3_17)),
% 38.78/5.25    inference(forward_demodulation,[],[f162,f50])).
% 38.78/5.25  fof(f162,plain,(
% 38.78/5.25    k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) | (~spl3_14 | ~spl3_16 | ~spl3_17)),
% 38.78/5.25    inference(forward_demodulation,[],[f160,f121])).
% 38.78/5.25  fof(f160,plain,(
% 38.78/5.25    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) | (~spl3_16 | ~spl3_17)),
% 38.78/5.25    inference(superposition,[],[f134,f153])).
% 38.78/5.25  fof(f153,plain,(
% 38.78/5.25    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)) | ~spl3_17),
% 38.78/5.25    inference(avatar_component_clause,[],[f151])).
% 38.78/5.25  fof(f159,plain,(
% 38.78/5.25    spl3_18 | ~spl3_4 | ~spl3_10 | ~spl3_14 | ~spl3_16),
% 38.78/5.25    inference(avatar_split_clause,[],[f144,f133,f119,f88,f48,f156])).
% 38.78/5.25  fof(f144,plain,(
% 38.78/5.25    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) | (~spl3_4 | ~spl3_10 | ~spl3_14 | ~spl3_16)),
% 38.78/5.25    inference(forward_demodulation,[],[f143,f50])).
% 38.78/5.25  fof(f143,plain,(
% 38.78/5.25    k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) | (~spl3_10 | ~spl3_14 | ~spl3_16)),
% 38.78/5.25    inference(forward_demodulation,[],[f137,f121])).
% 38.78/5.25  fof(f137,plain,(
% 38.78/5.25    k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | (~spl3_10 | ~spl3_16)),
% 38.78/5.25    inference(superposition,[],[f134,f90])).
% 38.78/5.25  fof(f154,plain,(
% 38.78/5.25    spl3_17 | ~spl3_4 | ~spl3_15 | ~spl3_16),
% 38.78/5.25    inference(avatar_split_clause,[],[f142,f133,f124,f48,f151])).
% 38.78/5.25  fof(f142,plain,(
% 38.78/5.25    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)) | (~spl3_4 | ~spl3_15 | ~spl3_16)),
% 38.78/5.25    inference(forward_demodulation,[],[f136,f126])).
% 38.78/5.25  fof(f136,plain,(
% 38.78/5.25    k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)) | (~spl3_4 | ~spl3_16)),
% 38.78/5.25    inference(superposition,[],[f134,f50])).
% 38.78/5.25  fof(f135,plain,(
% 38.78/5.25    spl3_16 | ~spl3_6 | ~spl3_9 | ~spl3_14),
% 38.78/5.25    inference(avatar_split_clause,[],[f129,f119,f75,f59,f133])).
% 38.78/5.25  fof(f129,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | (~spl3_6 | ~spl3_9 | ~spl3_14)),
% 38.78/5.25    inference(backward_demodulation,[],[f76,f128])).
% 38.78/5.25  fof(f127,plain,(
% 38.78/5.25    spl3_15 | ~spl3_7 | ~spl3_13),
% 38.78/5.25    inference(avatar_split_clause,[],[f117,f112,f63,f124])).
% 38.78/5.25  fof(f117,plain,(
% 38.78/5.25    sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_7 | ~spl3_13)),
% 38.78/5.25    inference(superposition,[],[f64,f114])).
% 38.78/5.25  fof(f122,plain,(
% 38.78/5.25    spl3_14 | ~spl3_7 | ~spl3_13),
% 38.78/5.25    inference(avatar_split_clause,[],[f116,f112,f63,f119])).
% 38.78/5.25  fof(f116,plain,(
% 38.78/5.25    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2) | (~spl3_7 | ~spl3_13)),
% 38.78/5.25    inference(superposition,[],[f64,f114])).
% 38.78/5.25  fof(f115,plain,(
% 38.78/5.25    spl3_13 | ~spl3_5 | ~spl3_8),
% 38.78/5.25    inference(avatar_split_clause,[],[f103,f67,f54,f112])).
% 38.78/5.25  fof(f103,plain,(
% 38.78/5.25    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_8)),
% 38.78/5.25    inference(superposition,[],[f68,f56])).
% 38.78/5.25  fof(f102,plain,(
% 38.78/5.25    spl3_12 | ~spl3_6 | ~spl3_10),
% 38.78/5.25    inference(avatar_split_clause,[],[f97,f88,f59,f100])).
% 38.78/5.25  fof(f97,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k5_xboole_0(sK2,X0)) ) | (~spl3_6 | ~spl3_10)),
% 38.78/5.25    inference(superposition,[],[f60,f90])).
% 38.78/5.25  fof(f96,plain,(
% 38.78/5.25    spl3_11 | ~spl3_5 | ~spl3_7),
% 38.78/5.25    inference(avatar_split_clause,[],[f82,f63,f54,f93])).
% 38.78/5.25  fof(f82,plain,(
% 38.78/5.25    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2) | (~spl3_5 | ~spl3_7)),
% 38.78/5.25    inference(superposition,[],[f64,f56])).
% 38.78/5.25  fof(f91,plain,(
% 38.78/5.25    spl3_10 | ~spl3_5 | ~spl3_7),
% 38.78/5.25    inference(avatar_split_clause,[],[f81,f63,f54,f88])).
% 38.78/5.25  fof(f81,plain,(
% 38.78/5.25    sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) | (~spl3_5 | ~spl3_7)),
% 38.78/5.25    inference(superposition,[],[f64,f56])).
% 38.78/5.25  fof(f77,plain,(
% 38.78/5.25    spl3_9 | ~spl3_4 | ~spl3_6),
% 38.78/5.25    inference(avatar_split_clause,[],[f70,f59,f48,f75])).
% 38.78/5.25  fof(f70,plain,(
% 38.78/5.25    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0)) ) | (~spl3_4 | ~spl3_6)),
% 38.78/5.25    inference(superposition,[],[f60,f50])).
% 38.78/5.25  fof(f69,plain,(
% 38.78/5.25    spl3_8),
% 38.78/5.25    inference(avatar_split_clause,[],[f28,f67])).
% 38.78/5.25  fof(f28,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 38.78/5.25    inference(definition_unfolding,[],[f18,f20,f20])).
% 38.78/5.25  fof(f18,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 38.78/5.25    inference(cnf_transformation,[],[f1])).
% 38.78/5.25  fof(f1,axiom,(
% 38.78/5.25    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 38.78/5.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 38.78/5.25  fof(f65,plain,(
% 38.78/5.25    spl3_7),
% 38.78/5.25    inference(avatar_split_clause,[],[f26,f63])).
% 38.78/5.25  fof(f26,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 38.78/5.25    inference(definition_unfolding,[],[f21,f20])).
% 38.78/5.25  fof(f21,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 38.78/5.25    inference(cnf_transformation,[],[f2])).
% 38.78/5.25  fof(f2,axiom,(
% 38.78/5.25    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 38.78/5.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 38.78/5.25  fof(f61,plain,(
% 38.78/5.25    spl3_6),
% 38.78/5.25    inference(avatar_split_clause,[],[f24,f59])).
% 38.78/5.25  fof(f24,plain,(
% 38.78/5.25    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 38.78/5.25    inference(cnf_transformation,[],[f7])).
% 38.78/5.25  fof(f7,axiom,(
% 38.78/5.25    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 38.78/5.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 38.78/5.25  fof(f57,plain,(
% 38.78/5.25    spl3_5 | ~spl3_1 | ~spl3_3),
% 38.78/5.25    inference(avatar_split_clause,[],[f52,f43,f34,f54])).
% 38.78/5.25  fof(f34,plain,(
% 38.78/5.25    spl3_1 <=> r1_tarski(sK2,sK1)),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 38.78/5.25  fof(f43,plain,(
% 38.78/5.25    spl3_3 <=> ! [X1,X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 38.78/5.25  fof(f52,plain,(
% 38.78/5.25    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | (~spl3_1 | ~spl3_3)),
% 38.78/5.25    inference(resolution,[],[f44,f36])).
% 38.78/5.25  fof(f36,plain,(
% 38.78/5.25    r1_tarski(sK2,sK1) | ~spl3_1),
% 38.78/5.25    inference(avatar_component_clause,[],[f34])).
% 38.78/5.25  fof(f44,plain,(
% 38.78/5.25    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl3_3),
% 38.78/5.25    inference(avatar_component_clause,[],[f43])).
% 38.78/5.25  fof(f51,plain,(
% 38.78/5.25    spl3_4 | ~spl3_1 | ~spl3_2),
% 38.78/5.25    inference(avatar_split_clause,[],[f46,f39,f34,f48])).
% 38.78/5.25  fof(f39,plain,(
% 38.78/5.25    spl3_2 <=> ! [X1,X0] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 38.78/5.25    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 38.78/5.25  fof(f46,plain,(
% 38.78/5.25    sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_2)),
% 38.78/5.25    inference(resolution,[],[f40,f36])).
% 38.78/5.25  fof(f40,plain,(
% 38.78/5.25    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) ) | ~spl3_2),
% 38.78/5.25    inference(avatar_component_clause,[],[f39])).
% 38.78/5.25  fof(f45,plain,(
% 38.78/5.25    spl3_3),
% 38.78/5.25    inference(avatar_split_clause,[],[f30,f43])).
% 38.78/5.25  fof(f30,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 38.78/5.25    inference(definition_unfolding,[],[f23,f20])).
% 38.78/5.25  fof(f23,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 38.78/5.25    inference(cnf_transformation,[],[f13])).
% 38.78/5.25  fof(f13,plain,(
% 38.78/5.25    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 38.78/5.25    inference(ennf_transformation,[],[f4])).
% 38.78/5.25  fof(f4,axiom,(
% 38.78/5.25    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 38.78/5.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 38.78/5.25  fof(f41,plain,(
% 38.78/5.25    spl3_2),
% 38.78/5.25    inference(avatar_split_clause,[],[f29,f39])).
% 38.78/5.25  fof(f29,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 38.78/5.25    inference(definition_unfolding,[],[f22,f19])).
% 38.78/5.25  fof(f22,plain,(
% 38.78/5.25    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 38.78/5.25    inference(cnf_transformation,[],[f12])).
% 38.78/5.25  fof(f12,plain,(
% 38.78/5.25    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 38.78/5.25    inference(ennf_transformation,[],[f3])).
% 38.78/5.25  fof(f3,axiom,(
% 38.78/5.25    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 38.78/5.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 38.78/5.25  fof(f37,plain,(
% 38.78/5.25    spl3_1),
% 38.78/5.25    inference(avatar_split_clause,[],[f16,f34])).
% 38.78/5.25  fof(f16,plain,(
% 38.78/5.25    r1_tarski(sK2,sK1)),
% 38.78/5.25    inference(cnf_transformation,[],[f15])).
% 38.78/5.25  % SZS output end Proof for theBenchmark
% 38.78/5.25  % (17223)------------------------------
% 38.78/5.25  % (17223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.78/5.25  % (17223)Termination reason: Refutation
% 38.78/5.25  
% 38.78/5.25  % (17223)Memory used [KB]: 138291
% 38.78/5.25  % (17223)Time elapsed: 4.797 s
% 38.78/5.25  % (17223)------------------------------
% 38.78/5.25  % (17223)------------------------------
% 38.78/5.26  % (17215)Success in time 4.893 s
%------------------------------------------------------------------------------
