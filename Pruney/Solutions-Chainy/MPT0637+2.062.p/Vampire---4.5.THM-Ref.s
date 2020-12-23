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
% DateTime   : Thu Dec  3 12:52:31 EST 2020

% Result     : Theorem 4.11s
% Output     : Refutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  244 ( 515 expanded)
%              Number of leaves         :   62 ( 246 expanded)
%              Depth                    :   12
%              Number of atoms          :  660 (1249 expanded)
%              Number of equality atoms :  148 ( 336 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7517,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f100,f104,f124,f128,f139,f143,f147,f160,f196,f210,f214,f218,f234,f253,f269,f273,f277,f310,f369,f549,f603,f952,f986,f1058,f1168,f1189,f1207,f1222,f1237,f4331,f4372,f4711,f4715,f4980,f5434,f6357,f7365])).

fof(f7365,plain,
    ( ~ spl2_2
    | spl2_88
    | ~ spl2_241 ),
    inference(avatar_contradiction_clause,[],[f7364])).

fof(f7364,plain,
    ( $false
    | ~ spl2_2
    | spl2_88
    | ~ spl2_241 ),
    inference(subsumption_resolution,[],[f7130,f6356])).

fof(f6356,plain,
    ( ! [X123,X122] : k7_relat_1(k6_relat_1(X123),X122) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122)))
    | ~ spl2_241 ),
    inference(avatar_component_clause,[],[f6355])).

fof(f6355,plain,
    ( spl2_241
  <=> ! [X122,X123] : k7_relat_1(k6_relat_1(X123),X122) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_241])])).

fof(f7130,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_2
    | spl2_88
    | ~ spl2_241 ),
    inference(backward_demodulation,[],[f1188,f6636])).

fof(f6636,plain,
    ( ! [X2,X3] : k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))
    | ~ spl2_2
    | ~ spl2_241 ),
    inference(superposition,[],[f83,f6356])).

fof(f83,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1188,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | spl2_88 ),
    inference(avatar_component_clause,[],[f1186])).

fof(f1186,plain,
    ( spl2_88
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f6357,plain,
    ( spl2_241
    | ~ spl2_83
    | ~ spl2_203
    | ~ spl2_218 ),
    inference(avatar_split_clause,[],[f5719,f5432,f4370,f1056,f6355])).

fof(f1056,plain,
    ( spl2_83
  <=> ! [X13,X12] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))),X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f4370,plain,
    ( spl2_203
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).

fof(f5432,plain,
    ( spl2_218
  <=> ! [X219,X218] : k7_relat_1(k6_relat_1(X219),X218) = k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).

fof(f5719,plain,
    ( ! [X123,X122] : k7_relat_1(k6_relat_1(X123),X122) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122)))
    | ~ spl2_83
    | ~ spl2_203
    | ~ spl2_218 ),
    inference(forward_demodulation,[],[f5495,f4371])).

fof(f4371,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)
    | ~ spl2_203 ),
    inference(avatar_component_clause,[],[f4370])).

fof(f5495,plain,
    ( ! [X123,X122] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122))),X122)
    | ~ spl2_83
    | ~ spl2_218 ),
    inference(superposition,[],[f1057,f5433])).

fof(f5433,plain,
    ( ! [X218,X219] : k7_relat_1(k6_relat_1(X219),X218) = k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218)))
    | ~ spl2_218 ),
    inference(avatar_component_clause,[],[f5432])).

fof(f1057,plain,
    ( ! [X12,X13] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))),X12)
    | ~ spl2_83 ),
    inference(avatar_component_clause,[],[f1056])).

fof(f5434,plain,
    ( spl2_218
    | ~ spl2_2
    | ~ spl2_217 ),
    inference(avatar_split_clause,[],[f5359,f4978,f82,f5432])).

fof(f4978,plain,
    ( spl2_217
  <=> ! [X1,X0] : k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_217])])).

fof(f5359,plain,
    ( ! [X218,X219] : k7_relat_1(k6_relat_1(X219),X218) = k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218)))
    | ~ spl2_2
    | ~ spl2_217 ),
    inference(forward_demodulation,[],[f5106,f83])).

fof(f5106,plain,
    ( ! [X218,X219] : k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218))) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X219),X218)))
    | ~ spl2_2
    | ~ spl2_217 ),
    inference(superposition,[],[f83,f4979])).

fof(f4979,plain,
    ( ! [X0,X1] : k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))
    | ~ spl2_217 ),
    inference(avatar_component_clause,[],[f4978])).

fof(f4980,plain,
    ( spl2_217
    | ~ spl2_26
    | ~ spl2_27
    | ~ spl2_208
    | ~ spl2_209 ),
    inference(avatar_split_clause,[],[f4760,f4713,f4709,f251,f232,f4978])).

fof(f232,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f251,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f4709,plain,
    ( spl2_208
  <=> ! [X150,X151] : r1_tarski(k7_relat_1(k6_relat_1(X150),X151),k7_relat_1(k6_relat_1(X151),k2_relat_1(k7_relat_1(k6_relat_1(X150),X151)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_208])])).

fof(f4713,plain,
    ( spl2_209
  <=> ! [X153,X152] : r1_tarski(k7_relat_1(k6_relat_1(X153),k2_relat_1(k7_relat_1(k6_relat_1(X152),X153))),k7_relat_1(k6_relat_1(X152),X153)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).

fof(f4760,plain,
    ( ! [X0,X1] : k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))
    | ~ spl2_26
    | ~ spl2_27
    | ~ spl2_208
    | ~ spl2_209 ),
    inference(forward_demodulation,[],[f4747,f4717])).

fof(f4717,plain,
    ( ! [X2,X3] : k6_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X2),X3)),k7_relat_1(k6_relat_1(X3),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))))
    | ~ spl2_26
    | ~ spl2_208 ),
    inference(resolution,[],[f4710,f233])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f232])).

fof(f4710,plain,
    ( ! [X151,X150] : r1_tarski(k7_relat_1(k6_relat_1(X150),X151),k7_relat_1(k6_relat_1(X151),k2_relat_1(k7_relat_1(k6_relat_1(X150),X151))))
    | ~ spl2_208 ),
    inference(avatar_component_clause,[],[f4709])).

fof(f4747,plain,
    ( ! [X0,X1] : k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))
    | ~ spl2_27
    | ~ spl2_209 ),
    inference(resolution,[],[f4714,f252])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f251])).

fof(f4714,plain,
    ( ! [X152,X153] : r1_tarski(k7_relat_1(k6_relat_1(X153),k2_relat_1(k7_relat_1(k6_relat_1(X152),X153))),k7_relat_1(k6_relat_1(X152),X153))
    | ~ spl2_209 ),
    inference(avatar_component_clause,[],[f4713])).

fof(f4715,plain,
    ( spl2_209
    | ~ spl2_91
    | ~ spl2_203 ),
    inference(avatar_split_clause,[],[f4447,f4370,f1235,f4713])).

fof(f1235,plain,
    ( spl2_91
  <=> ! [X1,X0] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).

fof(f4447,plain,
    ( ! [X152,X153] : r1_tarski(k7_relat_1(k6_relat_1(X153),k2_relat_1(k7_relat_1(k6_relat_1(X152),X153))),k7_relat_1(k6_relat_1(X152),X153))
    | ~ spl2_91
    | ~ spl2_203 ),
    inference(superposition,[],[f1236,f4371])).

fof(f1236,plain,
    ( ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_91 ),
    inference(avatar_component_clause,[],[f1235])).

fof(f4711,plain,
    ( spl2_208
    | ~ spl2_91
    | ~ spl2_203 ),
    inference(avatar_split_clause,[],[f4446,f4370,f1235,f4709])).

fof(f4446,plain,
    ( ! [X151,X150] : r1_tarski(k7_relat_1(k6_relat_1(X150),X151),k7_relat_1(k6_relat_1(X151),k2_relat_1(k7_relat_1(k6_relat_1(X150),X151))))
    | ~ spl2_91
    | ~ spl2_203 ),
    inference(superposition,[],[f1236,f4371])).

fof(f4372,plain,
    ( spl2_203
    | ~ spl2_78
    | ~ spl2_83
    | ~ spl2_200 ),
    inference(avatar_split_clause,[],[f4364,f4329,f1056,f984,f4370])).

fof(f984,plain,
    ( spl2_78
  <=> ! [X3,X5,X4] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f4329,plain,
    ( spl2_200
  <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_200])])).

fof(f4364,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)
    | ~ spl2_78
    | ~ spl2_83
    | ~ spl2_200 ),
    inference(forward_demodulation,[],[f4349,f1057])).

fof(f4349,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)
    | ~ spl2_78
    | ~ spl2_200 ),
    inference(superposition,[],[f4330,f985])).

fof(f985,plain,
    ( ! [X4,X5,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f984])).

fof(f4330,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))))
    | ~ spl2_200 ),
    inference(avatar_component_clause,[],[f4329])).

fof(f4331,plain,
    ( spl2_200
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f163,f158,f102,f4329])).

fof(f102,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f158,plain,
    ( spl2_15
  <=> ! [X5,X6] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f163,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))))
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(resolution,[],[f159,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f159,plain,
    ( ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1237,plain,
    ( spl2_91
    | ~ spl2_52
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f1229,f1220,f601,f1235])).

fof(f601,plain,
    ( spl2_52
  <=> ! [X3,X5,X4] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f1220,plain,
    ( spl2_90
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f1229,plain,
    ( ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_52
    | ~ spl2_90 ),
    inference(superposition,[],[f602,f1221])).

fof(f1221,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f602,plain,
    ( ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f601])).

fof(f1222,plain,
    ( spl2_90
    | ~ spl2_29
    | ~ spl2_89 ),
    inference(avatar_split_clause,[],[f1214,f1205,f271,f1220])).

fof(f271,plain,
    ( spl2_29
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f1205,plain,
    ( spl2_89
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f1214,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_29
    | ~ spl2_89 ),
    inference(superposition,[],[f1206,f272])).

fof(f272,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f271])).

fof(f1206,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_89 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1207,plain,
    ( spl2_89
    | ~ spl2_15
    | ~ spl2_22
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f1178,f1166,f208,f158,f1205])).

fof(f208,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f1166,plain,
    ( spl2_87
  <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f1178,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_15
    | ~ spl2_22
    | ~ spl2_87 ),
    inference(subsumption_resolution,[],[f1169,f159])).

fof(f1169,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) )
    | ~ spl2_22
    | ~ spl2_87 ),
    inference(resolution,[],[f1167,f209])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f1167,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1189,plain,
    ( ~ spl2_88
    | ~ spl2_1
    | ~ spl2_2
    | spl2_28
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f1159,f950,f266,f82,f78,f1186])).

fof(f78,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f266,plain,
    ( spl2_28
  <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f950,plain,
    ( spl2_77
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f1159,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_28
    | ~ spl2_77 ),
    inference(backward_demodulation,[],[f268,f1158])).

fof(f1158,plain,
    ( ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_77 ),
    inference(forward_demodulation,[],[f1155,f83])).

fof(f1155,plain,
    ( ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4))
    | ~ spl2_1
    | ~ spl2_77 ),
    inference(resolution,[],[f951,f79])).

fof(f79,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f951,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) )
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f950])).

fof(f268,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f266])).

fof(f1168,plain,
    ( spl2_87
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_24
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f1162,f950,f216,f82,f78,f1166])).

fof(f216,plain,
    ( spl2_24
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1162,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_24
    | ~ spl2_77 ),
    inference(backward_demodulation,[],[f217,f1158])).

fof(f217,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1058,plain,
    ( spl2_83
    | ~ spl2_20
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f242,f232,f194,f1056])).

fof(f194,plain,
    ( spl2_20
  <=> ! [X1,X2] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f242,plain,
    ( ! [X12,X13] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))),X12)
    | ~ spl2_20
    | ~ spl2_26 ),
    inference(resolution,[],[f233,f195])).

fof(f195,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f986,plain,
    ( spl2_78
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f563,f547,f275,f271,f145,f141,f78,f984])).

fof(f141,plain,
    ( spl2_13
  <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f145,plain,
    ( spl2_14
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f275,plain,
    ( spl2_30
  <=> ! [X3,X5,X4] : k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f547,plain,
    ( spl2_49
  <=> ! [X5,X4,X6] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f563,plain,
    ( ! [X4,X5,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_49 ),
    inference(backward_demodulation,[],[f276,f561])).

fof(f561,plain,
    ( ! [X6,X4,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_29
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f560,f146])).

fof(f146,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f560,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_29
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f559,f272])).

fof(f559,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f555,f142])).

fof(f142,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f555,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6)))
    | ~ spl2_1
    | ~ spl2_49 ),
    inference(resolution,[],[f548,f79])).

fof(f548,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) )
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f547])).

fof(f276,plain,
    ( ! [X4,X5,X3] : k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f275])).

fof(f952,plain,(
    spl2_77 ),
    inference(avatar_split_clause,[],[f76,f950])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f603,plain,
    ( spl2_52
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_29
    | ~ spl2_41
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f573,f547,f367,f271,f145,f141,f78,f601])).

fof(f367,plain,
    ( spl2_41
  <=> ! [X3,X5,X4] : r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f573,plain,
    ( ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_29
    | ~ spl2_41
    | ~ spl2_49 ),
    inference(backward_demodulation,[],[f368,f561])).

fof(f368,plain,
    ( ! [X4,X5,X3] : r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f367])).

fof(f549,plain,
    ( spl2_49
    | ~ spl2_1
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f537,f308,f78,f547])).

fof(f308,plain,
    ( spl2_36
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f537,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) )
    | ~ spl2_1
    | ~ spl2_36 ),
    inference(resolution,[],[f309,f79])).

fof(f309,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f308])).

fof(f369,plain,
    ( spl2_41
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f340,f275,f158,f90,f367])).

fof(f90,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f340,plain,
    ( ! [X4,X5,X3] : r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f335,f159])).

fof(f335,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) )
    | ~ spl2_4
    | ~ spl2_30 ),
    inference(superposition,[],[f91,f276])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f310,plain,(
    spl2_36 ),
    inference(avatar_split_clause,[],[f60,f308])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f277,plain,
    ( spl2_30
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f162,f158,f122,f275])).

fof(f122,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f162,plain,
    ( ! [X4,X5,X3] : k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(resolution,[],[f159,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f273,plain,
    ( spl2_29
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f161,f158,f126,f271])).

fof(f126,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f161,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(resolution,[],[f159,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f269,plain,
    ( ~ spl2_28
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f135,f126,f122,f78,f266])).

fof(f135,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f131,f134])).

fof(f134,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f129,f132])).

fof(f132,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(resolution,[],[f127,f79])).

fof(f129,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f123,f79])).

fof(f131,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f74,f129])).

fof(f74,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f43,f73])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f41])).

fof(f41,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f253,plain,
    ( spl2_27
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_14
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f248,f212,f145,f86,f78,f251])).

fof(f86,plain,
    ( spl2_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f212,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_14
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f247,f146])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f244,f87])).

fof(f87,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f213,f79])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f234,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f222,f208,f145,f82,f78,f232])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f221,f146])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f220,f79])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_22 ),
    inference(superposition,[],[f209,f83])).

fof(f218,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f75,f216])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f214,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f59,f212])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f210,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f58,f208])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f196,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f187,f145,f137,f86,f78,f194])).

fof(f137,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f187,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f186,f87])).

fof(f186,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f185,f79])).

fof(f185,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f180,f79])).

fof(f180,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(superposition,[],[f138,f146])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f160,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f156,f145,f98,f78,f158])).

fof(f98,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f156,plain,
    ( ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f155,f79])).

fof(f155,plain,
    ( ! [X6,X5] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
        | ~ v1_relat_1(k6_relat_1(X5)) )
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f152,f79])).

fof(f152,plain,
    ( ! [X6,X5] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(k6_relat_1(X5)) )
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f99,f146])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f147,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f132,f126,f78,f145])).

fof(f143,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f134,f126,f122,f78,f141])).

fof(f139,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f48,f137])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f128,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f54,f126])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f124,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f104,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f47,f102])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f100,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f62,f98])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f92,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f56,f90])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f88,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f84,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f45,f82])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (14672)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (14674)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (14671)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (14683)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (14679)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (14680)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (14677)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (14669)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (14682)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (14670)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (14675)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (14678)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (14678)Refutation not found, incomplete strategy% (14678)------------------------------
% 0.21/0.52  % (14678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14678)Memory used [KB]: 10618
% 0.21/0.52  % (14678)Time elapsed: 0.078 s
% 0.21/0.52  % (14678)------------------------------
% 0.21/0.52  % (14678)------------------------------
% 0.21/0.55  % (14673)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (14684)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.56  % (14668)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.56  % (14681)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.57  % (14676)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.57  % (14667)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 4.11/0.89  % (14674)Refutation found. Thanks to Tanya!
% 4.11/0.89  % SZS status Theorem for theBenchmark
% 4.11/0.89  % SZS output start Proof for theBenchmark
% 4.11/0.89  fof(f7517,plain,(
% 4.11/0.89    $false),
% 4.11/0.89    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f100,f104,f124,f128,f139,f143,f147,f160,f196,f210,f214,f218,f234,f253,f269,f273,f277,f310,f369,f549,f603,f952,f986,f1058,f1168,f1189,f1207,f1222,f1237,f4331,f4372,f4711,f4715,f4980,f5434,f6357,f7365])).
% 4.11/0.89  fof(f7365,plain,(
% 4.11/0.89    ~spl2_2 | spl2_88 | ~spl2_241),
% 4.11/0.89    inference(avatar_contradiction_clause,[],[f7364])).
% 4.11/0.89  fof(f7364,plain,(
% 4.11/0.89    $false | (~spl2_2 | spl2_88 | ~spl2_241)),
% 4.11/0.89    inference(subsumption_resolution,[],[f7130,f6356])).
% 4.11/0.89  fof(f6356,plain,(
% 4.11/0.89    ( ! [X123,X122] : (k7_relat_1(k6_relat_1(X123),X122) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122)))) ) | ~spl2_241),
% 4.11/0.89    inference(avatar_component_clause,[],[f6355])).
% 4.11/0.89  fof(f6355,plain,(
% 4.11/0.89    spl2_241 <=> ! [X122,X123] : k7_relat_1(k6_relat_1(X123),X122) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122)))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_241])])).
% 4.11/0.89  fof(f7130,plain,(
% 4.11/0.89    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_2 | spl2_88 | ~spl2_241)),
% 4.11/0.89    inference(backward_demodulation,[],[f1188,f6636])).
% 4.11/0.89  fof(f6636,plain,(
% 4.11/0.89    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ) | (~spl2_2 | ~spl2_241)),
% 4.11/0.89    inference(superposition,[],[f83,f6356])).
% 4.11/0.89  fof(f83,plain,(
% 4.11/0.89    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 4.11/0.89    inference(avatar_component_clause,[],[f82])).
% 4.11/0.89  fof(f82,plain,(
% 4.11/0.89    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 4.11/0.89  fof(f1188,plain,(
% 4.11/0.89    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | spl2_88),
% 4.11/0.89    inference(avatar_component_clause,[],[f1186])).
% 4.11/0.89  fof(f1186,plain,(
% 4.11/0.89    spl2_88 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 4.11/0.89  fof(f6357,plain,(
% 4.11/0.89    spl2_241 | ~spl2_83 | ~spl2_203 | ~spl2_218),
% 4.11/0.89    inference(avatar_split_clause,[],[f5719,f5432,f4370,f1056,f6355])).
% 4.11/0.89  fof(f1056,plain,(
% 4.11/0.89    spl2_83 <=> ! [X13,X12] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))),X12)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).
% 4.11/0.89  fof(f4370,plain,(
% 4.11/0.89    spl2_203 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).
% 4.11/0.89  fof(f5432,plain,(
% 4.11/0.89    spl2_218 <=> ! [X219,X218] : k7_relat_1(k6_relat_1(X219),X218) = k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218)))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).
% 4.11/0.89  fof(f5719,plain,(
% 4.11/0.89    ( ! [X123,X122] : (k7_relat_1(k6_relat_1(X123),X122) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122)))) ) | (~spl2_83 | ~spl2_203 | ~spl2_218)),
% 4.11/0.89    inference(forward_demodulation,[],[f5495,f4371])).
% 4.11/0.89  fof(f4371,plain,(
% 4.11/0.89    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) ) | ~spl2_203),
% 4.11/0.89    inference(avatar_component_clause,[],[f4370])).
% 4.11/0.89  fof(f5495,plain,(
% 4.11/0.89    ( ! [X123,X122] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X123),X122))),X122)) ) | (~spl2_83 | ~spl2_218)),
% 4.11/0.89    inference(superposition,[],[f1057,f5433])).
% 4.11/0.89  fof(f5433,plain,(
% 4.11/0.89    ( ! [X218,X219] : (k7_relat_1(k6_relat_1(X219),X218) = k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218)))) ) | ~spl2_218),
% 4.11/0.89    inference(avatar_component_clause,[],[f5432])).
% 4.11/0.89  fof(f1057,plain,(
% 4.11/0.89    ( ! [X12,X13] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))),X12)) ) | ~spl2_83),
% 4.11/0.89    inference(avatar_component_clause,[],[f1056])).
% 4.11/0.89  fof(f5434,plain,(
% 4.11/0.89    spl2_218 | ~spl2_2 | ~spl2_217),
% 4.11/0.89    inference(avatar_split_clause,[],[f5359,f4978,f82,f5432])).
% 4.11/0.89  fof(f4978,plain,(
% 4.11/0.89    spl2_217 <=> ! [X1,X0] : k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_217])])).
% 4.11/0.89  fof(f5359,plain,(
% 4.11/0.89    ( ! [X218,X219] : (k7_relat_1(k6_relat_1(X219),X218) = k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218)))) ) | (~spl2_2 | ~spl2_217)),
% 4.11/0.89    inference(forward_demodulation,[],[f5106,f83])).
% 4.11/0.89  fof(f5106,plain,(
% 4.11/0.89    ( ! [X218,X219] : (k7_relat_1(k6_relat_1(X218),k2_relat_1(k7_relat_1(k6_relat_1(X219),X218))) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X219),X218)))) ) | (~spl2_2 | ~spl2_217)),
% 4.11/0.89    inference(superposition,[],[f83,f4979])).
% 4.11/0.89  fof(f4979,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ) | ~spl2_217),
% 4.11/0.89    inference(avatar_component_clause,[],[f4978])).
% 4.11/0.89  fof(f4980,plain,(
% 4.11/0.89    spl2_217 | ~spl2_26 | ~spl2_27 | ~spl2_208 | ~spl2_209),
% 4.11/0.89    inference(avatar_split_clause,[],[f4760,f4713,f4709,f251,f232,f4978])).
% 4.11/0.89  fof(f232,plain,(
% 4.11/0.89    spl2_26 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 4.11/0.89  fof(f251,plain,(
% 4.11/0.89    spl2_27 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 4.11/0.89  fof(f4709,plain,(
% 4.11/0.89    spl2_208 <=> ! [X150,X151] : r1_tarski(k7_relat_1(k6_relat_1(X150),X151),k7_relat_1(k6_relat_1(X151),k2_relat_1(k7_relat_1(k6_relat_1(X150),X151))))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_208])])).
% 4.11/0.89  fof(f4713,plain,(
% 4.11/0.89    spl2_209 <=> ! [X153,X152] : r1_tarski(k7_relat_1(k6_relat_1(X153),k2_relat_1(k7_relat_1(k6_relat_1(X152),X153))),k7_relat_1(k6_relat_1(X152),X153))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).
% 4.11/0.89  fof(f4760,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ) | (~spl2_26 | ~spl2_27 | ~spl2_208 | ~spl2_209)),
% 4.11/0.89    inference(forward_demodulation,[],[f4747,f4717])).
% 4.11/0.89  fof(f4717,plain,(
% 4.11/0.89    ( ! [X2,X3] : (k6_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X2),X3)),k7_relat_1(k6_relat_1(X3),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))))) ) | (~spl2_26 | ~spl2_208)),
% 4.11/0.89    inference(resolution,[],[f4710,f233])).
% 4.11/0.89  fof(f233,plain,(
% 4.11/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_26),
% 4.11/0.89    inference(avatar_component_clause,[],[f232])).
% 4.11/0.89  fof(f4710,plain,(
% 4.11/0.89    ( ! [X151,X150] : (r1_tarski(k7_relat_1(k6_relat_1(X150),X151),k7_relat_1(k6_relat_1(X151),k2_relat_1(k7_relat_1(k6_relat_1(X150),X151))))) ) | ~spl2_208),
% 4.11/0.89    inference(avatar_component_clause,[],[f4709])).
% 4.11/0.89  fof(f4747,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k6_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ) | (~spl2_27 | ~spl2_209)),
% 4.11/0.89    inference(resolution,[],[f4714,f252])).
% 4.11/0.89  fof(f252,plain,(
% 4.11/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_27),
% 4.11/0.89    inference(avatar_component_clause,[],[f251])).
% 4.11/0.89  fof(f4714,plain,(
% 4.11/0.89    ( ! [X152,X153] : (r1_tarski(k7_relat_1(k6_relat_1(X153),k2_relat_1(k7_relat_1(k6_relat_1(X152),X153))),k7_relat_1(k6_relat_1(X152),X153))) ) | ~spl2_209),
% 4.11/0.89    inference(avatar_component_clause,[],[f4713])).
% 4.11/0.89  fof(f4715,plain,(
% 4.11/0.89    spl2_209 | ~spl2_91 | ~spl2_203),
% 4.11/0.89    inference(avatar_split_clause,[],[f4447,f4370,f1235,f4713])).
% 4.11/0.89  fof(f1235,plain,(
% 4.11/0.89    spl2_91 <=> ! [X1,X0] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).
% 4.11/0.89  fof(f4447,plain,(
% 4.11/0.89    ( ! [X152,X153] : (r1_tarski(k7_relat_1(k6_relat_1(X153),k2_relat_1(k7_relat_1(k6_relat_1(X152),X153))),k7_relat_1(k6_relat_1(X152),X153))) ) | (~spl2_91 | ~spl2_203)),
% 4.11/0.89    inference(superposition,[],[f1236,f4371])).
% 4.11/0.89  fof(f1236,plain,(
% 4.11/0.89    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_91),
% 4.11/0.89    inference(avatar_component_clause,[],[f1235])).
% 4.11/0.89  fof(f4711,plain,(
% 4.11/0.89    spl2_208 | ~spl2_91 | ~spl2_203),
% 4.11/0.89    inference(avatar_split_clause,[],[f4446,f4370,f1235,f4709])).
% 4.11/0.89  fof(f4446,plain,(
% 4.11/0.89    ( ! [X151,X150] : (r1_tarski(k7_relat_1(k6_relat_1(X150),X151),k7_relat_1(k6_relat_1(X151),k2_relat_1(k7_relat_1(k6_relat_1(X150),X151))))) ) | (~spl2_91 | ~spl2_203)),
% 4.11/0.89    inference(superposition,[],[f1236,f4371])).
% 4.11/0.89  fof(f4372,plain,(
% 4.11/0.89    spl2_203 | ~spl2_78 | ~spl2_83 | ~spl2_200),
% 4.11/0.89    inference(avatar_split_clause,[],[f4364,f4329,f1056,f984,f4370])).
% 4.11/0.89  fof(f984,plain,(
% 4.11/0.89    spl2_78 <=> ! [X3,X5,X4] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 4.11/0.89  fof(f4329,plain,(
% 4.11/0.89    spl2_200 <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_200])])).
% 4.11/0.89  fof(f4364,plain,(
% 4.11/0.89    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) ) | (~spl2_78 | ~spl2_83 | ~spl2_200)),
% 4.11/0.89    inference(forward_demodulation,[],[f4349,f1057])).
% 4.11/0.89  fof(f4349,plain,(
% 4.11/0.89    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)) ) | (~spl2_78 | ~spl2_200)),
% 4.11/0.89    inference(superposition,[],[f4330,f985])).
% 4.11/0.89  fof(f985,plain,(
% 4.11/0.89    ( ! [X4,X5,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)) ) | ~spl2_78),
% 4.11/0.89    inference(avatar_component_clause,[],[f984])).
% 4.11/0.89  fof(f4330,plain,(
% 4.11/0.89    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))))) ) | ~spl2_200),
% 4.11/0.89    inference(avatar_component_clause,[],[f4329])).
% 4.11/0.89  fof(f4331,plain,(
% 4.11/0.89    spl2_200 | ~spl2_7 | ~spl2_15),
% 4.11/0.89    inference(avatar_split_clause,[],[f163,f158,f102,f4329])).
% 4.11/0.89  fof(f102,plain,(
% 4.11/0.89    spl2_7 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 4.11/0.89  fof(f158,plain,(
% 4.11/0.89    spl2_15 <=> ! [X5,X6] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 4.11/0.89  fof(f163,plain,(
% 4.11/0.89    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))))) ) | (~spl2_7 | ~spl2_15)),
% 4.11/0.89    inference(resolution,[],[f159,f103])).
% 4.11/0.89  fof(f103,plain,(
% 4.11/0.89    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_7),
% 4.11/0.89    inference(avatar_component_clause,[],[f102])).
% 4.11/0.89  fof(f159,plain,(
% 4.11/0.89    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) ) | ~spl2_15),
% 4.11/0.89    inference(avatar_component_clause,[],[f158])).
% 4.11/0.89  fof(f1237,plain,(
% 4.11/0.89    spl2_91 | ~spl2_52 | ~spl2_90),
% 4.11/0.89    inference(avatar_split_clause,[],[f1229,f1220,f601,f1235])).
% 4.11/0.89  fof(f601,plain,(
% 4.11/0.89    spl2_52 <=> ! [X3,X5,X4] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 4.11/0.89  fof(f1220,plain,(
% 4.11/0.89    spl2_90 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 4.11/0.89  fof(f1229,plain,(
% 4.11/0.89    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_52 | ~spl2_90)),
% 4.11/0.89    inference(superposition,[],[f602,f1221])).
% 4.11/0.89  fof(f1221,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | ~spl2_90),
% 4.11/0.89    inference(avatar_component_clause,[],[f1220])).
% 4.11/0.89  fof(f602,plain,(
% 4.11/0.89    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) ) | ~spl2_52),
% 4.11/0.89    inference(avatar_component_clause,[],[f601])).
% 4.11/0.89  fof(f1222,plain,(
% 4.11/0.89    spl2_90 | ~spl2_29 | ~spl2_89),
% 4.11/0.89    inference(avatar_split_clause,[],[f1214,f1205,f271,f1220])).
% 4.11/0.89  fof(f271,plain,(
% 4.11/0.89    spl2_29 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 4.11/0.89  fof(f1205,plain,(
% 4.11/0.89    spl2_89 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 4.11/0.89  fof(f1214,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | (~spl2_29 | ~spl2_89)),
% 4.11/0.89    inference(superposition,[],[f1206,f272])).
% 4.11/0.89  fof(f272,plain,(
% 4.11/0.89    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_29),
% 4.11/0.89    inference(avatar_component_clause,[],[f271])).
% 4.11/0.89  fof(f1206,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_89),
% 4.11/0.89    inference(avatar_component_clause,[],[f1205])).
% 4.11/0.89  fof(f1207,plain,(
% 4.11/0.89    spl2_89 | ~spl2_15 | ~spl2_22 | ~spl2_87),
% 4.11/0.89    inference(avatar_split_clause,[],[f1178,f1166,f208,f158,f1205])).
% 4.11/0.89  fof(f208,plain,(
% 4.11/0.89    spl2_22 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 4.11/0.89  fof(f1166,plain,(
% 4.11/0.89    spl2_87 <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 4.11/0.89  fof(f1178,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_15 | ~spl2_22 | ~spl2_87)),
% 4.11/0.89    inference(subsumption_resolution,[],[f1169,f159])).
% 4.11/0.89  fof(f1169,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_22 | ~spl2_87)),
% 4.11/0.89    inference(resolution,[],[f1167,f209])).
% 4.11/0.89  fof(f209,plain,(
% 4.11/0.89    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) ) | ~spl2_22),
% 4.11/0.89    inference(avatar_component_clause,[],[f208])).
% 4.11/0.89  fof(f1167,plain,(
% 4.11/0.89    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | ~spl2_87),
% 4.11/0.89    inference(avatar_component_clause,[],[f1166])).
% 4.11/0.89  fof(f1189,plain,(
% 4.11/0.89    ~spl2_88 | ~spl2_1 | ~spl2_2 | spl2_28 | ~spl2_77),
% 4.11/0.89    inference(avatar_split_clause,[],[f1159,f950,f266,f82,f78,f1186])).
% 4.11/0.89  fof(f78,plain,(
% 4.11/0.89    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 4.11/0.89  fof(f266,plain,(
% 4.11/0.89    spl2_28 <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 4.11/0.89  fof(f950,plain,(
% 4.11/0.89    spl2_77 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 4.11/0.89  fof(f1159,plain,(
% 4.11/0.89    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_28 | ~spl2_77)),
% 4.11/0.89    inference(backward_demodulation,[],[f268,f1158])).
% 4.11/0.89  fof(f1158,plain,(
% 4.11/0.89    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) ) | (~spl2_1 | ~spl2_2 | ~spl2_77)),
% 4.11/0.89    inference(forward_demodulation,[],[f1155,f83])).
% 4.11/0.89  fof(f1155,plain,(
% 4.11/0.89    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4))) ) | (~spl2_1 | ~spl2_77)),
% 4.11/0.89    inference(resolution,[],[f951,f79])).
% 4.11/0.89  fof(f79,plain,(
% 4.11/0.89    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 4.11/0.89    inference(avatar_component_clause,[],[f78])).
% 4.11/0.89  fof(f951,plain,(
% 4.11/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) | ~spl2_77),
% 4.11/0.89    inference(avatar_component_clause,[],[f950])).
% 4.11/0.89  fof(f268,plain,(
% 4.11/0.89    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_28),
% 4.11/0.89    inference(avatar_component_clause,[],[f266])).
% 4.11/0.89  fof(f1168,plain,(
% 4.11/0.89    spl2_87 | ~spl2_1 | ~spl2_2 | ~spl2_24 | ~spl2_77),
% 4.11/0.89    inference(avatar_split_clause,[],[f1162,f950,f216,f82,f78,f1166])).
% 4.11/0.89  fof(f216,plain,(
% 4.11/0.89    spl2_24 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 4.11/0.89  fof(f1162,plain,(
% 4.11/0.89    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_24 | ~spl2_77)),
% 4.11/0.89    inference(backward_demodulation,[],[f217,f1158])).
% 4.11/0.89  fof(f217,plain,(
% 4.11/0.89    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) ) | ~spl2_24),
% 4.11/0.89    inference(avatar_component_clause,[],[f216])).
% 4.11/0.89  fof(f1058,plain,(
% 4.11/0.89    spl2_83 | ~spl2_20 | ~spl2_26),
% 4.11/0.89    inference(avatar_split_clause,[],[f242,f232,f194,f1056])).
% 4.11/0.89  fof(f194,plain,(
% 4.11/0.89    spl2_20 <=> ! [X1,X2] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 4.11/0.89  fof(f242,plain,(
% 4.11/0.89    ( ! [X12,X13] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X12),X13))),X12)) ) | (~spl2_20 | ~spl2_26)),
% 4.11/0.89    inference(resolution,[],[f233,f195])).
% 4.11/0.89  fof(f195,plain,(
% 4.11/0.89    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) ) | ~spl2_20),
% 4.11/0.89    inference(avatar_component_clause,[],[f194])).
% 4.11/0.89  fof(f986,plain,(
% 4.11/0.89    spl2_78 | ~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_29 | ~spl2_30 | ~spl2_49),
% 4.11/0.89    inference(avatar_split_clause,[],[f563,f547,f275,f271,f145,f141,f78,f984])).
% 4.11/0.89  fof(f141,plain,(
% 4.11/0.89    spl2_13 <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 4.11/0.89  fof(f145,plain,(
% 4.11/0.89    spl2_14 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 4.11/0.89  fof(f275,plain,(
% 4.11/0.89    spl2_30 <=> ! [X3,X5,X4] : k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 4.11/0.89  fof(f547,plain,(
% 4.11/0.89    spl2_49 <=> ! [X5,X4,X6] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)))),
% 4.11/0.89    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 4.11/0.89  fof(f563,plain,(
% 4.11/0.89    ( ! [X4,X5,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)) ) | (~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_29 | ~spl2_30 | ~spl2_49)),
% 4.11/0.89    inference(backward_demodulation,[],[f276,f561])).
% 4.11/0.89  fof(f561,plain,(
% 4.11/0.89    ( ! [X6,X4,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))) ) | (~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_29 | ~spl2_49)),
% 4.11/0.89    inference(forward_demodulation,[],[f560,f146])).
% 4.11/0.89  fof(f146,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_14),
% 4.11/0.89    inference(avatar_component_clause,[],[f145])).
% 4.11/0.89  fof(f560,plain,(
% 4.11/0.89    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)) ) | (~spl2_1 | ~spl2_13 | ~spl2_29 | ~spl2_49)),
% 4.11/0.89    inference(forward_demodulation,[],[f559,f272])).
% 4.11/0.89  fof(f559,plain,(
% 4.11/0.89    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))) ) | (~spl2_1 | ~spl2_13 | ~spl2_49)),
% 4.11/0.89    inference(forward_demodulation,[],[f555,f142])).
% 4.11/0.89  fof(f142,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_13),
% 4.11/0.89    inference(avatar_component_clause,[],[f141])).
% 4.11/0.89  fof(f555,plain,(
% 4.11/0.89    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6)))) ) | (~spl2_1 | ~spl2_49)),
% 4.11/0.89    inference(resolution,[],[f548,f79])).
% 4.11/0.89  fof(f548,plain,(
% 4.11/0.89    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4))) ) | ~spl2_49),
% 4.11/0.89    inference(avatar_component_clause,[],[f547])).
% 4.11/0.89  fof(f276,plain,(
% 4.11/0.89    ( ! [X4,X5,X3] : (k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))) ) | ~spl2_30),
% 4.11/0.89    inference(avatar_component_clause,[],[f275])).
% 4.11/0.89  fof(f952,plain,(
% 4.11/0.89    spl2_77),
% 4.11/0.89    inference(avatar_split_clause,[],[f76,f950])).
% 4.11/0.89  fof(f76,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 4.11/0.89    inference(definition_unfolding,[],[f55,f73])).
% 4.11/0.89  fof(f73,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.11/0.89    inference(definition_unfolding,[],[f51,f72])).
% 4.11/0.89  fof(f72,plain,(
% 4.11/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.11/0.89    inference(definition_unfolding,[],[f52,f71])).
% 4.11/0.89  fof(f71,plain,(
% 4.11/0.89    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.11/0.89    inference(definition_unfolding,[],[f63,f70])).
% 4.11/0.89  fof(f70,plain,(
% 4.11/0.89    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.11/0.89    inference(definition_unfolding,[],[f64,f69])).
% 4.11/0.89  fof(f69,plain,(
% 4.11/0.89    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.11/0.89    inference(definition_unfolding,[],[f65,f68])).
% 4.11/0.90  fof(f68,plain,(
% 4.11/0.90    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.11/0.90    inference(definition_unfolding,[],[f66,f67])).
% 4.11/0.90  fof(f67,plain,(
% 4.11/0.90    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f7])).
% 4.11/0.90  fof(f7,axiom,(
% 4.11/0.90    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 4.11/0.90  fof(f66,plain,(
% 4.11/0.90    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f6])).
% 4.11/0.90  fof(f6,axiom,(
% 4.11/0.90    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 4.11/0.90  fof(f65,plain,(
% 4.11/0.90    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f5])).
% 4.11/0.90  fof(f5,axiom,(
% 4.11/0.90    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 4.11/0.90  fof(f64,plain,(
% 4.11/0.90    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f4])).
% 4.11/0.90  fof(f4,axiom,(
% 4.11/0.90    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 4.11/0.90  fof(f63,plain,(
% 4.11/0.90    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f3])).
% 4.11/0.90  fof(f3,axiom,(
% 4.11/0.90    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.11/0.90  fof(f52,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f2])).
% 4.11/0.90  fof(f2,axiom,(
% 4.11/0.90    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.11/0.90  fof(f51,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.11/0.90    inference(cnf_transformation,[],[f8])).
% 4.11/0.90  fof(f8,axiom,(
% 4.11/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 4.11/0.90  fof(f55,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f31])).
% 4.11/0.90  fof(f31,plain,(
% 4.11/0.90    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f21])).
% 4.11/0.90  fof(f21,axiom,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 4.11/0.90  fof(f603,plain,(
% 4.11/0.90    spl2_52 | ~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_29 | ~spl2_41 | ~spl2_49),
% 4.11/0.90    inference(avatar_split_clause,[],[f573,f547,f367,f271,f145,f141,f78,f601])).
% 4.11/0.90  fof(f367,plain,(
% 4.11/0.90    spl2_41 <=> ! [X3,X5,X4] : r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 4.11/0.90  fof(f573,plain,(
% 4.11/0.90    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) ) | (~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_29 | ~spl2_41 | ~spl2_49)),
% 4.11/0.90    inference(backward_demodulation,[],[f368,f561])).
% 4.11/0.90  fof(f368,plain,(
% 4.11/0.90    ( ! [X4,X5,X3] : (r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))) ) | ~spl2_41),
% 4.11/0.90    inference(avatar_component_clause,[],[f367])).
% 4.11/0.90  fof(f549,plain,(
% 4.11/0.90    spl2_49 | ~spl2_1 | ~spl2_36),
% 4.11/0.90    inference(avatar_split_clause,[],[f537,f308,f78,f547])).
% 4.11/0.90  fof(f308,plain,(
% 4.11/0.90    spl2_36 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 4.11/0.90  fof(f537,plain,(
% 4.11/0.90    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4))) ) | (~spl2_1 | ~spl2_36)),
% 4.11/0.90    inference(resolution,[],[f309,f79])).
% 4.11/0.90  fof(f309,plain,(
% 4.11/0.90    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) ) | ~spl2_36),
% 4.11/0.90    inference(avatar_component_clause,[],[f308])).
% 4.11/0.90  fof(f369,plain,(
% 4.11/0.90    spl2_41 | ~spl2_4 | ~spl2_15 | ~spl2_30),
% 4.11/0.90    inference(avatar_split_clause,[],[f340,f275,f158,f90,f367])).
% 4.11/0.90  fof(f90,plain,(
% 4.11/0.90    spl2_4 <=> ! [X1,X0] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 4.11/0.90  fof(f340,plain,(
% 4.11/0.90    ( ! [X4,X5,X3] : (r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))) ) | (~spl2_4 | ~spl2_15 | ~spl2_30)),
% 4.11/0.90    inference(subsumption_resolution,[],[f335,f159])).
% 4.11/0.90  fof(f335,plain,(
% 4.11/0.90    ( ! [X4,X5,X3] : (r1_tarski(k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) ) | (~spl2_4 | ~spl2_30)),
% 4.11/0.90    inference(superposition,[],[f91,f276])).
% 4.11/0.90  fof(f91,plain,(
% 4.11/0.90    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) ) | ~spl2_4),
% 4.11/0.90    inference(avatar_component_clause,[],[f90])).
% 4.11/0.90  fof(f310,plain,(
% 4.11/0.90    spl2_36),
% 4.11/0.90    inference(avatar_split_clause,[],[f60,f308])).
% 4.11/0.90  fof(f60,plain,(
% 4.11/0.90    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f37])).
% 4.11/0.90  fof(f37,plain,(
% 4.11/0.90    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f13])).
% 4.11/0.90  fof(f13,axiom,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 4.11/0.90  fof(f277,plain,(
% 4.11/0.90    spl2_30 | ~spl2_10 | ~spl2_15),
% 4.11/0.90    inference(avatar_split_clause,[],[f162,f158,f122,f275])).
% 4.11/0.90  fof(f122,plain,(
% 4.11/0.90    spl2_10 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 4.11/0.90  fof(f162,plain,(
% 4.11/0.90    ( ! [X4,X5,X3] : (k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))) ) | (~spl2_10 | ~spl2_15)),
% 4.11/0.90    inference(resolution,[],[f159,f123])).
% 4.11/0.90  fof(f123,plain,(
% 4.11/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_10),
% 4.11/0.90    inference(avatar_component_clause,[],[f122])).
% 4.11/0.90  fof(f273,plain,(
% 4.11/0.90    spl2_29 | ~spl2_11 | ~spl2_15),
% 4.11/0.90    inference(avatar_split_clause,[],[f161,f158,f126,f271])).
% 4.11/0.90  fof(f126,plain,(
% 4.11/0.90    spl2_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 4.11/0.90  fof(f161,plain,(
% 4.11/0.90    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_11 | ~spl2_15)),
% 4.11/0.90    inference(resolution,[],[f159,f127])).
% 4.11/0.90  fof(f127,plain,(
% 4.11/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_11),
% 4.11/0.90    inference(avatar_component_clause,[],[f126])).
% 4.11/0.90  fof(f269,plain,(
% 4.11/0.90    ~spl2_28 | ~spl2_1 | ~spl2_10 | ~spl2_11),
% 4.11/0.90    inference(avatar_split_clause,[],[f135,f126,f122,f78,f266])).
% 4.11/0.90  fof(f135,plain,(
% 4.11/0.90    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_10 | ~spl2_11)),
% 4.11/0.90    inference(backward_demodulation,[],[f131,f134])).
% 4.11/0.90  fof(f134,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_10 | ~spl2_11)),
% 4.11/0.90    inference(backward_demodulation,[],[f129,f132])).
% 4.11/0.90  fof(f132,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_11)),
% 4.11/0.90    inference(resolution,[],[f127,f79])).
% 4.11/0.90  fof(f129,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_10)),
% 4.11/0.90    inference(resolution,[],[f123,f79])).
% 4.11/0.90  fof(f131,plain,(
% 4.11/0.90    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | (~spl2_1 | ~spl2_10)),
% 4.11/0.90    inference(backward_demodulation,[],[f74,f129])).
% 4.11/0.90  fof(f74,plain,(
% 4.11/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 4.11/0.90    inference(definition_unfolding,[],[f43,f73])).
% 4.11/0.90  fof(f43,plain,(
% 4.11/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 4.11/0.90    inference(cnf_transformation,[],[f42])).
% 4.11/0.90  fof(f42,plain,(
% 4.11/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 4.11/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f41])).
% 4.11/0.90  fof(f41,plain,(
% 4.11/0.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 4.11/0.90    introduced(choice_axiom,[])).
% 4.11/0.90  fof(f25,plain,(
% 4.11/0.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f24])).
% 4.11/0.90  fof(f24,negated_conjecture,(
% 4.11/0.90    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 4.11/0.90    inference(negated_conjecture,[],[f23])).
% 4.11/0.90  fof(f23,conjecture,(
% 4.11/0.90    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 4.11/0.90  fof(f253,plain,(
% 4.11/0.90    spl2_27 | ~spl2_1 | ~spl2_3 | ~spl2_14 | ~spl2_23),
% 4.11/0.90    inference(avatar_split_clause,[],[f248,f212,f145,f86,f78,f251])).
% 4.11/0.90  fof(f86,plain,(
% 4.11/0.90    spl2_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 4.11/0.90  fof(f212,plain,(
% 4.11/0.90    spl2_23 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 4.11/0.90  fof(f248,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) ) | (~spl2_1 | ~spl2_3 | ~spl2_14 | ~spl2_23)),
% 4.11/0.90    inference(forward_demodulation,[],[f247,f146])).
% 4.11/0.90  fof(f247,plain,(
% 4.11/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_3 | ~spl2_23)),
% 4.11/0.90    inference(forward_demodulation,[],[f244,f87])).
% 4.11/0.90  fof(f87,plain,(
% 4.11/0.90    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 4.11/0.90    inference(avatar_component_clause,[],[f86])).
% 4.11/0.90  fof(f244,plain,(
% 4.11/0.90    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_23)),
% 4.11/0.90    inference(resolution,[],[f213,f79])).
% 4.11/0.90  fof(f213,plain,(
% 4.11/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl2_23),
% 4.11/0.90    inference(avatar_component_clause,[],[f212])).
% 4.11/0.90  fof(f234,plain,(
% 4.11/0.90    spl2_26 | ~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_22),
% 4.11/0.90    inference(avatar_split_clause,[],[f222,f208,f145,f82,f78,f232])).
% 4.11/0.90  fof(f222,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_22)),
% 4.11/0.90    inference(forward_demodulation,[],[f221,f146])).
% 4.11/0.90  fof(f221,plain,(
% 4.11/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_2 | ~spl2_22)),
% 4.11/0.90    inference(subsumption_resolution,[],[f220,f79])).
% 4.11/0.90  fof(f220,plain,(
% 4.11/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_22)),
% 4.11/0.90    inference(superposition,[],[f209,f83])).
% 4.11/0.90  fof(f218,plain,(
% 4.11/0.90    spl2_24),
% 4.11/0.90    inference(avatar_split_clause,[],[f75,f216])).
% 4.11/0.90  fof(f75,plain,(
% 4.11/0.90    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 4.11/0.90    inference(definition_unfolding,[],[f50,f73])).
% 4.11/0.90  fof(f50,plain,(
% 4.11/0.90    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f1])).
% 4.11/0.90  fof(f1,axiom,(
% 4.11/0.90    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.11/0.90  fof(f214,plain,(
% 4.11/0.90    spl2_23),
% 4.11/0.90    inference(avatar_split_clause,[],[f59,f212])).
% 4.11/0.90  fof(f59,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f36])).
% 4.11/0.90  fof(f36,plain,(
% 4.11/0.90    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(flattening,[],[f35])).
% 4.11/0.90  fof(f35,plain,(
% 4.11/0.90    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f19])).
% 4.11/0.90  fof(f19,axiom,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 4.11/0.90  fof(f210,plain,(
% 4.11/0.90    spl2_22),
% 4.11/0.90    inference(avatar_split_clause,[],[f58,f208])).
% 4.11/0.90  fof(f58,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f34])).
% 4.11/0.90  fof(f34,plain,(
% 4.11/0.90    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(flattening,[],[f33])).
% 4.11/0.90  fof(f33,plain,(
% 4.11/0.90    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f18])).
% 4.11/0.90  fof(f18,axiom,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 4.11/0.90  fof(f196,plain,(
% 4.11/0.90    spl2_20 | ~spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_14),
% 4.11/0.90    inference(avatar_split_clause,[],[f187,f145,f137,f86,f78,f194])).
% 4.11/0.90  fof(f137,plain,(
% 4.11/0.90    spl2_12 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 4.11/0.90  fof(f187,plain,(
% 4.11/0.90    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) ) | (~spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_14)),
% 4.11/0.90    inference(forward_demodulation,[],[f186,f87])).
% 4.11/0.90  fof(f186,plain,(
% 4.11/0.90    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))) ) | (~spl2_1 | ~spl2_12 | ~spl2_14)),
% 4.11/0.90    inference(subsumption_resolution,[],[f185,f79])).
% 4.11/0.90  fof(f185,plain,(
% 4.11/0.90    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_12 | ~spl2_14)),
% 4.11/0.90    inference(subsumption_resolution,[],[f180,f79])).
% 4.11/0.90  fof(f180,plain,(
% 4.11/0.90    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_12 | ~spl2_14)),
% 4.11/0.90    inference(superposition,[],[f138,f146])).
% 4.11/0.90  fof(f138,plain,(
% 4.11/0.90    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_12),
% 4.11/0.90    inference(avatar_component_clause,[],[f137])).
% 4.11/0.90  fof(f160,plain,(
% 4.11/0.90    spl2_15 | ~spl2_1 | ~spl2_6 | ~spl2_14),
% 4.11/0.90    inference(avatar_split_clause,[],[f156,f145,f98,f78,f158])).
% 4.11/0.90  fof(f98,plain,(
% 4.11/0.90    spl2_6 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.11/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 4.11/0.90  fof(f156,plain,(
% 4.11/0.90    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) ) | (~spl2_1 | ~spl2_6 | ~spl2_14)),
% 4.11/0.90    inference(subsumption_resolution,[],[f155,f79])).
% 4.11/0.90  fof(f155,plain,(
% 4.11/0.90    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X5))) ) | (~spl2_1 | ~spl2_6 | ~spl2_14)),
% 4.11/0.90    inference(subsumption_resolution,[],[f152,f79])).
% 4.11/0.90  fof(f152,plain,(
% 4.11/0.90    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) ) | (~spl2_6 | ~spl2_14)),
% 4.11/0.90    inference(superposition,[],[f99,f146])).
% 4.11/0.90  fof(f99,plain,(
% 4.11/0.90    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 4.11/0.90    inference(avatar_component_clause,[],[f98])).
% 4.11/0.90  fof(f147,plain,(
% 4.11/0.90    spl2_14 | ~spl2_1 | ~spl2_11),
% 4.11/0.90    inference(avatar_split_clause,[],[f132,f126,f78,f145])).
% 4.11/0.90  fof(f143,plain,(
% 4.11/0.90    spl2_13 | ~spl2_1 | ~spl2_10 | ~spl2_11),
% 4.11/0.90    inference(avatar_split_clause,[],[f134,f126,f122,f78,f141])).
% 4.11/0.90  fof(f139,plain,(
% 4.11/0.90    spl2_12),
% 4.11/0.90    inference(avatar_split_clause,[],[f48,f137])).
% 4.11/0.90  fof(f48,plain,(
% 4.11/0.90    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f27])).
% 4.11/0.90  fof(f27,plain,(
% 4.11/0.90    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.11/0.90    inference(ennf_transformation,[],[f14])).
% 4.11/0.90  fof(f14,axiom,(
% 4.11/0.90    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 4.11/0.90  fof(f128,plain,(
% 4.11/0.90    spl2_11),
% 4.11/0.90    inference(avatar_split_clause,[],[f54,f126])).
% 4.11/0.90  fof(f54,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f30])).
% 4.11/0.90  fof(f30,plain,(
% 4.11/0.90    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f22])).
% 4.11/0.90  fof(f22,axiom,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 4.11/0.90  fof(f124,plain,(
% 4.11/0.90    spl2_10),
% 4.11/0.90    inference(avatar_split_clause,[],[f53,f122])).
% 4.11/0.90  fof(f53,plain,(
% 4.11/0.90    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f29])).
% 4.11/0.90  fof(f29,plain,(
% 4.11/0.90    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f12])).
% 4.11/0.90  fof(f12,axiom,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 4.11/0.90  fof(f104,plain,(
% 4.11/0.90    spl2_7),
% 4.11/0.90    inference(avatar_split_clause,[],[f47,f102])).
% 4.11/0.90  fof(f47,plain,(
% 4.11/0.90    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f26])).
% 4.11/0.90  fof(f26,plain,(
% 4.11/0.90    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 4.11/0.90    inference(ennf_transformation,[],[f20])).
% 4.11/0.90  fof(f20,axiom,(
% 4.11/0.90    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 4.11/0.90  fof(f100,plain,(
% 4.11/0.90    spl2_6),
% 4.11/0.90    inference(avatar_split_clause,[],[f62,f98])).
% 4.11/0.90  fof(f62,plain,(
% 4.11/0.90    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f40])).
% 4.11/0.90  fof(f40,plain,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.11/0.90    inference(flattening,[],[f39])).
% 4.11/0.90  fof(f39,plain,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 4.11/0.90    inference(ennf_transformation,[],[f9])).
% 4.11/0.90  fof(f9,axiom,(
% 4.11/0.90    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 4.11/0.90  fof(f92,plain,(
% 4.11/0.90    spl2_4),
% 4.11/0.90    inference(avatar_split_clause,[],[f56,f90])).
% 4.11/0.90  fof(f56,plain,(
% 4.11/0.90    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 4.11/0.90    inference(cnf_transformation,[],[f32])).
% 4.11/0.90  fof(f32,plain,(
% 4.11/0.90    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 4.11/0.90    inference(ennf_transformation,[],[f17])).
% 4.11/0.90  fof(f17,axiom,(
% 4.11/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 4.11/0.90  fof(f88,plain,(
% 4.11/0.90    spl2_3),
% 4.11/0.90    inference(avatar_split_clause,[],[f46,f86])).
% 4.11/0.90  fof(f46,plain,(
% 4.11/0.90    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.11/0.90    inference(cnf_transformation,[],[f16])).
% 4.11/0.90  fof(f16,axiom,(
% 4.11/0.90    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 4.11/0.90  fof(f84,plain,(
% 4.11/0.90    spl2_2),
% 4.11/0.90    inference(avatar_split_clause,[],[f45,f82])).
% 4.11/0.90  fof(f45,plain,(
% 4.11/0.90    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.11/0.90    inference(cnf_transformation,[],[f16])).
% 4.11/0.90  fof(f80,plain,(
% 4.11/0.90    spl2_1),
% 4.11/0.90    inference(avatar_split_clause,[],[f44,f78])).
% 4.11/0.90  fof(f44,plain,(
% 4.11/0.90    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.11/0.90    inference(cnf_transformation,[],[f10])).
% 4.11/0.90  fof(f10,axiom,(
% 4.11/0.90    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 4.11/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 4.11/0.90  % SZS output end Proof for theBenchmark
% 4.11/0.90  % (14674)------------------------------
% 4.11/0.90  % (14674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.90  % (14674)Termination reason: Refutation
% 4.11/0.90  
% 4.11/0.90  % (14674)Memory used [KB]: 11769
% 4.11/0.90  % (14674)Time elapsed: 0.430 s
% 4.11/0.90  % (14674)------------------------------
% 4.11/0.90  % (14674)------------------------------
% 4.11/0.91  % (14666)Success in time 0.54 s
%------------------------------------------------------------------------------
