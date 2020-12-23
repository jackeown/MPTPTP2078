%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:41 EST 2020

% Result     : Theorem 22.31s
% Output     : Refutation 22.31s
% Verified   : 
% Statistics : Number of formulae       :  250 ( 493 expanded)
%              Number of leaves         :   65 ( 258 expanded)
%              Depth                    :   10
%              Number of atoms          :  675 (1226 expanded)
%              Number of equality atoms :  148 ( 338 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f59,f63,f67,f71,f75,f79,f87,f96,f112,f120,f137,f141,f166,f172,f199,f255,f1055,f1064,f1664,f1681,f1713,f2700,f4643,f10441,f32867,f40260,f40452,f43075,f43077,f43559,f43690,f43788,f44104,f44128,f44132,f44136,f44408,f45682,f45693,f47837,f48753,f50526,f57080,f78082,f80247,f84671,f87637,f89281,f97799,f107897])).

fof(f107897,plain,
    ( ~ spl4_4
    | spl4_14
    | ~ spl4_935
    | ~ spl4_3499
    | ~ spl4_5196
    | ~ spl4_5315
    | ~ spl4_5387
    | ~ spl4_5646 ),
    inference(avatar_contradiction_clause,[],[f107896])).

fof(f107896,plain,
    ( $false
    | ~ spl4_4
    | spl4_14
    | ~ spl4_935
    | ~ spl4_3499
    | ~ spl4_5196
    | ~ spl4_5315
    | ~ spl4_5387
    | ~ spl4_5646 ),
    inference(subsumption_resolution,[],[f107895,f40451])).

fof(f40451,plain,
    ( ! [X668,X670,X667,X669] : k2_xboole_0(k3_xboole_0(X669,X667),k2_xboole_0(X670,k3_xboole_0(X667,X668))) = k2_xboole_0(X670,k3_xboole_0(X667,k2_xboole_0(X668,X669)))
    | ~ spl4_3499 ),
    inference(avatar_component_clause,[],[f40450])).

fof(f40450,plain,
    ( spl4_3499
  <=> ! [X669,X667,X670,X668] : k2_xboole_0(k3_xboole_0(X669,X667),k2_xboole_0(X670,k3_xboole_0(X667,X668))) = k2_xboole_0(X670,k3_xboole_0(X667,k2_xboole_0(X668,X669))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3499])])).

fof(f107895,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)))
    | ~ spl4_4
    | spl4_14
    | ~ spl4_935
    | ~ spl4_5196
    | ~ spl4_5315
    | ~ spl4_5387
    | ~ spl4_5646 ),
    inference(forward_demodulation,[],[f107894,f84046])).

fof(f84046,plain,
    ( ! [X26,X24,X25] : k3_xboole_0(X24,k2_xboole_0(X26,X25)) = k3_xboole_0(k2_xboole_0(X25,X26),X24)
    | ~ spl4_5196 ),
    inference(avatar_component_clause,[],[f84045])).

fof(f84045,plain,
    ( spl4_5196
  <=> ! [X25,X24,X26] : k3_xboole_0(X24,k2_xboole_0(X26,X25)) = k3_xboole_0(k2_xboole_0(X25,X26),X24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5196])])).

fof(f107894,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))
    | ~ spl4_4
    | spl4_14
    | ~ spl4_935
    | ~ spl4_5315
    | ~ spl4_5387
    | ~ spl4_5646 ),
    inference(forward_demodulation,[],[f107893,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107893,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK2))
    | spl4_14
    | ~ spl4_935
    | ~ spl4_5315
    | ~ spl4_5387
    | ~ spl4_5646 ),
    inference(forward_demodulation,[],[f107892,f97798])).

fof(f97798,plain,
    ( ! [X732,X730,X733,X731] : k3_xboole_0(k2_xboole_0(X732,X731),k2_xboole_0(X733,k3_xboole_0(X730,X731))) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X732,X731),X733),k3_xboole_0(X730,X731))
    | ~ spl4_5646 ),
    inference(avatar_component_clause,[],[f97797])).

fof(f97797,plain,
    ( spl4_5646
  <=> ! [X731,X733,X730,X732] : k3_xboole_0(k2_xboole_0(X732,X731),k2_xboole_0(X733,k3_xboole_0(X730,X731))) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X732,X731),X733),k3_xboole_0(X730,X731)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5646])])).

fof(f107892,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | spl4_14
    | ~ spl4_935
    | ~ spl4_5315
    | ~ spl4_5387 ),
    inference(forward_demodulation,[],[f107891,f87010])).

fof(f87010,plain,
    ( ! [X45,X43,X44,X42] : k3_xboole_0(k2_xboole_0(X42,X43),k2_xboole_0(X45,X44)) = k3_xboole_0(k2_xboole_0(X43,X42),k2_xboole_0(X44,X45))
    | ~ spl4_5315 ),
    inference(avatar_component_clause,[],[f87009])).

fof(f87009,plain,
    ( spl4_5315
  <=> ! [X42,X44,X43,X45] : k3_xboole_0(k2_xboole_0(X42,X43),k2_xboole_0(X45,X44)) = k3_xboole_0(k2_xboole_0(X43,X42),k2_xboole_0(X44,X45)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5315])])).

fof(f107891,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1))
    | spl4_14
    | ~ spl4_935
    | ~ spl4_5387 ),
    inference(forward_demodulation,[],[f107275,f88913])).

fof(f88913,plain,
    ( ! [X78,X76,X77,X75] : k3_xboole_0(k2_xboole_0(X76,X75),k2_xboole_0(X77,X78)) = k3_xboole_0(k2_xboole_0(X78,X77),k2_xboole_0(X75,X76))
    | ~ spl4_5387 ),
    inference(avatar_component_clause,[],[f88912])).

fof(f88912,plain,
    ( spl4_5387
  <=> ! [X75,X77,X76,X78] : k3_xboole_0(k2_xboole_0(X76,X75),k2_xboole_0(X77,X78)) = k3_xboole_0(k2_xboole_0(X78,X77),k2_xboole_0(X75,X76)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5387])])).

fof(f107275,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2))
    | spl4_14
    | ~ spl4_935 ),
    inference(superposition,[],[f95,f10439])).

fof(f10439,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2))
    | ~ spl4_935 ),
    inference(avatar_component_clause,[],[f10438])).

fof(f10438,plain,
    ( spl4_935
  <=> ! [X1,X0,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_935])])).

fof(f95,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_14
  <=> k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) = k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f97799,plain,
    ( spl4_5646
    | ~ spl4_195
    | ~ spl4_3956 ),
    inference(avatar_split_clause,[],[f97513,f44406,f1678,f97797])).

fof(f1678,plain,
    ( spl4_195
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_195])])).

fof(f44406,plain,
    ( spl4_3956
  <=> ! [X276,X275,X277] : k3_xboole_0(X275,X276) = k3_xboole_0(k3_xboole_0(X275,X276),k2_xboole_0(X277,X276)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3956])])).

fof(f97513,plain,
    ( ! [X732,X730,X733,X731] : k3_xboole_0(k2_xboole_0(X732,X731),k2_xboole_0(X733,k3_xboole_0(X730,X731))) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X732,X731),X733),k3_xboole_0(X730,X731))
    | ~ spl4_195
    | ~ spl4_3956 ),
    inference(superposition,[],[f1679,f44407])).

fof(f44407,plain,
    ( ! [X277,X275,X276] : k3_xboole_0(X275,X276) = k3_xboole_0(k3_xboole_0(X275,X276),k2_xboole_0(X277,X276))
    | ~ spl4_3956 ),
    inference(avatar_component_clause,[],[f44406])).

fof(f1679,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X1,X0))
    | ~ spl4_195 ),
    inference(avatar_component_clause,[],[f1678])).

fof(f89281,plain,
    ( spl4_5387
    | ~ spl4_5143
    | ~ spl4_5196 ),
    inference(avatar_split_clause,[],[f88704,f84045,f77901,f88912])).

fof(f77901,plain,
    ( spl4_5143
  <=> ! [X9,X8,X10] : k3_xboole_0(X8,k2_xboole_0(X9,X10)) = k3_xboole_0(X8,k2_xboole_0(X10,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5143])])).

fof(f88704,plain,
    ( ! [X1942,X1940,X1943,X1941] : k3_xboole_0(k2_xboole_0(X1942,X1943),k2_xboole_0(X1941,X1940)) = k3_xboole_0(k2_xboole_0(X1940,X1941),k2_xboole_0(X1943,X1942))
    | ~ spl4_5143
    | ~ spl4_5196 ),
    inference(superposition,[],[f77902,f84046])).

fof(f77902,plain,
    ( ! [X10,X8,X9] : k3_xboole_0(X8,k2_xboole_0(X9,X10)) = k3_xboole_0(X8,k2_xboole_0(X10,X9))
    | ~ spl4_5143 ),
    inference(avatar_component_clause,[],[f77901])).

fof(f87637,plain,
    ( spl4_5315
    | ~ spl4_5143
    | ~ spl4_5190 ),
    inference(avatar_split_clause,[],[f86807,f80191,f77901,f87009])).

fof(f80191,plain,
    ( spl4_5190
  <=> ! [X7,X8,X6] : k3_xboole_0(k2_xboole_0(X6,X7),X8) = k3_xboole_0(k2_xboole_0(X7,X6),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5190])])).

fof(f86807,plain,
    ( ! [X1936,X1934,X1937,X1935] : k3_xboole_0(k2_xboole_0(X1935,X1934),k2_xboole_0(X1936,X1937)) = k3_xboole_0(k2_xboole_0(X1934,X1935),k2_xboole_0(X1937,X1936))
    | ~ spl4_5143
    | ~ spl4_5190 ),
    inference(superposition,[],[f77902,f80192])).

fof(f80192,plain,
    ( ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),X8) = k3_xboole_0(k2_xboole_0(X7,X6),X8)
    | ~ spl4_5190 ),
    inference(avatar_component_clause,[],[f80191])).

fof(f84671,plain,
    ( spl4_5196
    | ~ spl4_3
    | ~ spl4_5143 ),
    inference(avatar_split_clause,[],[f83617,f77901,f45,f84045])).

fof(f45,plain,
    ( spl4_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f83617,plain,
    ( ! [X263,X265,X264] : k3_xboole_0(X263,k2_xboole_0(X265,X264)) = k3_xboole_0(k2_xboole_0(X264,X265),X263)
    | ~ spl4_3
    | ~ spl4_5143 ),
    inference(superposition,[],[f46,f77902])).

fof(f46,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f80247,plain,
    ( spl4_5190
    | ~ spl4_6
    | ~ spl4_3577
    | ~ spl4_4214
    | ~ spl4_4258
    | ~ spl4_4727 ),
    inference(avatar_split_clause,[],[f80246,f57078,f48750,f47828,f41837,f57,f80191])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f41837,plain,
    ( spl4_3577
  <=> ! [X5,X4] : k3_xboole_0(k2_xboole_0(X5,X5),X4) = k3_xboole_0(X5,k2_xboole_0(X4,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3577])])).

fof(f47828,plain,
    ( spl4_4214
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4214])])).

fof(f48750,plain,
    ( spl4_4258
  <=> ! [X348,X347] : k2_xboole_0(X347,X348) = k2_xboole_0(X347,k2_xboole_0(X348,X347)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4258])])).

fof(f57078,plain,
    ( spl4_4727
  <=> ! [X1510,X1508,X1509] : k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)) = k2_xboole_0(X1508,k2_xboole_0(X1509,k2_xboole_0(X1508,X1510))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4727])])).

fof(f80246,plain,
    ( ! [X47,X45,X46] : k3_xboole_0(k2_xboole_0(X45,X46),X47) = k3_xboole_0(k2_xboole_0(X46,X45),X47)
    | ~ spl4_6
    | ~ spl4_3577
    | ~ spl4_4214
    | ~ spl4_4258
    | ~ spl4_4727 ),
    inference(forward_demodulation,[],[f80245,f47829])).

fof(f47829,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl4_4214 ),
    inference(avatar_component_clause,[],[f47828])).

fof(f80245,plain,
    ( ! [X47,X45,X46] : k3_xboole_0(k2_xboole_0(X45,X46),k2_xboole_0(X47,X47)) = k3_xboole_0(k2_xboole_0(X46,X45),X47)
    | ~ spl4_6
    | ~ spl4_3577
    | ~ spl4_4258
    | ~ spl4_4727 ),
    inference(forward_demodulation,[],[f80244,f48751])).

fof(f48751,plain,
    ( ! [X347,X348] : k2_xboole_0(X347,X348) = k2_xboole_0(X347,k2_xboole_0(X348,X347))
    | ~ spl4_4258 ),
    inference(avatar_component_clause,[],[f48750])).

fof(f80244,plain,
    ( ! [X47,X45,X46] : k3_xboole_0(k2_xboole_0(X45,X46),k2_xboole_0(X47,X47)) = k3_xboole_0(k2_xboole_0(X46,k2_xboole_0(X45,X46)),X47)
    | ~ spl4_6
    | ~ spl4_3577
    | ~ spl4_4727 ),
    inference(forward_demodulation,[],[f79147,f57079])).

fof(f57079,plain,
    ( ! [X1509,X1508,X1510] : k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)) = k2_xboole_0(X1508,k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)))
    | ~ spl4_4727 ),
    inference(avatar_component_clause,[],[f57078])).

fof(f79147,plain,
    ( ! [X47,X45,X46] : k3_xboole_0(k2_xboole_0(X45,X46),k2_xboole_0(X47,X47)) = k3_xboole_0(k2_xboole_0(X45,k2_xboole_0(X46,k2_xboole_0(X45,X46))),X47)
    | ~ spl4_6
    | ~ spl4_3577 ),
    inference(superposition,[],[f41838,f58])).

fof(f58,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f41838,plain,
    ( ! [X4,X5] : k3_xboole_0(k2_xboole_0(X5,X5),X4) = k3_xboole_0(X5,k2_xboole_0(X4,X4))
    | ~ spl4_3577 ),
    inference(avatar_component_clause,[],[f41837])).

fof(f78082,plain,
    ( spl4_5143
    | ~ spl4_7
    | ~ spl4_197 ),
    inference(avatar_split_clause,[],[f77449,f1692,f61,f77901])).

fof(f61,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1692,plain,
    ( spl4_197
  <=> ! [X3,X5,X4] : k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X3,X5),k3_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).

fof(f77449,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1))
    | ~ spl4_7
    | ~ spl4_197 ),
    inference(superposition,[],[f62,f1693])).

fof(f1693,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X3,X5),k3_xboole_0(X3,X4))
    | ~ spl4_197 ),
    inference(avatar_component_clause,[],[f1692])).

fof(f62,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f57080,plain,
    ( spl4_4727
    | ~ spl4_3886
    | ~ spl4_4319 ),
    inference(avatar_split_clause,[],[f56752,f50523,f44126,f57078])).

fof(f44126,plain,
    ( spl4_3886
  <=> ! [X25,X23,X24] : k3_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X23,X25))) = X23 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3886])])).

fof(f50523,plain,
    ( spl4_4319
  <=> ! [X1,X2] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4319])])).

fof(f56752,plain,
    ( ! [X1509,X1508,X1510] : k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)) = k2_xboole_0(X1508,k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)))
    | ~ spl4_3886
    | ~ spl4_4319 ),
    inference(superposition,[],[f50524,f44127])).

fof(f44127,plain,
    ( ! [X24,X23,X25] : k3_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X23,X25))) = X23
    | ~ spl4_3886 ),
    inference(avatar_component_clause,[],[f44126])).

fof(f50524,plain,
    ( ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1
    | ~ spl4_4319 ),
    inference(avatar_component_clause,[],[f50523])).

fof(f50526,plain,
    ( spl4_4319
    | ~ spl4_3
    | ~ spl4_4141 ),
    inference(avatar_split_clause,[],[f49979,f45691,f45,f50523])).

fof(f45691,plain,
    ( spl4_4141
  <=> ! [X240,X239] : k2_xboole_0(k3_xboole_0(X239,X240),X239) = X239 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4141])])).

fof(f49979,plain,
    ( ! [X4,X3] : k2_xboole_0(k3_xboole_0(X4,X3),X3) = X3
    | ~ spl4_3
    | ~ spl4_4141 ),
    inference(superposition,[],[f45692,f46])).

fof(f45692,plain,
    ( ! [X239,X240] : k2_xboole_0(k3_xboole_0(X239,X240),X239) = X239
    | ~ spl4_4141 ),
    inference(avatar_component_clause,[],[f45691])).

fof(f48753,plain,
    ( spl4_4258
    | ~ spl4_491
    | ~ spl4_4214 ),
    inference(avatar_split_clause,[],[f48303,f47828,f4499,f48750])).

fof(f4499,plain,
    ( spl4_491
  <=> ! [X13,X12,X14] : k2_xboole_0(k2_xboole_0(X13,X14),X12) = k2_xboole_0(X13,k2_xboole_0(X12,X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_491])])).

fof(f48303,plain,
    ( ! [X399,X398] : k2_xboole_0(X398,X399) = k2_xboole_0(X398,k2_xboole_0(X399,X398))
    | ~ spl4_491
    | ~ spl4_4214 ),
    inference(superposition,[],[f4500,f47829])).

fof(f4500,plain,
    ( ! [X14,X12,X13] : k2_xboole_0(k2_xboole_0(X13,X14),X12) = k2_xboole_0(X13,k2_xboole_0(X12,X14))
    | ~ spl4_491 ),
    inference(avatar_component_clause,[],[f4499])).

fof(f47837,plain,
    ( spl4_4214
    | ~ spl4_3887
    | ~ spl4_4135 ),
    inference(avatar_split_clause,[],[f47411,f45650,f44130,f47828])).

fof(f44130,plain,
    ( spl4_3887
  <=> ! [X27,X26] : k3_xboole_0(X26,k2_xboole_0(X26,X27)) = X26 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3887])])).

fof(f45650,plain,
    ( spl4_4135
  <=> ! [X5,X6] : k2_xboole_0(X5,k3_xboole_0(X5,X6)) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4135])])).

fof(f47411,plain,
    ( ! [X11] : k2_xboole_0(X11,X11) = X11
    | ~ spl4_3887
    | ~ spl4_4135 ),
    inference(superposition,[],[f45651,f44131])).

fof(f44131,plain,
    ( ! [X26,X27] : k3_xboole_0(X26,k2_xboole_0(X26,X27)) = X26
    | ~ spl4_3887 ),
    inference(avatar_component_clause,[],[f44130])).

fof(f45651,plain,
    ( ! [X6,X5] : k2_xboole_0(X5,k3_xboole_0(X5,X6)) = X5
    | ~ spl4_4135 ),
    inference(avatar_component_clause,[],[f45650])).

fof(f45693,plain,
    ( spl4_4141
    | ~ spl4_195
    | ~ spl4_3880
    | ~ spl4_3888 ),
    inference(avatar_split_clause,[],[f45689,f44134,f44102,f1678,f45691])).

fof(f44102,plain,
    ( spl4_3880
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3880])])).

fof(f44134,plain,
    ( spl4_3888
  <=> ! [X28] : k3_xboole_0(X28,X28) = X28 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3888])])).

fof(f45689,plain,
    ( ! [X239,X240] : k2_xboole_0(k3_xboole_0(X239,X240),X239) = X239
    | ~ spl4_195
    | ~ spl4_3880
    | ~ spl4_3888 ),
    inference(forward_demodulation,[],[f45202,f44103])).

fof(f44103,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0
    | ~ spl4_3880 ),
    inference(avatar_component_clause,[],[f44102])).

fof(f45202,plain,
    ( ! [X239,X240] : k2_xboole_0(k3_xboole_0(X239,X240),X239) = k3_xboole_0(X239,k2_xboole_0(X240,X239))
    | ~ spl4_195
    | ~ spl4_3888 ),
    inference(superposition,[],[f1679,f44135])).

fof(f44135,plain,
    ( ! [X28] : k3_xboole_0(X28,X28) = X28
    | ~ spl4_3888 ),
    inference(avatar_component_clause,[],[f44134])).

fof(f45682,plain,
    ( spl4_4135
    | ~ spl4_192
    | ~ spl4_3887
    | ~ spl4_3888 ),
    inference(avatar_split_clause,[],[f45681,f44134,f44130,f1661,f45650])).

fof(f1661,plain,
    ( spl4_192
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f45681,plain,
    ( ! [X235,X236] : k2_xboole_0(X235,k3_xboole_0(X235,X236)) = X235
    | ~ spl4_192
    | ~ spl4_3887
    | ~ spl4_3888 ),
    inference(forward_demodulation,[],[f45200,f44131])).

fof(f45200,plain,
    ( ! [X235,X236] : k3_xboole_0(X235,k2_xboole_0(X235,X236)) = k2_xboole_0(X235,k3_xboole_0(X235,X236))
    | ~ spl4_192
    | ~ spl4_3888 ),
    inference(superposition,[],[f1662,f44135])).

fof(f1662,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))
    | ~ spl4_192 ),
    inference(avatar_component_clause,[],[f1661])).

fof(f44408,plain,
    ( spl4_3956
    | ~ spl4_34
    | ~ spl4_3873 ),
    inference(avatar_split_clause,[],[f43928,f43786,f252,f44406])).

fof(f252,plain,
    ( spl4_34
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X2,X0),k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f43786,plain,
    ( spl4_3873
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | k3_xboole_0(X2,X3) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3873])])).

fof(f43928,plain,
    ( ! [X277,X275,X276] : k3_xboole_0(X275,X276) = k3_xboole_0(k3_xboole_0(X275,X276),k2_xboole_0(X277,X276))
    | ~ spl4_34
    | ~ spl4_3873 ),
    inference(resolution,[],[f43787,f253])).

fof(f253,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X2,X0),k2_xboole_0(X1,X0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f252])).

fof(f43787,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k3_xboole_0(X2,X3) = X2 )
    | ~ spl4_3873 ),
    inference(avatar_component_clause,[],[f43786])).

fof(f44136,plain,
    ( spl4_3888
    | ~ spl4_3861
    | ~ spl4_3873 ),
    inference(avatar_split_clause,[],[f43860,f43786,f43688,f44134])).

fof(f43688,plain,
    ( spl4_3861
  <=> ! [X2] : r1_tarski(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3861])])).

fof(f43860,plain,
    ( ! [X28] : k3_xboole_0(X28,X28) = X28
    | ~ spl4_3861
    | ~ spl4_3873 ),
    inference(resolution,[],[f43787,f43689])).

fof(f43689,plain,
    ( ! [X2] : r1_tarski(X2,X2)
    | ~ spl4_3861 ),
    inference(avatar_component_clause,[],[f43688])).

fof(f44132,plain,
    ( spl4_3887
    | ~ spl4_25
    | ~ spl4_3873 ),
    inference(avatar_split_clause,[],[f43859,f43786,f169,f44130])).

fof(f169,plain,
    ( spl4_25
  <=> ! [X1,X0] : r1_tarski(X1,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f43859,plain,
    ( ! [X26,X27] : k3_xboole_0(X26,k2_xboole_0(X26,X27)) = X26
    | ~ spl4_25
    | ~ spl4_3873 ),
    inference(resolution,[],[f43787,f170])).

fof(f170,plain,
    ( ! [X0,X1] : r1_tarski(X1,k2_xboole_0(X1,X0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f169])).

fof(f44128,plain,
    ( spl4_3886
    | ~ spl4_24
    | ~ spl4_3873 ),
    inference(avatar_split_clause,[],[f43858,f43786,f164,f44126])).

fof(f164,plain,
    ( spl4_24
  <=> ! [X3,X5,X4] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f43858,plain,
    ( ! [X24,X23,X25] : k3_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X23,X25))) = X23
    | ~ spl4_24
    | ~ spl4_3873 ),
    inference(resolution,[],[f43787,f165])).

fof(f165,plain,
    ( ! [X4,X5,X3] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f164])).

fof(f44104,plain,
    ( spl4_3880
    | ~ spl4_19
    | ~ spl4_3873 ),
    inference(avatar_split_clause,[],[f43852,f43786,f135,f44102])).

fof(f135,plain,
    ( spl4_19
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f43852,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0
    | ~ spl4_19
    | ~ spl4_3873 ),
    inference(resolution,[],[f43787,f136])).

fof(f136,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f135])).

fof(f43788,plain,
    ( spl4_3873
    | ~ spl4_2912
    | ~ spl4_3861 ),
    inference(avatar_split_clause,[],[f43764,f43688,f32865,f43786])).

fof(f32865,plain,
    ( spl4_2912
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2912])])).

fof(f43764,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k3_xboole_0(X2,X3) = X2 )
    | ~ spl4_2912
    | ~ spl4_3861 ),
    inference(resolution,[],[f43689,f32866])).

fof(f32866,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X0)
        | ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl4_2912 ),
    inference(avatar_component_clause,[],[f32865])).

fof(f43690,plain,
    ( spl4_3861
    | ~ spl4_10
    | ~ spl4_3852 ),
    inference(avatar_split_clause,[],[f43660,f43557,f73,f43688])).

fof(f73,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f43557,plain,
    ( spl4_3852
  <=> ! [X23,X24] : r1_tarski(k2_xboole_0(X23,k3_xboole_0(X24,X23)),X23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3852])])).

fof(f43660,plain,
    ( ! [X2] : r1_tarski(X2,X2)
    | ~ spl4_10
    | ~ spl4_3852 ),
    inference(resolution,[],[f43558,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f43558,plain,
    ( ! [X24,X23] : r1_tarski(k2_xboole_0(X23,k3_xboole_0(X24,X23)),X23)
    | ~ spl4_3852 ),
    inference(avatar_component_clause,[],[f43557])).

fof(f43559,plain,
    ( spl4_3852
    | ~ spl4_8
    | ~ spl4_3583 ),
    inference(avatar_split_clause,[],[f43498,f41905,f65,f43557])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f41905,plain,
    ( spl4_3583
  <=> ! [X153,X152] : r1_tarski(k3_xboole_0(X153,k2_xboole_0(X152,X152)),X152) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3583])])).

fof(f43498,plain,
    ( ! [X24,X23] : r1_tarski(k2_xboole_0(X23,k3_xboole_0(X24,X23)),X23)
    | ~ spl4_8
    | ~ spl4_3583 ),
    inference(superposition,[],[f41906,f66])).

fof(f66,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f41906,plain,
    ( ! [X152,X153] : r1_tarski(k3_xboole_0(X153,k2_xboole_0(X152,X152)),X152)
    | ~ spl4_3583 ),
    inference(avatar_component_clause,[],[f41905])).

fof(f43077,plain,
    ( spl4_3577
    | ~ spl4_3
    | ~ spl4_3467 ),
    inference(avatar_split_clause,[],[f41464,f40252,f45,f41837])).

fof(f40252,plain,
    ( spl4_3467
  <=> ! [X3,X2] : k3_xboole_0(X3,k2_xboole_0(X2,X2)) = k3_xboole_0(X2,k2_xboole_0(X3,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3467])])).

fof(f41464,plain,
    ( ! [X156,X157] : k3_xboole_0(X157,k2_xboole_0(X156,X156)) = k3_xboole_0(k2_xboole_0(X157,X157),X156)
    | ~ spl4_3
    | ~ spl4_3467 ),
    inference(superposition,[],[f46,f40253])).

fof(f40253,plain,
    ( ! [X2,X3] : k3_xboole_0(X3,k2_xboole_0(X2,X2)) = k3_xboole_0(X2,k2_xboole_0(X3,X3))
    | ~ spl4_3467 ),
    inference(avatar_component_clause,[],[f40252])).

fof(f43075,plain,
    ( spl4_3583
    | ~ spl4_2
    | ~ spl4_3467 ),
    inference(avatar_split_clause,[],[f41462,f40252,f41,f41905])).

fof(f41,plain,
    ( spl4_2
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f41462,plain,
    ( ! [X152,X153] : r1_tarski(k3_xboole_0(X153,k2_xboole_0(X152,X152)),X152)
    | ~ spl4_2
    | ~ spl4_3467 ),
    inference(superposition,[],[f42,f40253])).

fof(f42,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f40452,plain,
    ( spl4_3499
    | ~ spl4_116
    | ~ spl4_195 ),
    inference(avatar_split_clause,[],[f39957,f1678,f1059,f40450])).

fof(f1059,plain,
    ( spl4_116
  <=> ! [X3,X5,X4] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f39957,plain,
    ( ! [X668,X670,X667,X669] : k2_xboole_0(k3_xboole_0(X669,X667),k2_xboole_0(X670,k3_xboole_0(X667,X668))) = k2_xboole_0(X670,k3_xboole_0(X667,k2_xboole_0(X668,X669)))
    | ~ spl4_116
    | ~ spl4_195 ),
    inference(superposition,[],[f1060,f1679])).

fof(f1060,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f40260,plain,
    ( spl4_3467
    | ~ spl4_192
    | ~ spl4_195 ),
    inference(avatar_split_clause,[],[f39796,f1678,f1661,f40252])).

fof(f39796,plain,
    ( ! [X26,X27] : k3_xboole_0(X26,k2_xboole_0(X27,X27)) = k3_xboole_0(X27,k2_xboole_0(X26,X26))
    | ~ spl4_192
    | ~ spl4_195 ),
    inference(superposition,[],[f1662,f1679])).

fof(f32867,plain,
    ( spl4_2912
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f32863,f85,f77,f32865])).

fof(f77,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X1,X2) = X0
        | ~ r1_tarski(sK3(X0,X1,X2),X0)
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f85,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X1,X2) = X0
        | r1_tarski(sK3(X0,X1,X2),X1)
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f32863,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X0) )
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f32861])).

fof(f32861,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X0)
        | k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X0) )
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(resolution,[],[f86,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        | k3_xboole_0(X1,X2) = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(sK3(X0,X1,X2),X1)
        | k3_xboole_0(X1,X2) = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f10441,plain,
    ( spl4_935
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f10297,f65,f49,f10438])).

fof(f10297,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X5))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(superposition,[],[f66,f50])).

fof(f4643,plain,
    ( spl4_491
    | ~ spl4_4
    | ~ spl4_338 ),
    inference(avatar_split_clause,[],[f4418,f2692,f49,f4499])).

fof(f2692,plain,
    ( spl4_338
  <=> ! [X3,X5,X4] : k2_xboole_0(X4,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k2_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_338])])).

fof(f4418,plain,
    ( ! [X70,X72,X71] : k2_xboole_0(X71,k2_xboole_0(X70,X72)) = k2_xboole_0(k2_xboole_0(X71,X72),X70)
    | ~ spl4_4
    | ~ spl4_338 ),
    inference(superposition,[],[f50,f2693])).

fof(f2693,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X4,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k2_xboole_0(X4,X5))
    | ~ spl4_338 ),
    inference(avatar_component_clause,[],[f2692])).

fof(f2700,plain,
    ( spl4_338
    | ~ spl4_6
    | ~ spl4_115 ),
    inference(avatar_split_clause,[],[f2604,f1052,f57,f2692])).

fof(f1052,plain,
    ( spl4_115
  <=> ! [X1,X0,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f2604,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2))
    | ~ spl4_6
    | ~ spl4_115 ),
    inference(superposition,[],[f58,f1053])).

fof(f1053,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)
    | ~ spl4_115 ),
    inference(avatar_component_clause,[],[f1052])).

fof(f1713,plain,
    ( spl4_197
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f1618,f61,f49,f1692])).

fof(f1618,plain,
    ( ! [X28,X29,X27] : k3_xboole_0(X27,k2_xboole_0(X28,X29)) = k2_xboole_0(k3_xboole_0(X27,X29),k3_xboole_0(X27,X28))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f50,f62])).

fof(f1681,plain,
    ( spl4_195
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f1604,f61,f45,f1678])).

fof(f1604,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(X3,k2_xboole_0(X5,X4)) = k2_xboole_0(k3_xboole_0(X3,X5),k3_xboole_0(X4,X3))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f62,f46])).

fof(f1664,plain,
    ( spl4_192
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f1600,f61,f45,f1661])).

fof(f1600,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X5))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f62,f46])).

fof(f1064,plain,
    ( spl4_116
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1001,f57,f49,f1059])).

fof(f1001,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f50,f58])).

fof(f1055,plain,
    ( spl4_115
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f996,f57,f49,f1052])).

fof(f996,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k2_xboole_0(X4,X3),X5)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f58,f50])).

fof(f255,plain,
    ( spl4_34
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f245,f196,f49,f252])).

fof(f196,plain,
    ( spl4_28
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f245,plain,
    ( ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X5,X3),k2_xboole_0(X4,X3))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(superposition,[],[f197,f50])).

fof(f197,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X1,X0),k2_xboole_0(X0,X2))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f187,f139,f45,f196])).

fof(f139,plain,
    ( spl4_20
  <=> ! [X3,X2,X4] : r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X2,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f187,plain,
    ( ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X4,X3),k2_xboole_0(X3,X5))
    | ~ spl4_3
    | ~ spl4_20 ),
    inference(superposition,[],[f140,f46])).

fof(f140,plain,
    ( ! [X4,X2,X3] : r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X2,X4))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f172,plain,
    ( spl4_25
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f158,f135,f49,f169])).

fof(f158,plain,
    ( ! [X2,X3] : r1_tarski(X3,k2_xboole_0(X3,X2))
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(superposition,[],[f136,f50])).

fof(f166,plain,
    ( spl4_24
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f155,f135,f73,f164])).

fof(f155,plain,
    ( ! [X4,X5,X3] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(resolution,[],[f136,f74])).

fof(f141,plain,
    ( spl4_20
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f126,f118,f73,f139])).

fof(f118,plain,
    ( spl4_17
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f126,plain,
    ( ! [X4,X2,X3] : r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X2,X4))
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(resolution,[],[f119,f74])).

fof(f119,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f137,plain,
    ( spl4_19
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f125,f118,f109,f135])).

fof(f109,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k2_xboole_0(X1,X0),X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f125,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(resolution,[],[f119,f110])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X1,X0),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f120,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f115,f69,f41,f118])).

fof(f69,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f115,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f70,f42])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f112,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f107,f73,f49,f109])).

fof(f107,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k2_xboole_0(X4,X3),X5)
        | r1_tarski(X3,X5) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(superposition,[],[f74,f50])).

fof(f96,plain,
    ( ~ spl4_14
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f91,f57,f49,f45,f36,f93])).

fof(f36,plain,
    ( spl4_1
  <=> k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f91,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f90,f50])).

fof(f90,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK2)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f89,f46])).

fof(f89,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,sK0)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f88,f58])).

fof(f88,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2))
    | spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f38,f50])).

fof(f38,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f87,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK3(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f79,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK3(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f67,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f63,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f51,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))
   => k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:03:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (6317)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (6320)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (6319)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.44  % (6321)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (6313)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.44  % (6315)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.45  % (6318)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.45  % (6314)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.46  % (6323)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.47  % (6322)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.47  % (6316)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.49  % (6324)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 4.89/1.02  % (6314)Time limit reached!
% 4.89/1.02  % (6314)------------------------------
% 4.89/1.02  % (6314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.02  % (6314)Termination reason: Time limit
% 4.89/1.02  % (6314)Termination phase: Saturation
% 4.89/1.02  
% 4.89/1.02  % (6314)Memory used [KB]: 29807
% 4.89/1.02  % (6314)Time elapsed: 0.600 s
% 4.89/1.02  % (6314)------------------------------
% 4.89/1.02  % (6314)------------------------------
% 8.08/1.41  % (6313)Time limit reached!
% 8.08/1.41  % (6313)------------------------------
% 8.08/1.41  % (6313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.08/1.41  % (6313)Termination reason: Time limit
% 8.08/1.41  % (6313)Termination phase: Saturation
% 8.08/1.41  
% 8.08/1.41  % (6313)Memory used [KB]: 45415
% 8.08/1.41  % (6313)Time elapsed: 1.0000 s
% 8.08/1.41  % (6313)------------------------------
% 8.08/1.41  % (6313)------------------------------
% 22.31/3.16  % (6318)Refutation found. Thanks to Tanya!
% 22.31/3.16  % SZS status Theorem for theBenchmark
% 22.31/3.16  % SZS output start Proof for theBenchmark
% 22.31/3.17  fof(f108297,plain,(
% 22.31/3.17    $false),
% 22.31/3.17    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f59,f63,f67,f71,f75,f79,f87,f96,f112,f120,f137,f141,f166,f172,f199,f255,f1055,f1064,f1664,f1681,f1713,f2700,f4643,f10441,f32867,f40260,f40452,f43075,f43077,f43559,f43690,f43788,f44104,f44128,f44132,f44136,f44408,f45682,f45693,f47837,f48753,f50526,f57080,f78082,f80247,f84671,f87637,f89281,f97799,f107897])).
% 22.31/3.17  fof(f107897,plain,(
% 22.31/3.17    ~spl4_4 | spl4_14 | ~spl4_935 | ~spl4_3499 | ~spl4_5196 | ~spl4_5315 | ~spl4_5387 | ~spl4_5646),
% 22.31/3.17    inference(avatar_contradiction_clause,[],[f107896])).
% 22.31/3.17  fof(f107896,plain,(
% 22.31/3.17    $false | (~spl4_4 | spl4_14 | ~spl4_935 | ~spl4_3499 | ~spl4_5196 | ~spl4_5315 | ~spl4_5387 | ~spl4_5646)),
% 22.31/3.17    inference(subsumption_resolution,[],[f107895,f40451])).
% 22.31/3.17  fof(f40451,plain,(
% 22.31/3.17    ( ! [X668,X670,X667,X669] : (k2_xboole_0(k3_xboole_0(X669,X667),k2_xboole_0(X670,k3_xboole_0(X667,X668))) = k2_xboole_0(X670,k3_xboole_0(X667,k2_xboole_0(X668,X669)))) ) | ~spl4_3499),
% 22.31/3.17    inference(avatar_component_clause,[],[f40450])).
% 22.31/3.17  fof(f40450,plain,(
% 22.31/3.17    spl4_3499 <=> ! [X669,X667,X670,X668] : k2_xboole_0(k3_xboole_0(X669,X667),k2_xboole_0(X670,k3_xboole_0(X667,X668))) = k2_xboole_0(X670,k3_xboole_0(X667,k2_xboole_0(X668,X669)))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3499])])).
% 22.31/3.17  fof(f107895,plain,(
% 22.31/3.17    k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))) | (~spl4_4 | spl4_14 | ~spl4_935 | ~spl4_5196 | ~spl4_5315 | ~spl4_5387 | ~spl4_5646)),
% 22.31/3.17    inference(forward_demodulation,[],[f107894,f84046])).
% 22.31/3.17  fof(f84046,plain,(
% 22.31/3.17    ( ! [X26,X24,X25] : (k3_xboole_0(X24,k2_xboole_0(X26,X25)) = k3_xboole_0(k2_xboole_0(X25,X26),X24)) ) | ~spl4_5196),
% 22.31/3.17    inference(avatar_component_clause,[],[f84045])).
% 22.31/3.17  fof(f84045,plain,(
% 22.31/3.17    spl4_5196 <=> ! [X25,X24,X26] : k3_xboole_0(X24,k2_xboole_0(X26,X25)) = k3_xboole_0(k2_xboole_0(X25,X26),X24)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_5196])])).
% 22.31/3.17  fof(f107894,plain,(
% 22.31/3.17    k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) | (~spl4_4 | spl4_14 | ~spl4_935 | ~spl4_5315 | ~spl4_5387 | ~spl4_5646)),
% 22.31/3.17    inference(forward_demodulation,[],[f107893,f50])).
% 22.31/3.17  fof(f50,plain,(
% 22.31/3.17    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_4),
% 22.31/3.17    inference(avatar_component_clause,[],[f49])).
% 22.31/3.17  fof(f49,plain,(
% 22.31/3.17    spl4_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 22.31/3.17  fof(f107893,plain,(
% 22.31/3.17    k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK2)) | (spl4_14 | ~spl4_935 | ~spl4_5315 | ~spl4_5387 | ~spl4_5646)),
% 22.31/3.17    inference(forward_demodulation,[],[f107892,f97798])).
% 22.31/3.17  fof(f97798,plain,(
% 22.31/3.17    ( ! [X732,X730,X733,X731] : (k3_xboole_0(k2_xboole_0(X732,X731),k2_xboole_0(X733,k3_xboole_0(X730,X731))) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X732,X731),X733),k3_xboole_0(X730,X731))) ) | ~spl4_5646),
% 22.31/3.17    inference(avatar_component_clause,[],[f97797])).
% 22.31/3.17  fof(f97797,plain,(
% 22.31/3.17    spl4_5646 <=> ! [X731,X733,X730,X732] : k3_xboole_0(k2_xboole_0(X732,X731),k2_xboole_0(X733,k3_xboole_0(X730,X731))) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X732,X731),X733),k3_xboole_0(X730,X731))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_5646])])).
% 22.31/3.17  fof(f107892,plain,(
% 22.31/3.17    k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | (spl4_14 | ~spl4_935 | ~spl4_5315 | ~spl4_5387)),
% 22.31/3.17    inference(forward_demodulation,[],[f107891,f87010])).
% 22.31/3.17  fof(f87010,plain,(
% 22.31/3.17    ( ! [X45,X43,X44,X42] : (k3_xboole_0(k2_xboole_0(X42,X43),k2_xboole_0(X45,X44)) = k3_xboole_0(k2_xboole_0(X43,X42),k2_xboole_0(X44,X45))) ) | ~spl4_5315),
% 22.31/3.17    inference(avatar_component_clause,[],[f87009])).
% 22.31/3.17  fof(f87009,plain,(
% 22.31/3.17    spl4_5315 <=> ! [X42,X44,X43,X45] : k3_xboole_0(k2_xboole_0(X42,X43),k2_xboole_0(X45,X44)) = k3_xboole_0(k2_xboole_0(X43,X42),k2_xboole_0(X44,X45))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_5315])])).
% 22.31/3.17  fof(f107891,plain,(
% 22.31/3.17    k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1)) | (spl4_14 | ~spl4_935 | ~spl4_5387)),
% 22.31/3.17    inference(forward_demodulation,[],[f107275,f88913])).
% 22.31/3.17  fof(f88913,plain,(
% 22.31/3.17    ( ! [X78,X76,X77,X75] : (k3_xboole_0(k2_xboole_0(X76,X75),k2_xboole_0(X77,X78)) = k3_xboole_0(k2_xboole_0(X78,X77),k2_xboole_0(X75,X76))) ) | ~spl4_5387),
% 22.31/3.17    inference(avatar_component_clause,[],[f88912])).
% 22.31/3.17  fof(f88912,plain,(
% 22.31/3.17    spl4_5387 <=> ! [X75,X77,X76,X78] : k3_xboole_0(k2_xboole_0(X76,X75),k2_xboole_0(X77,X78)) = k3_xboole_0(k2_xboole_0(X78,X77),k2_xboole_0(X75,X76))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_5387])])).
% 22.31/3.17  fof(f107275,plain,(
% 22.31/3.17    k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2)) | (spl4_14 | ~spl4_935)),
% 22.31/3.17    inference(superposition,[],[f95,f10439])).
% 22.31/3.17  fof(f10439,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2))) ) | ~spl4_935),
% 22.31/3.17    inference(avatar_component_clause,[],[f10438])).
% 22.31/3.17  fof(f10438,plain,(
% 22.31/3.17    spl4_935 <=> ! [X1,X0,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_935])])).
% 22.31/3.17  fof(f95,plain,(
% 22.31/3.17    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) | spl4_14),
% 22.31/3.17    inference(avatar_component_clause,[],[f93])).
% 22.31/3.17  fof(f93,plain,(
% 22.31/3.17    spl4_14 <=> k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) = k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 22.31/3.17  fof(f97799,plain,(
% 22.31/3.17    spl4_5646 | ~spl4_195 | ~spl4_3956),
% 22.31/3.17    inference(avatar_split_clause,[],[f97513,f44406,f1678,f97797])).
% 22.31/3.17  fof(f1678,plain,(
% 22.31/3.17    spl4_195 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X1,X0))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_195])])).
% 22.31/3.17  fof(f44406,plain,(
% 22.31/3.17    spl4_3956 <=> ! [X276,X275,X277] : k3_xboole_0(X275,X276) = k3_xboole_0(k3_xboole_0(X275,X276),k2_xboole_0(X277,X276))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3956])])).
% 22.31/3.17  fof(f97513,plain,(
% 22.31/3.17    ( ! [X732,X730,X733,X731] : (k3_xboole_0(k2_xboole_0(X732,X731),k2_xboole_0(X733,k3_xboole_0(X730,X731))) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X732,X731),X733),k3_xboole_0(X730,X731))) ) | (~spl4_195 | ~spl4_3956)),
% 22.31/3.17    inference(superposition,[],[f1679,f44407])).
% 22.31/3.17  fof(f44407,plain,(
% 22.31/3.17    ( ! [X277,X275,X276] : (k3_xboole_0(X275,X276) = k3_xboole_0(k3_xboole_0(X275,X276),k2_xboole_0(X277,X276))) ) | ~spl4_3956),
% 22.31/3.17    inference(avatar_component_clause,[],[f44406])).
% 22.31/3.17  fof(f1679,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X1,X0))) ) | ~spl4_195),
% 22.31/3.17    inference(avatar_component_clause,[],[f1678])).
% 22.31/3.17  fof(f89281,plain,(
% 22.31/3.17    spl4_5387 | ~spl4_5143 | ~spl4_5196),
% 22.31/3.17    inference(avatar_split_clause,[],[f88704,f84045,f77901,f88912])).
% 22.31/3.17  fof(f77901,plain,(
% 22.31/3.17    spl4_5143 <=> ! [X9,X8,X10] : k3_xboole_0(X8,k2_xboole_0(X9,X10)) = k3_xboole_0(X8,k2_xboole_0(X10,X9))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_5143])])).
% 22.31/3.17  fof(f88704,plain,(
% 22.31/3.17    ( ! [X1942,X1940,X1943,X1941] : (k3_xboole_0(k2_xboole_0(X1942,X1943),k2_xboole_0(X1941,X1940)) = k3_xboole_0(k2_xboole_0(X1940,X1941),k2_xboole_0(X1943,X1942))) ) | (~spl4_5143 | ~spl4_5196)),
% 22.31/3.17    inference(superposition,[],[f77902,f84046])).
% 22.31/3.17  fof(f77902,plain,(
% 22.31/3.17    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k2_xboole_0(X9,X10)) = k3_xboole_0(X8,k2_xboole_0(X10,X9))) ) | ~spl4_5143),
% 22.31/3.17    inference(avatar_component_clause,[],[f77901])).
% 22.31/3.17  fof(f87637,plain,(
% 22.31/3.17    spl4_5315 | ~spl4_5143 | ~spl4_5190),
% 22.31/3.17    inference(avatar_split_clause,[],[f86807,f80191,f77901,f87009])).
% 22.31/3.17  fof(f80191,plain,(
% 22.31/3.17    spl4_5190 <=> ! [X7,X8,X6] : k3_xboole_0(k2_xboole_0(X6,X7),X8) = k3_xboole_0(k2_xboole_0(X7,X6),X8)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_5190])])).
% 22.31/3.17  fof(f86807,plain,(
% 22.31/3.17    ( ! [X1936,X1934,X1937,X1935] : (k3_xboole_0(k2_xboole_0(X1935,X1934),k2_xboole_0(X1936,X1937)) = k3_xboole_0(k2_xboole_0(X1934,X1935),k2_xboole_0(X1937,X1936))) ) | (~spl4_5143 | ~spl4_5190)),
% 22.31/3.17    inference(superposition,[],[f77902,f80192])).
% 22.31/3.17  fof(f80192,plain,(
% 22.31/3.17    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),X8) = k3_xboole_0(k2_xboole_0(X7,X6),X8)) ) | ~spl4_5190),
% 22.31/3.17    inference(avatar_component_clause,[],[f80191])).
% 22.31/3.17  fof(f84671,plain,(
% 22.31/3.17    spl4_5196 | ~spl4_3 | ~spl4_5143),
% 22.31/3.17    inference(avatar_split_clause,[],[f83617,f77901,f45,f84045])).
% 22.31/3.17  fof(f45,plain,(
% 22.31/3.17    spl4_3 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 22.31/3.17  fof(f83617,plain,(
% 22.31/3.17    ( ! [X263,X265,X264] : (k3_xboole_0(X263,k2_xboole_0(X265,X264)) = k3_xboole_0(k2_xboole_0(X264,X265),X263)) ) | (~spl4_3 | ~spl4_5143)),
% 22.31/3.17    inference(superposition,[],[f46,f77902])).
% 22.31/3.17  fof(f46,plain,(
% 22.31/3.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_3),
% 22.31/3.17    inference(avatar_component_clause,[],[f45])).
% 22.31/3.17  fof(f80247,plain,(
% 22.31/3.17    spl4_5190 | ~spl4_6 | ~spl4_3577 | ~spl4_4214 | ~spl4_4258 | ~spl4_4727),
% 22.31/3.17    inference(avatar_split_clause,[],[f80246,f57078,f48750,f47828,f41837,f57,f80191])).
% 22.31/3.17  fof(f57,plain,(
% 22.31/3.17    spl4_6 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 22.31/3.17  fof(f41837,plain,(
% 22.31/3.17    spl4_3577 <=> ! [X5,X4] : k3_xboole_0(k2_xboole_0(X5,X5),X4) = k3_xboole_0(X5,k2_xboole_0(X4,X4))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3577])])).
% 22.31/3.17  fof(f47828,plain,(
% 22.31/3.17    spl4_4214 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_4214])])).
% 22.31/3.17  fof(f48750,plain,(
% 22.31/3.17    spl4_4258 <=> ! [X348,X347] : k2_xboole_0(X347,X348) = k2_xboole_0(X347,k2_xboole_0(X348,X347))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_4258])])).
% 22.31/3.17  fof(f57078,plain,(
% 22.31/3.17    spl4_4727 <=> ! [X1510,X1508,X1509] : k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)) = k2_xboole_0(X1508,k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_4727])])).
% 22.31/3.17  fof(f80246,plain,(
% 22.31/3.17    ( ! [X47,X45,X46] : (k3_xboole_0(k2_xboole_0(X45,X46),X47) = k3_xboole_0(k2_xboole_0(X46,X45),X47)) ) | (~spl4_6 | ~spl4_3577 | ~spl4_4214 | ~spl4_4258 | ~spl4_4727)),
% 22.31/3.17    inference(forward_demodulation,[],[f80245,f47829])).
% 22.31/3.17  fof(f47829,plain,(
% 22.31/3.17    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl4_4214),
% 22.31/3.17    inference(avatar_component_clause,[],[f47828])).
% 22.31/3.17  fof(f80245,plain,(
% 22.31/3.17    ( ! [X47,X45,X46] : (k3_xboole_0(k2_xboole_0(X45,X46),k2_xboole_0(X47,X47)) = k3_xboole_0(k2_xboole_0(X46,X45),X47)) ) | (~spl4_6 | ~spl4_3577 | ~spl4_4258 | ~spl4_4727)),
% 22.31/3.17    inference(forward_demodulation,[],[f80244,f48751])).
% 22.31/3.17  fof(f48751,plain,(
% 22.31/3.17    ( ! [X347,X348] : (k2_xboole_0(X347,X348) = k2_xboole_0(X347,k2_xboole_0(X348,X347))) ) | ~spl4_4258),
% 22.31/3.17    inference(avatar_component_clause,[],[f48750])).
% 22.31/3.17  fof(f80244,plain,(
% 22.31/3.17    ( ! [X47,X45,X46] : (k3_xboole_0(k2_xboole_0(X45,X46),k2_xboole_0(X47,X47)) = k3_xboole_0(k2_xboole_0(X46,k2_xboole_0(X45,X46)),X47)) ) | (~spl4_6 | ~spl4_3577 | ~spl4_4727)),
% 22.31/3.17    inference(forward_demodulation,[],[f79147,f57079])).
% 22.31/3.17  fof(f57079,plain,(
% 22.31/3.17    ( ! [X1509,X1508,X1510] : (k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)) = k2_xboole_0(X1508,k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)))) ) | ~spl4_4727),
% 22.31/3.17    inference(avatar_component_clause,[],[f57078])).
% 22.31/3.17  fof(f79147,plain,(
% 22.31/3.17    ( ! [X47,X45,X46] : (k3_xboole_0(k2_xboole_0(X45,X46),k2_xboole_0(X47,X47)) = k3_xboole_0(k2_xboole_0(X45,k2_xboole_0(X46,k2_xboole_0(X45,X46))),X47)) ) | (~spl4_6 | ~spl4_3577)),
% 22.31/3.17    inference(superposition,[],[f41838,f58])).
% 22.31/3.17  fof(f58,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_6),
% 22.31/3.17    inference(avatar_component_clause,[],[f57])).
% 22.31/3.17  fof(f41838,plain,(
% 22.31/3.17    ( ! [X4,X5] : (k3_xboole_0(k2_xboole_0(X5,X5),X4) = k3_xboole_0(X5,k2_xboole_0(X4,X4))) ) | ~spl4_3577),
% 22.31/3.17    inference(avatar_component_clause,[],[f41837])).
% 22.31/3.17  fof(f78082,plain,(
% 22.31/3.17    spl4_5143 | ~spl4_7 | ~spl4_197),
% 22.31/3.17    inference(avatar_split_clause,[],[f77449,f1692,f61,f77901])).
% 22.31/3.17  fof(f61,plain,(
% 22.31/3.17    spl4_7 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 22.31/3.17  fof(f1692,plain,(
% 22.31/3.17    spl4_197 <=> ! [X3,X5,X4] : k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X3,X5),k3_xboole_0(X3,X4))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).
% 22.31/3.17  fof(f77449,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1))) ) | (~spl4_7 | ~spl4_197)),
% 22.31/3.17    inference(superposition,[],[f62,f1693])).
% 22.31/3.17  fof(f1693,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X3,X5),k3_xboole_0(X3,X4))) ) | ~spl4_197),
% 22.31/3.17    inference(avatar_component_clause,[],[f1692])).
% 22.31/3.17  fof(f62,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl4_7),
% 22.31/3.17    inference(avatar_component_clause,[],[f61])).
% 22.31/3.17  fof(f57080,plain,(
% 22.31/3.17    spl4_4727 | ~spl4_3886 | ~spl4_4319),
% 22.31/3.17    inference(avatar_split_clause,[],[f56752,f50523,f44126,f57078])).
% 22.31/3.17  fof(f44126,plain,(
% 22.31/3.17    spl4_3886 <=> ! [X25,X23,X24] : k3_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X23,X25))) = X23),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3886])])).
% 22.31/3.17  fof(f50523,plain,(
% 22.31/3.17    spl4_4319 <=> ! [X1,X2] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_4319])])).
% 22.31/3.17  fof(f56752,plain,(
% 22.31/3.17    ( ! [X1509,X1508,X1510] : (k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)) = k2_xboole_0(X1508,k2_xboole_0(X1509,k2_xboole_0(X1508,X1510)))) ) | (~spl4_3886 | ~spl4_4319)),
% 22.31/3.17    inference(superposition,[],[f50524,f44127])).
% 22.31/3.17  fof(f44127,plain,(
% 22.31/3.17    ( ! [X24,X23,X25] : (k3_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X23,X25))) = X23) ) | ~spl4_3886),
% 22.31/3.17    inference(avatar_component_clause,[],[f44126])).
% 22.31/3.17  fof(f50524,plain,(
% 22.31/3.17    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1) ) | ~spl4_4319),
% 22.31/3.17    inference(avatar_component_clause,[],[f50523])).
% 22.31/3.17  fof(f50526,plain,(
% 22.31/3.17    spl4_4319 | ~spl4_3 | ~spl4_4141),
% 22.31/3.17    inference(avatar_split_clause,[],[f49979,f45691,f45,f50523])).
% 22.31/3.17  fof(f45691,plain,(
% 22.31/3.17    spl4_4141 <=> ! [X240,X239] : k2_xboole_0(k3_xboole_0(X239,X240),X239) = X239),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_4141])])).
% 22.31/3.17  fof(f49979,plain,(
% 22.31/3.17    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X4,X3),X3) = X3) ) | (~spl4_3 | ~spl4_4141)),
% 22.31/3.17    inference(superposition,[],[f45692,f46])).
% 22.31/3.17  fof(f45692,plain,(
% 22.31/3.17    ( ! [X239,X240] : (k2_xboole_0(k3_xboole_0(X239,X240),X239) = X239) ) | ~spl4_4141),
% 22.31/3.17    inference(avatar_component_clause,[],[f45691])).
% 22.31/3.17  fof(f48753,plain,(
% 22.31/3.17    spl4_4258 | ~spl4_491 | ~spl4_4214),
% 22.31/3.17    inference(avatar_split_clause,[],[f48303,f47828,f4499,f48750])).
% 22.31/3.17  fof(f4499,plain,(
% 22.31/3.17    spl4_491 <=> ! [X13,X12,X14] : k2_xboole_0(k2_xboole_0(X13,X14),X12) = k2_xboole_0(X13,k2_xboole_0(X12,X14))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_491])])).
% 22.31/3.17  fof(f48303,plain,(
% 22.31/3.17    ( ! [X399,X398] : (k2_xboole_0(X398,X399) = k2_xboole_0(X398,k2_xboole_0(X399,X398))) ) | (~spl4_491 | ~spl4_4214)),
% 22.31/3.17    inference(superposition,[],[f4500,f47829])).
% 22.31/3.17  fof(f4500,plain,(
% 22.31/3.17    ( ! [X14,X12,X13] : (k2_xboole_0(k2_xboole_0(X13,X14),X12) = k2_xboole_0(X13,k2_xboole_0(X12,X14))) ) | ~spl4_491),
% 22.31/3.17    inference(avatar_component_clause,[],[f4499])).
% 22.31/3.17  fof(f47837,plain,(
% 22.31/3.17    spl4_4214 | ~spl4_3887 | ~spl4_4135),
% 22.31/3.17    inference(avatar_split_clause,[],[f47411,f45650,f44130,f47828])).
% 22.31/3.17  fof(f44130,plain,(
% 22.31/3.17    spl4_3887 <=> ! [X27,X26] : k3_xboole_0(X26,k2_xboole_0(X26,X27)) = X26),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3887])])).
% 22.31/3.17  fof(f45650,plain,(
% 22.31/3.17    spl4_4135 <=> ! [X5,X6] : k2_xboole_0(X5,k3_xboole_0(X5,X6)) = X5),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_4135])])).
% 22.31/3.17  fof(f47411,plain,(
% 22.31/3.17    ( ! [X11] : (k2_xboole_0(X11,X11) = X11) ) | (~spl4_3887 | ~spl4_4135)),
% 22.31/3.17    inference(superposition,[],[f45651,f44131])).
% 22.31/3.17  fof(f44131,plain,(
% 22.31/3.17    ( ! [X26,X27] : (k3_xboole_0(X26,k2_xboole_0(X26,X27)) = X26) ) | ~spl4_3887),
% 22.31/3.17    inference(avatar_component_clause,[],[f44130])).
% 22.31/3.17  fof(f45651,plain,(
% 22.31/3.17    ( ! [X6,X5] : (k2_xboole_0(X5,k3_xboole_0(X5,X6)) = X5) ) | ~spl4_4135),
% 22.31/3.17    inference(avatar_component_clause,[],[f45650])).
% 22.31/3.17  fof(f45693,plain,(
% 22.31/3.17    spl4_4141 | ~spl4_195 | ~spl4_3880 | ~spl4_3888),
% 22.31/3.17    inference(avatar_split_clause,[],[f45689,f44134,f44102,f1678,f45691])).
% 22.31/3.17  fof(f44102,plain,(
% 22.31/3.17    spl4_3880 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3880])])).
% 22.31/3.17  fof(f44134,plain,(
% 22.31/3.17    spl4_3888 <=> ! [X28] : k3_xboole_0(X28,X28) = X28),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3888])])).
% 22.31/3.17  fof(f45689,plain,(
% 22.31/3.17    ( ! [X239,X240] : (k2_xboole_0(k3_xboole_0(X239,X240),X239) = X239) ) | (~spl4_195 | ~spl4_3880 | ~spl4_3888)),
% 22.31/3.17    inference(forward_demodulation,[],[f45202,f44103])).
% 22.31/3.17  fof(f44103,plain,(
% 22.31/3.17    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) ) | ~spl4_3880),
% 22.31/3.17    inference(avatar_component_clause,[],[f44102])).
% 22.31/3.17  fof(f45202,plain,(
% 22.31/3.17    ( ! [X239,X240] : (k2_xboole_0(k3_xboole_0(X239,X240),X239) = k3_xboole_0(X239,k2_xboole_0(X240,X239))) ) | (~spl4_195 | ~spl4_3888)),
% 22.31/3.17    inference(superposition,[],[f1679,f44135])).
% 22.31/3.17  fof(f44135,plain,(
% 22.31/3.17    ( ! [X28] : (k3_xboole_0(X28,X28) = X28) ) | ~spl4_3888),
% 22.31/3.17    inference(avatar_component_clause,[],[f44134])).
% 22.31/3.17  fof(f45682,plain,(
% 22.31/3.17    spl4_4135 | ~spl4_192 | ~spl4_3887 | ~spl4_3888),
% 22.31/3.17    inference(avatar_split_clause,[],[f45681,f44134,f44130,f1661,f45650])).
% 22.31/3.17  fof(f1661,plain,(
% 22.31/3.17    spl4_192 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).
% 22.31/3.17  fof(f45681,plain,(
% 22.31/3.17    ( ! [X235,X236] : (k2_xboole_0(X235,k3_xboole_0(X235,X236)) = X235) ) | (~spl4_192 | ~spl4_3887 | ~spl4_3888)),
% 22.31/3.17    inference(forward_demodulation,[],[f45200,f44131])).
% 22.31/3.17  fof(f45200,plain,(
% 22.31/3.17    ( ! [X235,X236] : (k3_xboole_0(X235,k2_xboole_0(X235,X236)) = k2_xboole_0(X235,k3_xboole_0(X235,X236))) ) | (~spl4_192 | ~spl4_3888)),
% 22.31/3.17    inference(superposition,[],[f1662,f44135])).
% 22.31/3.17  fof(f1662,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) ) | ~spl4_192),
% 22.31/3.17    inference(avatar_component_clause,[],[f1661])).
% 22.31/3.17  fof(f44408,plain,(
% 22.31/3.17    spl4_3956 | ~spl4_34 | ~spl4_3873),
% 22.31/3.17    inference(avatar_split_clause,[],[f43928,f43786,f252,f44406])).
% 22.31/3.17  fof(f252,plain,(
% 22.31/3.17    spl4_34 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X2,X0),k2_xboole_0(X1,X0))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 22.31/3.17  fof(f43786,plain,(
% 22.31/3.17    spl4_3873 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | k3_xboole_0(X2,X3) = X2)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3873])])).
% 22.31/3.17  fof(f43928,plain,(
% 22.31/3.17    ( ! [X277,X275,X276] : (k3_xboole_0(X275,X276) = k3_xboole_0(k3_xboole_0(X275,X276),k2_xboole_0(X277,X276))) ) | (~spl4_34 | ~spl4_3873)),
% 22.31/3.17    inference(resolution,[],[f43787,f253])).
% 22.31/3.17  fof(f253,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X2,X0),k2_xboole_0(X1,X0))) ) | ~spl4_34),
% 22.31/3.17    inference(avatar_component_clause,[],[f252])).
% 22.31/3.17  fof(f43787,plain,(
% 22.31/3.17    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k3_xboole_0(X2,X3) = X2) ) | ~spl4_3873),
% 22.31/3.17    inference(avatar_component_clause,[],[f43786])).
% 22.31/3.17  fof(f44136,plain,(
% 22.31/3.17    spl4_3888 | ~spl4_3861 | ~spl4_3873),
% 22.31/3.17    inference(avatar_split_clause,[],[f43860,f43786,f43688,f44134])).
% 22.31/3.17  fof(f43688,plain,(
% 22.31/3.17    spl4_3861 <=> ! [X2] : r1_tarski(X2,X2)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3861])])).
% 22.31/3.17  fof(f43860,plain,(
% 22.31/3.17    ( ! [X28] : (k3_xboole_0(X28,X28) = X28) ) | (~spl4_3861 | ~spl4_3873)),
% 22.31/3.17    inference(resolution,[],[f43787,f43689])).
% 22.31/3.17  fof(f43689,plain,(
% 22.31/3.17    ( ! [X2] : (r1_tarski(X2,X2)) ) | ~spl4_3861),
% 22.31/3.17    inference(avatar_component_clause,[],[f43688])).
% 22.31/3.17  fof(f44132,plain,(
% 22.31/3.17    spl4_3887 | ~spl4_25 | ~spl4_3873),
% 22.31/3.17    inference(avatar_split_clause,[],[f43859,f43786,f169,f44130])).
% 22.31/3.17  fof(f169,plain,(
% 22.31/3.17    spl4_25 <=> ! [X1,X0] : r1_tarski(X1,k2_xboole_0(X1,X0))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 22.31/3.17  fof(f43859,plain,(
% 22.31/3.17    ( ! [X26,X27] : (k3_xboole_0(X26,k2_xboole_0(X26,X27)) = X26) ) | (~spl4_25 | ~spl4_3873)),
% 22.31/3.17    inference(resolution,[],[f43787,f170])).
% 22.31/3.17  fof(f170,plain,(
% 22.31/3.17    ( ! [X0,X1] : (r1_tarski(X1,k2_xboole_0(X1,X0))) ) | ~spl4_25),
% 22.31/3.17    inference(avatar_component_clause,[],[f169])).
% 22.31/3.17  fof(f44128,plain,(
% 22.31/3.17    spl4_3886 | ~spl4_24 | ~spl4_3873),
% 22.31/3.17    inference(avatar_split_clause,[],[f43858,f43786,f164,f44126])).
% 22.31/3.17  fof(f164,plain,(
% 22.31/3.17    spl4_24 <=> ! [X3,X5,X4] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 22.31/3.17  fof(f43858,plain,(
% 22.31/3.17    ( ! [X24,X23,X25] : (k3_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X23,X25))) = X23) ) | (~spl4_24 | ~spl4_3873)),
% 22.31/3.17    inference(resolution,[],[f43787,f165])).
% 22.31/3.17  fof(f165,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))) ) | ~spl4_24),
% 22.31/3.17    inference(avatar_component_clause,[],[f164])).
% 22.31/3.17  fof(f44104,plain,(
% 22.31/3.17    spl4_3880 | ~spl4_19 | ~spl4_3873),
% 22.31/3.17    inference(avatar_split_clause,[],[f43852,f43786,f135,f44102])).
% 22.31/3.17  fof(f135,plain,(
% 22.31/3.17    spl4_19 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 22.31/3.17  fof(f43852,plain,(
% 22.31/3.17    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) ) | (~spl4_19 | ~spl4_3873)),
% 22.31/3.17    inference(resolution,[],[f43787,f136])).
% 22.31/3.17  fof(f136,plain,(
% 22.31/3.17    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | ~spl4_19),
% 22.31/3.17    inference(avatar_component_clause,[],[f135])).
% 22.31/3.17  fof(f43788,plain,(
% 22.31/3.17    spl4_3873 | ~spl4_2912 | ~spl4_3861),
% 22.31/3.17    inference(avatar_split_clause,[],[f43764,f43688,f32865,f43786])).
% 22.31/3.17  fof(f32865,plain,(
% 22.31/3.17    spl4_2912 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_2912])])).
% 22.31/3.17  fof(f43764,plain,(
% 22.31/3.17    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k3_xboole_0(X2,X3) = X2) ) | (~spl4_2912 | ~spl4_3861)),
% 22.31/3.17    inference(resolution,[],[f43689,f32866])).
% 22.31/3.17  fof(f32866,plain,(
% 22.31/3.17    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl4_2912),
% 22.31/3.17    inference(avatar_component_clause,[],[f32865])).
% 22.31/3.17  fof(f43690,plain,(
% 22.31/3.17    spl4_3861 | ~spl4_10 | ~spl4_3852),
% 22.31/3.17    inference(avatar_split_clause,[],[f43660,f43557,f73,f43688])).
% 22.31/3.17  fof(f73,plain,(
% 22.31/3.17    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 22.31/3.17  fof(f43557,plain,(
% 22.31/3.17    spl4_3852 <=> ! [X23,X24] : r1_tarski(k2_xboole_0(X23,k3_xboole_0(X24,X23)),X23)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3852])])).
% 22.31/3.17  fof(f43660,plain,(
% 22.31/3.17    ( ! [X2] : (r1_tarski(X2,X2)) ) | (~spl4_10 | ~spl4_3852)),
% 22.31/3.17    inference(resolution,[],[f43558,f74])).
% 22.31/3.17  fof(f74,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl4_10),
% 22.31/3.17    inference(avatar_component_clause,[],[f73])).
% 22.31/3.17  fof(f43558,plain,(
% 22.31/3.17    ( ! [X24,X23] : (r1_tarski(k2_xboole_0(X23,k3_xboole_0(X24,X23)),X23)) ) | ~spl4_3852),
% 22.31/3.17    inference(avatar_component_clause,[],[f43557])).
% 22.31/3.17  fof(f43559,plain,(
% 22.31/3.17    spl4_3852 | ~spl4_8 | ~spl4_3583),
% 22.31/3.17    inference(avatar_split_clause,[],[f43498,f41905,f65,f43557])).
% 22.31/3.17  fof(f65,plain,(
% 22.31/3.17    spl4_8 <=> ! [X1,X0,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 22.31/3.17  fof(f41905,plain,(
% 22.31/3.17    spl4_3583 <=> ! [X153,X152] : r1_tarski(k3_xboole_0(X153,k2_xboole_0(X152,X152)),X152)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3583])])).
% 22.31/3.17  fof(f43498,plain,(
% 22.31/3.17    ( ! [X24,X23] : (r1_tarski(k2_xboole_0(X23,k3_xboole_0(X24,X23)),X23)) ) | (~spl4_8 | ~spl4_3583)),
% 22.31/3.17    inference(superposition,[],[f41906,f66])).
% 22.31/3.17  fof(f66,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ) | ~spl4_8),
% 22.31/3.17    inference(avatar_component_clause,[],[f65])).
% 22.31/3.17  fof(f41906,plain,(
% 22.31/3.17    ( ! [X152,X153] : (r1_tarski(k3_xboole_0(X153,k2_xboole_0(X152,X152)),X152)) ) | ~spl4_3583),
% 22.31/3.17    inference(avatar_component_clause,[],[f41905])).
% 22.31/3.17  fof(f43077,plain,(
% 22.31/3.17    spl4_3577 | ~spl4_3 | ~spl4_3467),
% 22.31/3.17    inference(avatar_split_clause,[],[f41464,f40252,f45,f41837])).
% 22.31/3.17  fof(f40252,plain,(
% 22.31/3.17    spl4_3467 <=> ! [X3,X2] : k3_xboole_0(X3,k2_xboole_0(X2,X2)) = k3_xboole_0(X2,k2_xboole_0(X3,X3))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_3467])])).
% 22.31/3.17  fof(f41464,plain,(
% 22.31/3.17    ( ! [X156,X157] : (k3_xboole_0(X157,k2_xboole_0(X156,X156)) = k3_xboole_0(k2_xboole_0(X157,X157),X156)) ) | (~spl4_3 | ~spl4_3467)),
% 22.31/3.17    inference(superposition,[],[f46,f40253])).
% 22.31/3.17  fof(f40253,plain,(
% 22.31/3.17    ( ! [X2,X3] : (k3_xboole_0(X3,k2_xboole_0(X2,X2)) = k3_xboole_0(X2,k2_xboole_0(X3,X3))) ) | ~spl4_3467),
% 22.31/3.17    inference(avatar_component_clause,[],[f40252])).
% 22.31/3.17  fof(f43075,plain,(
% 22.31/3.17    spl4_3583 | ~spl4_2 | ~spl4_3467),
% 22.31/3.17    inference(avatar_split_clause,[],[f41462,f40252,f41,f41905])).
% 22.31/3.17  fof(f41,plain,(
% 22.31/3.17    spl4_2 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 22.31/3.17  fof(f41462,plain,(
% 22.31/3.17    ( ! [X152,X153] : (r1_tarski(k3_xboole_0(X153,k2_xboole_0(X152,X152)),X152)) ) | (~spl4_2 | ~spl4_3467)),
% 22.31/3.17    inference(superposition,[],[f42,f40253])).
% 22.31/3.17  fof(f42,plain,(
% 22.31/3.17    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl4_2),
% 22.31/3.17    inference(avatar_component_clause,[],[f41])).
% 22.31/3.17  fof(f40452,plain,(
% 22.31/3.17    spl4_3499 | ~spl4_116 | ~spl4_195),
% 22.31/3.17    inference(avatar_split_clause,[],[f39957,f1678,f1059,f40450])).
% 22.31/3.17  fof(f1059,plain,(
% 22.31/3.17    spl4_116 <=> ! [X3,X5,X4] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).
% 22.31/3.17  fof(f39957,plain,(
% 22.31/3.17    ( ! [X668,X670,X667,X669] : (k2_xboole_0(k3_xboole_0(X669,X667),k2_xboole_0(X670,k3_xboole_0(X667,X668))) = k2_xboole_0(X670,k3_xboole_0(X667,k2_xboole_0(X668,X669)))) ) | (~spl4_116 | ~spl4_195)),
% 22.31/3.17    inference(superposition,[],[f1060,f1679])).
% 22.31/3.17  fof(f1060,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) ) | ~spl4_116),
% 22.31/3.17    inference(avatar_component_clause,[],[f1059])).
% 22.31/3.17  fof(f40260,plain,(
% 22.31/3.17    spl4_3467 | ~spl4_192 | ~spl4_195),
% 22.31/3.17    inference(avatar_split_clause,[],[f39796,f1678,f1661,f40252])).
% 22.31/3.17  fof(f39796,plain,(
% 22.31/3.17    ( ! [X26,X27] : (k3_xboole_0(X26,k2_xboole_0(X27,X27)) = k3_xboole_0(X27,k2_xboole_0(X26,X26))) ) | (~spl4_192 | ~spl4_195)),
% 22.31/3.17    inference(superposition,[],[f1662,f1679])).
% 22.31/3.17  fof(f32867,plain,(
% 22.31/3.17    spl4_2912 | ~spl4_11 | ~spl4_13),
% 22.31/3.17    inference(avatar_split_clause,[],[f32863,f85,f77,f32865])).
% 22.31/3.17  fof(f77,plain,(
% 22.31/3.17    spl4_11 <=> ! [X1,X0,X2] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK3(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 22.31/3.17  fof(f85,plain,(
% 22.31/3.17    spl4_13 <=> ! [X1,X0,X2] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK3(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 22.31/3.17  fof(f32863,plain,(
% 22.31/3.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) ) | (~spl4_11 | ~spl4_13)),
% 22.31/3.17    inference(duplicate_literal_removal,[],[f32861])).
% 22.31/3.17  fof(f32861,plain,(
% 22.31/3.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) ) | (~spl4_11 | ~spl4_13)),
% 22.31/3.17    inference(resolution,[],[f86,f78])).
% 22.31/3.17  fof(f78,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl4_11),
% 22.31/3.17    inference(avatar_component_clause,[],[f77])).
% 22.31/3.17  fof(f86,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X1) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl4_13),
% 22.31/3.17    inference(avatar_component_clause,[],[f85])).
% 22.31/3.17  fof(f10441,plain,(
% 22.31/3.17    spl4_935 | ~spl4_4 | ~spl4_8),
% 22.31/3.17    inference(avatar_split_clause,[],[f10297,f65,f49,f10438])).
% 22.31/3.17  fof(f10297,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X5))) ) | (~spl4_4 | ~spl4_8)),
% 22.31/3.17    inference(superposition,[],[f66,f50])).
% 22.31/3.17  fof(f4643,plain,(
% 22.31/3.17    spl4_491 | ~spl4_4 | ~spl4_338),
% 22.31/3.17    inference(avatar_split_clause,[],[f4418,f2692,f49,f4499])).
% 22.31/3.17  fof(f2692,plain,(
% 22.31/3.17    spl4_338 <=> ! [X3,X5,X4] : k2_xboole_0(X4,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k2_xboole_0(X4,X5))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_338])])).
% 22.31/3.17  fof(f4418,plain,(
% 22.31/3.17    ( ! [X70,X72,X71] : (k2_xboole_0(X71,k2_xboole_0(X70,X72)) = k2_xboole_0(k2_xboole_0(X71,X72),X70)) ) | (~spl4_4 | ~spl4_338)),
% 22.31/3.17    inference(superposition,[],[f50,f2693])).
% 22.31/3.17  fof(f2693,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k2_xboole_0(X4,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k2_xboole_0(X4,X5))) ) | ~spl4_338),
% 22.31/3.17    inference(avatar_component_clause,[],[f2692])).
% 22.31/3.17  fof(f2700,plain,(
% 22.31/3.17    spl4_338 | ~spl4_6 | ~spl4_115),
% 22.31/3.17    inference(avatar_split_clause,[],[f2604,f1052,f57,f2692])).
% 22.31/3.17  fof(f1052,plain,(
% 22.31/3.17    spl4_115 <=> ! [X1,X0,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).
% 22.31/3.17  fof(f2604,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2))) ) | (~spl4_6 | ~spl4_115)),
% 22.31/3.17    inference(superposition,[],[f58,f1053])).
% 22.31/3.17  fof(f1053,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) ) | ~spl4_115),
% 22.31/3.17    inference(avatar_component_clause,[],[f1052])).
% 22.31/3.17  fof(f1713,plain,(
% 22.31/3.17    spl4_197 | ~spl4_4 | ~spl4_7),
% 22.31/3.17    inference(avatar_split_clause,[],[f1618,f61,f49,f1692])).
% 22.31/3.17  fof(f1618,plain,(
% 22.31/3.17    ( ! [X28,X29,X27] : (k3_xboole_0(X27,k2_xboole_0(X28,X29)) = k2_xboole_0(k3_xboole_0(X27,X29),k3_xboole_0(X27,X28))) ) | (~spl4_4 | ~spl4_7)),
% 22.31/3.17    inference(superposition,[],[f50,f62])).
% 22.31/3.17  fof(f1681,plain,(
% 22.31/3.17    spl4_195 | ~spl4_3 | ~spl4_7),
% 22.31/3.17    inference(avatar_split_clause,[],[f1604,f61,f45,f1678])).
% 22.31/3.17  fof(f1604,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k2_xboole_0(X5,X4)) = k2_xboole_0(k3_xboole_0(X3,X5),k3_xboole_0(X4,X3))) ) | (~spl4_3 | ~spl4_7)),
% 22.31/3.17    inference(superposition,[],[f62,f46])).
% 22.31/3.17  fof(f1664,plain,(
% 22.31/3.17    spl4_192 | ~spl4_3 | ~spl4_7),
% 22.31/3.17    inference(avatar_split_clause,[],[f1600,f61,f45,f1661])).
% 22.31/3.17  fof(f1600,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X5))) ) | (~spl4_3 | ~spl4_7)),
% 22.31/3.17    inference(superposition,[],[f62,f46])).
% 22.31/3.17  fof(f1064,plain,(
% 22.31/3.17    spl4_116 | ~spl4_4 | ~spl4_6),
% 22.31/3.17    inference(avatar_split_clause,[],[f1001,f57,f49,f1059])).
% 22.31/3.17  fof(f1001,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) ) | (~spl4_4 | ~spl4_6)),
% 22.31/3.17    inference(superposition,[],[f50,f58])).
% 22.31/3.17  fof(f1055,plain,(
% 22.31/3.17    spl4_115 | ~spl4_4 | ~spl4_6),
% 22.31/3.17    inference(avatar_split_clause,[],[f996,f57,f49,f1052])).
% 22.31/3.17  fof(f996,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k2_xboole_0(X4,X3),X5)) ) | (~spl4_4 | ~spl4_6)),
% 22.31/3.17    inference(superposition,[],[f58,f50])).
% 22.31/3.17  fof(f255,plain,(
% 22.31/3.17    spl4_34 | ~spl4_4 | ~spl4_28),
% 22.31/3.17    inference(avatar_split_clause,[],[f245,f196,f49,f252])).
% 22.31/3.17  fof(f196,plain,(
% 22.31/3.17    spl4_28 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X1,X0),k2_xboole_0(X0,X2))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 22.31/3.17  fof(f245,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X5,X3),k2_xboole_0(X4,X3))) ) | (~spl4_4 | ~spl4_28)),
% 22.31/3.17    inference(superposition,[],[f197,f50])).
% 22.31/3.17  fof(f197,plain,(
% 22.31/3.17    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),k2_xboole_0(X0,X2))) ) | ~spl4_28),
% 22.31/3.17    inference(avatar_component_clause,[],[f196])).
% 22.31/3.17  fof(f199,plain,(
% 22.31/3.17    spl4_28 | ~spl4_3 | ~spl4_20),
% 22.31/3.17    inference(avatar_split_clause,[],[f187,f139,f45,f196])).
% 22.31/3.17  fof(f139,plain,(
% 22.31/3.17    spl4_20 <=> ! [X3,X2,X4] : r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X2,X4))),
% 22.31/3.17    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 22.31/3.17  fof(f187,plain,(
% 22.31/3.17    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X4,X3),k2_xboole_0(X3,X5))) ) | (~spl4_3 | ~spl4_20)),
% 22.31/3.17    inference(superposition,[],[f140,f46])).
% 22.31/3.17  fof(f140,plain,(
% 22.31/3.17    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X2,X4))) ) | ~spl4_20),
% 22.31/3.17    inference(avatar_component_clause,[],[f139])).
% 22.31/3.17  fof(f172,plain,(
% 22.31/3.17    spl4_25 | ~spl4_4 | ~spl4_19),
% 22.31/3.17    inference(avatar_split_clause,[],[f158,f135,f49,f169])).
% 22.31/3.17  fof(f158,plain,(
% 22.31/3.17    ( ! [X2,X3] : (r1_tarski(X3,k2_xboole_0(X3,X2))) ) | (~spl4_4 | ~spl4_19)),
% 22.31/3.17    inference(superposition,[],[f136,f50])).
% 22.31/3.17  fof(f166,plain,(
% 22.31/3.17    spl4_24 | ~spl4_10 | ~spl4_19),
% 22.31/3.17    inference(avatar_split_clause,[],[f155,f135,f73,f164])).
% 22.31/3.18  fof(f155,plain,(
% 22.31/3.18    ( ! [X4,X5,X3] : (r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))) ) | (~spl4_10 | ~spl4_19)),
% 22.31/3.18    inference(resolution,[],[f136,f74])).
% 22.31/3.18  fof(f141,plain,(
% 22.31/3.18    spl4_20 | ~spl4_10 | ~spl4_17),
% 22.31/3.18    inference(avatar_split_clause,[],[f126,f118,f73,f139])).
% 22.31/3.18  fof(f118,plain,(
% 22.31/3.18    spl4_17 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2))),
% 22.31/3.18    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 22.31/3.18  fof(f126,plain,(
% 22.31/3.18    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X2,X4))) ) | (~spl4_10 | ~spl4_17)),
% 22.31/3.18    inference(resolution,[],[f119,f74])).
% 22.31/3.18  fof(f119,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2))) ) | ~spl4_17),
% 22.31/3.18    inference(avatar_component_clause,[],[f118])).
% 22.31/3.18  fof(f137,plain,(
% 22.31/3.18    spl4_19 | ~spl4_16 | ~spl4_17),
% 22.31/3.18    inference(avatar_split_clause,[],[f125,f118,f109,f135])).
% 22.31/3.18  fof(f109,plain,(
% 22.31/3.18    spl4_16 <=> ! [X1,X0,X2] : (~r1_tarski(k2_xboole_0(X1,X0),X2) | r1_tarski(X0,X2))),
% 22.31/3.18    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 22.31/3.18  fof(f125,plain,(
% 22.31/3.18    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | (~spl4_16 | ~spl4_17)),
% 22.31/3.18    inference(resolution,[],[f119,f110])).
% 22.31/3.18  fof(f110,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X1,X0),X2) | r1_tarski(X0,X2)) ) | ~spl4_16),
% 22.31/3.18    inference(avatar_component_clause,[],[f109])).
% 22.31/3.18  fof(f120,plain,(
% 22.31/3.18    spl4_17 | ~spl4_2 | ~spl4_9),
% 22.31/3.18    inference(avatar_split_clause,[],[f115,f69,f41,f118])).
% 22.31/3.18  fof(f69,plain,(
% 22.31/3.18    spl4_9 <=> ! [X1,X0,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 22.31/3.18    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 22.31/3.18  fof(f115,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2))) ) | (~spl4_2 | ~spl4_9)),
% 22.31/3.18    inference(resolution,[],[f70,f42])).
% 22.31/3.18  fof(f70,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) ) | ~spl4_9),
% 22.31/3.18    inference(avatar_component_clause,[],[f69])).
% 22.31/3.18  fof(f112,plain,(
% 22.31/3.18    spl4_16 | ~spl4_4 | ~spl4_10),
% 22.31/3.18    inference(avatar_split_clause,[],[f107,f73,f49,f109])).
% 22.31/3.18  fof(f107,plain,(
% 22.31/3.18    ( ! [X4,X5,X3] : (~r1_tarski(k2_xboole_0(X4,X3),X5) | r1_tarski(X3,X5)) ) | (~spl4_4 | ~spl4_10)),
% 22.31/3.18    inference(superposition,[],[f74,f50])).
% 22.31/3.18  fof(f96,plain,(
% 22.31/3.18    ~spl4_14 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_6),
% 22.31/3.18    inference(avatar_split_clause,[],[f91,f57,f49,f45,f36,f93])).
% 22.31/3.18  fof(f36,plain,(
% 22.31/3.18    spl4_1 <=> k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 22.31/3.18    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 22.31/3.18  fof(f91,plain,(
% 22.31/3.18    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_6)),
% 22.31/3.18    inference(forward_demodulation,[],[f90,f50])).
% 22.31/3.18  fof(f90,plain,(
% 22.31/3.18    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK2))) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_6)),
% 22.31/3.18    inference(forward_demodulation,[],[f89,f46])).
% 22.31/3.18  fof(f89,plain,(
% 22.31/3.18    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,sK0))) | (spl4_1 | ~spl4_4 | ~spl4_6)),
% 22.31/3.18    inference(forward_demodulation,[],[f88,f58])).
% 22.31/3.18  fof(f88,plain,(
% 22.31/3.18    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) | (spl4_1 | ~spl4_4)),
% 22.31/3.18    inference(forward_demodulation,[],[f38,f50])).
% 22.31/3.18  fof(f38,plain,(
% 22.31/3.18    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) | spl4_1),
% 22.31/3.18    inference(avatar_component_clause,[],[f36])).
% 22.31/3.18  fof(f87,plain,(
% 22.31/3.18    spl4_13),
% 22.31/3.18    inference(avatar_split_clause,[],[f32,f85])).
% 22.31/3.18  fof(f32,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK3(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 22.31/3.18    inference(cnf_transformation,[],[f21])).
% 22.31/3.18  fof(f21,plain,(
% 22.31/3.18    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 22.31/3.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f20])).
% 22.31/3.18  fof(f20,plain,(
% 22.31/3.18    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)))),
% 22.31/3.18    introduced(choice_axiom,[])).
% 22.31/3.18  fof(f17,plain,(
% 22.31/3.18    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 22.31/3.18    inference(flattening,[],[f16])).
% 22.31/3.18  fof(f16,plain,(
% 22.31/3.18    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 22.31/3.18    inference(ennf_transformation,[],[f6])).
% 22.31/3.18  fof(f6,axiom,(
% 22.31/3.18    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 22.31/3.18  fof(f79,plain,(
% 22.31/3.18    spl4_11),
% 22.31/3.18    inference(avatar_split_clause,[],[f34,f77])).
% 22.31/3.18  fof(f34,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK3(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 22.31/3.18    inference(cnf_transformation,[],[f21])).
% 22.31/3.18  fof(f75,plain,(
% 22.31/3.18    spl4_10),
% 22.31/3.18    inference(avatar_split_clause,[],[f31,f73])).
% 22.31/3.18  fof(f31,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 22.31/3.18    inference(cnf_transformation,[],[f15])).
% 22.31/3.18  fof(f15,plain,(
% 22.31/3.18    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 22.31/3.18    inference(ennf_transformation,[],[f3])).
% 22.31/3.18  fof(f3,axiom,(
% 22.31/3.18    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 22.31/3.18  fof(f71,plain,(
% 22.31/3.18    spl4_9),
% 22.31/3.18    inference(avatar_split_clause,[],[f30,f69])).
% 22.31/3.18  fof(f30,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 22.31/3.18    inference(cnf_transformation,[],[f14])).
% 22.31/3.18  fof(f14,plain,(
% 22.31/3.18    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 22.31/3.18    inference(ennf_transformation,[],[f10])).
% 22.31/3.18  fof(f10,axiom,(
% 22.31/3.18    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 22.31/3.18  fof(f67,plain,(
% 22.31/3.18    spl4_8),
% 22.31/3.18    inference(avatar_split_clause,[],[f29,f65])).
% 22.31/3.18  fof(f29,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 22.31/3.18    inference(cnf_transformation,[],[f8])).
% 22.31/3.18  fof(f8,axiom,(
% 22.31/3.18    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 22.31/3.18  fof(f63,plain,(
% 22.31/3.18    spl4_7),
% 22.31/3.18    inference(avatar_split_clause,[],[f28,f61])).
% 22.31/3.18  fof(f28,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 22.31/3.18    inference(cnf_transformation,[],[f7])).
% 22.31/3.18  fof(f7,axiom,(
% 22.31/3.18    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 22.31/3.18  fof(f59,plain,(
% 22.31/3.18    spl4_6),
% 22.31/3.18    inference(avatar_split_clause,[],[f27,f57])).
% 22.31/3.18  fof(f27,plain,(
% 22.31/3.18    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 22.31/3.18    inference(cnf_transformation,[],[f9])).
% 22.31/3.18  fof(f9,axiom,(
% 22.31/3.18    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 22.31/3.18  fof(f51,plain,(
% 22.31/3.18    spl4_4),
% 22.31/3.18    inference(avatar_split_clause,[],[f25,f49])).
% 22.31/3.18  fof(f25,plain,(
% 22.31/3.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 22.31/3.18    inference(cnf_transformation,[],[f1])).
% 22.31/3.18  fof(f1,axiom,(
% 22.31/3.18    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 22.31/3.18  fof(f47,plain,(
% 22.31/3.18    spl4_3),
% 22.31/3.18    inference(avatar_split_clause,[],[f24,f45])).
% 22.31/3.18  fof(f24,plain,(
% 22.31/3.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 22.31/3.18    inference(cnf_transformation,[],[f2])).
% 22.31/3.18  fof(f2,axiom,(
% 22.31/3.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 22.31/3.18  fof(f43,plain,(
% 22.31/3.18    spl4_2),
% 22.31/3.18    inference(avatar_split_clause,[],[f23,f41])).
% 22.31/3.18  fof(f23,plain,(
% 22.31/3.18    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 22.31/3.18    inference(cnf_transformation,[],[f5])).
% 22.31/3.18  fof(f5,axiom,(
% 22.31/3.18    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 22.31/3.18  fof(f39,plain,(
% 22.31/3.18    ~spl4_1),
% 22.31/3.18    inference(avatar_split_clause,[],[f22,f36])).
% 22.31/3.18  fof(f22,plain,(
% 22.31/3.18    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 22.31/3.18    inference(cnf_transformation,[],[f19])).
% 22.31/3.18  fof(f19,plain,(
% 22.31/3.18    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 22.31/3.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).
% 22.31/3.18  fof(f18,plain,(
% 22.31/3.18    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) => k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 22.31/3.18    introduced(choice_axiom,[])).
% 22.31/3.18  fof(f13,plain,(
% 22.31/3.18    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 22.31/3.18    inference(ennf_transformation,[],[f12])).
% 22.31/3.18  fof(f12,negated_conjecture,(
% 22.31/3.18    ~! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 22.31/3.18    inference(negated_conjecture,[],[f11])).
% 22.31/3.18  fof(f11,conjecture,(
% 22.31/3.18    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 22.31/3.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).
% 22.31/3.18  % SZS output end Proof for theBenchmark
% 22.31/3.18  % (6318)------------------------------
% 22.31/3.18  % (6318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.31/3.18  % (6318)Termination reason: Refutation
% 22.31/3.18  
% 22.31/3.18  % (6318)Memory used [KB]: 120253
% 22.31/3.18  % (6318)Time elapsed: 2.751 s
% 22.31/3.18  % (6318)------------------------------
% 22.31/3.18  % (6318)------------------------------
% 22.62/3.19  % (6312)Success in time 2.829 s
%------------------------------------------------------------------------------
