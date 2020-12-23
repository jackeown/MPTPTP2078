%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:25 EST 2020

% Result     : Theorem 23.33s
% Output     : Refutation 23.33s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 855 expanded)
%              Number of leaves         :   67 ( 424 expanded)
%              Depth                    :   11
%              Number of atoms          :  829 (2090 expanded)
%              Number of equality atoms :  228 ( 798 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f97,f108,f116,f120,f136,f149,f153,f161,f174,f181,f193,f212,f216,f255,f267,f308,f316,f339,f349,f372,f411,f442,f446,f519,f523,f527,f621,f633,f637,f681,f1072,f1080,f1204,f1327,f1403,f1791,f2108,f2644,f2828,f14582,f16155,f17815,f19122,f19823,f20240,f24942,f27426,f35964,f38600,f40134,f40508])).

fof(f40508,plain,
    ( spl2_12
    | ~ spl2_33
    | ~ spl2_36
    | ~ spl2_50
    | ~ spl2_113
    | ~ spl2_130
    | ~ spl2_157
    | ~ spl2_160 ),
    inference(avatar_contradiction_clause,[],[f40507])).

fof(f40507,plain,
    ( $false
    | spl2_12
    | ~ spl2_33
    | ~ spl2_36
    | ~ spl2_50
    | ~ spl2_113
    | ~ spl2_130
    | ~ spl2_157
    | ~ spl2_160 ),
    inference(subsumption_resolution,[],[f148,f40506])).

fof(f40506,plain,
    ( ! [X198,X197] : k5_xboole_0(X197,X198) = k4_xboole_0(k5_xboole_0(X197,k4_xboole_0(X198,X197)),k4_xboole_0(X197,k4_xboole_0(X197,X198)))
    | ~ spl2_33
    | ~ spl2_36
    | ~ spl2_50
    | ~ spl2_113
    | ~ spl2_130
    | ~ spl2_157
    | ~ spl2_160 ),
    inference(forward_demodulation,[],[f40316,f40424])).

fof(f40424,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(X21,k5_xboole_0(X21,X22))
    | ~ spl2_33
    | ~ spl2_36
    | ~ spl2_50
    | ~ spl2_113
    | ~ spl2_157
    | ~ spl2_160 ),
    inference(forward_demodulation,[],[f40423,f620])).

fof(f620,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl2_36
  <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f40423,plain,
    ( ! [X21,X22] : k5_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(X21,k5_xboole_0(X21,X22))
    | ~ spl2_33
    | ~ spl2_50
    | ~ spl2_113
    | ~ spl2_157
    | ~ spl2_160 ),
    inference(forward_demodulation,[],[f40247,f38882])).

fof(f38882,plain,
    ( ! [X116,X117] : k4_xboole_0(X116,X117) = k4_xboole_0(k5_xboole_0(X116,X117),k4_xboole_0(X117,X116))
    | ~ spl2_50
    | ~ spl2_113
    | ~ spl2_157 ),
    inference(forward_demodulation,[],[f38651,f1402])).

fof(f1402,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X27,X26) = k4_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X28))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1401,plain,
    ( spl2_50
  <=> ! [X27,X26,X28] : k4_xboole_0(X27,X26) = k4_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X28)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f38651,plain,
    ( ! [X116,X117] : k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(X117,X116)) = k4_xboole_0(k5_xboole_0(X116,X117),k4_xboole_0(X117,X116))
    | ~ spl2_113
    | ~ spl2_157 ),
    inference(superposition,[],[f38599,f20239])).

fof(f20239,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))
    | ~ spl2_113 ),
    inference(avatar_component_clause,[],[f20238])).

fof(f20238,plain,
    ( spl2_113
  <=> ! [X3,X2] : k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).

fof(f38599,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k5_xboole_0(X5,X6),X6)
    | ~ spl2_157 ),
    inference(avatar_component_clause,[],[f38598])).

fof(f38598,plain,
    ( spl2_157
  <=> ! [X5,X6] : k4_xboole_0(X5,X6) = k4_xboole_0(k5_xboole_0(X5,X6),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).

fof(f40247,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,k5_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)))
    | ~ spl2_33
    | ~ spl2_160 ),
    inference(superposition,[],[f518,f40133])).

fof(f40133,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(k5_xboole_0(X4,X3),X4)
    | ~ spl2_160 ),
    inference(avatar_component_clause,[],[f40132])).

fof(f40132,plain,
    ( spl2_160
  <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k4_xboole_0(k5_xboole_0(X4,X3),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_160])])).

fof(f518,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl2_33
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f40316,plain,
    ( ! [X198,X197] : k5_xboole_0(X197,X198) = k4_xboole_0(k5_xboole_0(X197,k4_xboole_0(X198,X197)),k4_xboole_0(X197,k5_xboole_0(X197,X198)))
    | ~ spl2_130
    | ~ spl2_160 ),
    inference(superposition,[],[f27425,f40133])).

fof(f27425,plain,
    ( ! [X21,X22] : k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = X22
    | ~ spl2_130 ),
    inference(avatar_component_clause,[],[f27424])).

fof(f27424,plain,
    ( spl2_130
  <=> ! [X22,X21] : k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = X22 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).

fof(f148,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_12
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f40134,plain,
    ( spl2_160
    | ~ spl2_126
    | ~ spl2_152 ),
    inference(avatar_split_clause,[],[f38181,f35962,f24940,f40132])).

fof(f24940,plain,
    ( spl2_126
  <=> ! [X32,X31] : k5_xboole_0(X31,X32) = k5_xboole_0(k4_xboole_0(X32,X31),k4_xboole_0(X31,X32)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).

fof(f35962,plain,
    ( spl2_152
  <=> ! [X16,X15,X14] : k4_xboole_0(X16,X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_152])])).

fof(f38181,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(k5_xboole_0(X4,X3),X4)
    | ~ spl2_126
    | ~ spl2_152 ),
    inference(superposition,[],[f35963,f24941])).

fof(f24941,plain,
    ( ! [X31,X32] : k5_xboole_0(X31,X32) = k5_xboole_0(k4_xboole_0(X32,X31),k4_xboole_0(X31,X32))
    | ~ spl2_126 ),
    inference(avatar_component_clause,[],[f24940])).

fof(f35963,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(X16,X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14)
    | ~ spl2_152 ),
    inference(avatar_component_clause,[],[f35962])).

fof(f38600,plain,
    ( spl2_157
    | ~ spl2_113
    | ~ spl2_152 ),
    inference(avatar_split_clause,[],[f38182,f35962,f20238,f38598])).

fof(f38182,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k5_xboole_0(X5,X6),X6)
    | ~ spl2_113
    | ~ spl2_152 ),
    inference(superposition,[],[f35963,f20239])).

fof(f35964,plain,
    ( spl2_152
    | ~ spl2_9
    | ~ spl2_54
    | ~ spl2_106 ),
    inference(avatar_split_clause,[],[f18224,f17813,f1789,f114,f35962])).

fof(f114,plain,
    ( spl2_9
  <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f1789,plain,
    ( spl2_54
  <=> ! [X27,X26,X28] : k4_xboole_0(X27,X28) = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f17813,plain,
    ( spl2_106
  <=> ! [X5,X4,X6] : k4_xboole_0(X6,X4) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).

fof(f18224,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(X16,X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14)
    | ~ spl2_9
    | ~ spl2_54
    | ~ spl2_106 ),
    inference(forward_demodulation,[],[f18125,f115])).

fof(f115,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f18125,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,X14),X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14)
    | ~ spl2_54
    | ~ spl2_106 ),
    inference(superposition,[],[f17814,f1790])).

fof(f1790,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X27,X28) = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f1789])).

fof(f17814,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(X6,X4) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4)
    | ~ spl2_106 ),
    inference(avatar_component_clause,[],[f17813])).

fof(f27426,plain,
    ( spl2_130
    | ~ spl2_26
    | ~ spl2_36
    | ~ spl2_39
    | ~ spl2_67
    | ~ spl2_94
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f19475,f19120,f14580,f2642,f631,f619,f347,f27424])).

fof(f347,plain,
    ( spl2_26
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f631,plain,
    ( spl2_39
  <=> ! [X5,X4] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f2642,plain,
    ( spl2_67
  <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f14580,plain,
    ( spl2_94
  <=> ! [X3,X2] : k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).

fof(f19120,plain,
    ( spl2_109
  <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X6,X7),X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).

fof(f19475,plain,
    ( ! [X21,X22] : k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = X22
    | ~ spl2_26
    | ~ spl2_36
    | ~ spl2_39
    | ~ spl2_67
    | ~ spl2_94
    | ~ spl2_109 ),
    inference(backward_demodulation,[],[f15785,f19472])).

fof(f19472,plain,
    ( ! [X28,X27] : k5_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X27,X28)) = X28
    | ~ spl2_26
    | ~ spl2_39
    | ~ spl2_67
    | ~ spl2_94
    | ~ spl2_109 ),
    inference(backward_demodulation,[],[f15788,f19469])).

fof(f19469,plain,
    ( ! [X78,X77] : k4_xboole_0(X78,k4_xboole_0(X78,k5_xboole_0(X77,k4_xboole_0(X78,X77)))) = X78
    | ~ spl2_26
    | ~ spl2_67
    | ~ spl2_94
    | ~ spl2_109 ),
    inference(backward_demodulation,[],[f15808,f19197])).

fof(f19197,plain,
    ( ! [X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X11,X10))) = X11
    | ~ spl2_26
    | ~ spl2_109 ),
    inference(superposition,[],[f348,f19121])).

fof(f19121,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X6,X7),X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6))
    | ~ spl2_109 ),
    inference(avatar_component_clause,[],[f19120])).

fof(f348,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f347])).

fof(f15808,plain,
    ( ! [X78,X77] : k4_xboole_0(X78,k4_xboole_0(X78,k5_xboole_0(X77,k4_xboole_0(X78,X77)))) = k5_xboole_0(k4_xboole_0(X77,X78),k5_xboole_0(X77,k4_xboole_0(X78,X77)))
    | ~ spl2_67
    | ~ spl2_94 ),
    inference(superposition,[],[f2643,f14581])).

fof(f14581,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2)
    | ~ spl2_94 ),
    inference(avatar_component_clause,[],[f14580])).

fof(f2643,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f2642])).

fof(f15788,plain,
    ( ! [X28,X27] : k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X27,k4_xboole_0(X28,X27)))) = k5_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X27,X28))
    | ~ spl2_39
    | ~ spl2_94 ),
    inference(superposition,[],[f632,f14581])).

fof(f632,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f631])).

fof(f15785,plain,
    ( ! [X21,X22] : k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = k5_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22))
    | ~ spl2_36
    | ~ spl2_94 ),
    inference(superposition,[],[f620,f14581])).

fof(f24942,plain,
    ( spl2_126
    | ~ spl2_78
    | ~ spl2_111 ),
    inference(avatar_split_clause,[],[f19924,f19821,f2826,f24940])).

fof(f2826,plain,
    ( spl2_78
  <=> ! [X9,X11,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(X10,k5_xboole_0(X11,X9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f19821,plain,
    ( spl2_111
  <=> ! [X11,X10] : k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X11,X10))) = X11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).

fof(f19924,plain,
    ( ! [X31,X32] : k5_xboole_0(X31,X32) = k5_xboole_0(k4_xboole_0(X32,X31),k4_xboole_0(X31,X32))
    | ~ spl2_78
    | ~ spl2_111 ),
    inference(superposition,[],[f2827,f19822])).

fof(f19822,plain,
    ( ! [X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X11,X10))) = X11
    | ~ spl2_111 ),
    inference(avatar_component_clause,[],[f19821])).

fof(f2827,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(X10,k5_xboole_0(X11,X9)))
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f2826])).

fof(f20240,plain,
    ( spl2_113
    | ~ spl2_40
    | ~ spl2_46
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f18916,f16153,f1078,f635,f20238])).

fof(f635,plain,
    ( spl2_40
  <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f1078,plain,
    ( spl2_46
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f16153,plain,
    ( spl2_98
  <=> ! [X1,X0,X2] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f18916,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))
    | ~ spl2_40
    | ~ spl2_46
    | ~ spl2_98 ),
    inference(forward_demodulation,[],[f18697,f1079])).

fof(f1079,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f1078])).

fof(f18697,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X3,X2))
    | ~ spl2_40
    | ~ spl2_98 ),
    inference(superposition,[],[f16154,f636])).

fof(f636,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5)
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f635])).

fof(f16154,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2)
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f16153])).

fof(f19823,plain,
    ( spl2_111
    | ~ spl2_26
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f19197,f19120,f347,f19821])).

fof(f19122,plain,
    ( spl2_109
    | ~ spl2_34
    | ~ spl2_46
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f18957,f16153,f1078,f521,f19120])).

fof(f521,plain,
    ( spl2_34
  <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f18957,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X6,X7),X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6))
    | ~ spl2_34
    | ~ spl2_46
    | ~ spl2_98 ),
    inference(forward_demodulation,[],[f18699,f1079])).

fof(f18699,plain,
    ( ! [X6,X7] : k5_xboole_0(X6,k4_xboole_0(X7,X6)) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))),X7)
    | ~ spl2_34
    | ~ spl2_98 ),
    inference(superposition,[],[f16154,f522])).

fof(f522,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f521])).

fof(f17815,plain,
    ( spl2_106
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_41
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f2742,f2106,f679,f265,f253,f17813])).

fof(f253,plain,
    ( spl2_20
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f265,plain,
    ( spl2_21
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f679,plain,
    ( spl2_41
  <=> ! [X5,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f2106,plain,
    ( spl2_57
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f2742,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(X6,X4) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4)
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_41
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f2741,f254])).

fof(f254,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f253])).

fof(f2741,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4) = k5_xboole_0(k4_xboole_0(X6,X4),k1_xboole_0)
    | ~ spl2_21
    | ~ spl2_41
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f2671,f266])).

fof(f266,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f265])).

fof(f2671,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4) = k5_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X4)))
    | ~ spl2_41
    | ~ spl2_57 ),
    inference(superposition,[],[f2107,f680])).

fof(f680,plain,
    ( ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f679])).

fof(f2107,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f2106])).

fof(f16155,plain,
    ( spl2_98
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f144,f134,f45,f16153])).

fof(f45,plain,
    ( spl2_2
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f134,plain,
    ( spl2_11
  <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f144,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2)
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f46,f135])).

fof(f135,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f46,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f14582,plain,
    ( spl2_94
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f2740,f2106,f337,f265,f253,f14580])).

fof(f337,plain,
    ( spl2_25
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f2740,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2)
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f2739,f254])).

fof(f2739,plain,
    ( ! [X2,X3] : k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2) = k5_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0)
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f2670,f266])).

fof(f2670,plain,
    ( ! [X2,X3] : k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2) = k5_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2)))
    | ~ spl2_25
    | ~ spl2_57 ),
    inference(superposition,[],[f2107,f338])).

fof(f338,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f337])).

fof(f2828,plain,
    ( spl2_78
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f1608,f1070,f444,f45,f2826])).

fof(f444,plain,
    ( spl2_32
  <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f1070,plain,
    ( spl2_44
  <=> ! [X11,X10,X12] : k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1608,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(X10,k5_xboole_0(X11,X9)))
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f1577,f46])).

fof(f1577,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(k5_xboole_0(X10,X11),X9))
    | ~ spl2_32
    | ~ spl2_44 ),
    inference(superposition,[],[f1071,f445])).

fof(f445,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1071,plain,
    ( ! [X12,X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12)))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f2644,plain,
    ( spl2_67
    | ~ spl2_31
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f546,f517,f440,f2642])).

fof(f440,plain,
    ( spl2_31
  <=> ! [X5,X6] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f546,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_31
    | ~ spl2_33 ),
    inference(superposition,[],[f441,f518])).

fof(f441,plain,
    ( ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f440])).

fof(f2108,plain,(
    spl2_57 ),
    inference(avatar_split_clause,[],[f37,f2106])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f28,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f1791,plain,
    ( spl2_54
    | ~ spl2_7
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f1445,f1401,f95,f1789])).

fof(f95,plain,
    ( spl2_7
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f1445,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X27,X28) = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))
    | ~ spl2_7
    | ~ spl2_50 ),
    inference(superposition,[],[f96,f1402])).

fof(f96,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1403,plain,
    ( spl2_50
    | ~ spl2_7
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f1337,f1325,f95,f1401])).

fof(f1325,plain,
    ( spl2_49
  <=> ! [X16,X15,X17] : k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,X16),X17)) = X16 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f1337,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X27,X26) = k4_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X28))
    | ~ spl2_7
    | ~ spl2_49 ),
    inference(superposition,[],[f1326,f96])).

fof(f1326,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,X16),X17)) = X16
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f1325])).

fof(f1327,plain,
    ( spl2_49
    | ~ spl2_22
    | ~ spl2_41
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f1279,f1202,f679,f306,f1325])).

fof(f306,plain,
    ( spl2_22
  <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f1202,plain,
    ( spl2_47
  <=> ! [X18,X17,X19] : k4_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19)))) = X19 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f1279,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,X16),X17)) = X16
    | ~ spl2_22
    | ~ spl2_41
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f1229,f307])).

fof(f307,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f306])).

fof(f1229,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),X17),k1_xboole_0)) = X16
    | ~ spl2_41
    | ~ spl2_47 ),
    inference(superposition,[],[f1203,f680])).

fof(f1203,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19)))) = X19
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1204,plain,
    ( spl2_47
    | ~ spl2_7
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f1115,f525,f95,f1202])).

fof(f525,plain,
    ( spl2_35
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f1115,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19)))) = X19
    | ~ spl2_7
    | ~ spl2_35 ),
    inference(superposition,[],[f96,f526])).

fof(f526,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f525])).

fof(f1080,plain,
    ( spl2_46
    | ~ spl2_3
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f646,f619,f49,f1078])).

fof(f49,plain,
    ( spl2_3
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f646,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_3
    | ~ spl2_36 ),
    inference(superposition,[],[f620,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f1072,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f418,f409,f45,f1070])).

fof(f409,plain,
    ( spl2_29
  <=> ! [X1,X2] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f418,plain,
    ( ! [X12,X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12)))
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(superposition,[],[f410,f46])).

fof(f410,plain,
    ( ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f409])).

fof(f681,plain,
    ( spl2_41
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_33
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f667,f619,f517,f314,f53,f679])).

fof(f53,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f314,plain,
    ( spl2_24
  <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f667,plain,
    ( ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_33
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f664,f315])).

fof(f315,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f314])).

fof(f664,plain,
    ( ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))
    | ~ spl2_4
    | ~ spl2_33
    | ~ spl2_36 ),
    inference(backward_demodulation,[],[f531,f662])).

fof(f662,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))
    | ~ spl2_4
    | ~ spl2_33
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f641,f518])).

fof(f641,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))) = k5_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))
    | ~ spl2_4
    | ~ spl2_36 ),
    inference(superposition,[],[f620,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f531,plain,
    ( ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))))
    | ~ spl2_4
    | ~ spl2_33 ),
    inference(superposition,[],[f518,f54])).

fof(f637,plain,
    ( spl2_40
    | ~ spl2_26
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f588,f521,f347,f635])).

fof(f588,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5)
    | ~ spl2_26
    | ~ spl2_34 ),
    inference(superposition,[],[f348,f522])).

fof(f633,plain,
    ( spl2_39
    | ~ spl2_26
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f543,f517,f347,f631])).

fof(f543,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_26
    | ~ spl2_33 ),
    inference(superposition,[],[f348,f518])).

fof(f621,plain,
    ( spl2_36
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f351,f347,f49,f619])).

fof(f351,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(superposition,[],[f348,f50])).

fof(f527,plain,(
    spl2_35 ),
    inference(avatar_split_clause,[],[f35,f525])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f523,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f137,f134,f53,f521])).

fof(f137,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(superposition,[],[f135,f54])).

fof(f519,plain,
    ( spl2_33
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f70,f53,f49,f517])).

fof(f70,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f50,f54])).

fof(f446,plain,
    ( spl2_32
    | ~ spl2_26
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f423,f409,f347,f444])).

fof(f423,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_26
    | ~ spl2_29 ),
    inference(superposition,[],[f348,f410])).

fof(f442,plain,
    ( spl2_31
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f415,f409,f440])).

fof(f415,plain,
    ( ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5
    | ~ spl2_29 ),
    inference(superposition,[],[f410,f410])).

fof(f411,plain,
    ( spl2_29
    | ~ spl2_20
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f401,f370,f347,f253,f409])).

fof(f370,plain,
    ( spl2_28
  <=> ! [X1,X2] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f401,plain,
    ( ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1
    | ~ spl2_20
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f389,f254])).

fof(f389,plain,
    ( ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0)
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(superposition,[],[f348,f371])).

fof(f371,plain,
    ( ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f370])).

fof(f372,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f292,f265,f214,f210,f191,f134,f106,f95,f53,f49,f45,f41,f370])).

fof(f41,plain,
    ( spl2_1
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f106,plain,
    ( spl2_8
  <=> ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f191,plain,
    ( spl2_17
  <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f210,plain,
    ( spl2_18
  <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f214,plain,
    ( spl2_19
  <=> ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f292,plain,
    ( ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f109,f283])).

fof(f283,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f244,f274])).

fof(f274,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(superposition,[],[f96,f266])).

fof(f244,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f215,f238])).

fof(f238,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f207,f227])).

fof(f227,plain,
    ( ! [X2] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2))
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(superposition,[],[f135,f211])).

fof(f211,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f207,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f69,f206])).

fof(f206,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f194,f70])).

fof(f194,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(superposition,[],[f192,f54])).

fof(f192,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f191])).

fof(f69,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f42,f54])).

fof(f42,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f215,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f214])).

fof(f109,plain,
    ( ! [X2,X1] : k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f107,f46])).

fof(f107,plain,
    ( ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f349,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f295,f265,f214,f210,f191,f151,f134,f106,f95,f53,f49,f45,f41,f347])).

fof(f151,plain,
    ( spl2_13
  <=> ! [X4] : k5_xboole_0(k4_xboole_0(X4,X4),X4) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f295,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f289,f287])).

fof(f287,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f152,f283])).

fof(f152,plain,
    ( ! [X4] : k5_xboole_0(k4_xboole_0(X4,X4),X4) = X4
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f289,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f110,f283])).

fof(f110,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f46,f107])).

fof(f339,plain,
    ( spl2_25
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f283,f265,f214,f210,f191,f134,f95,f53,f49,f41,f337])).

fof(f316,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f290,f265,f214,f210,f191,f134,f106,f95,f53,f49,f41,f314])).

fof(f290,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f107,f283])).

fof(f308,plain,
    ( spl2_22
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f274,f265,f95,f306])).

fof(f267,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f238,f210,f191,f134,f53,f49,f41,f265])).

fof(f255,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f239,f210,f191,f134,f53,f49,f41,f253])).

fof(f239,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f42,f238])).

fof(f216,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f206,f191,f53,f49,f214])).

fof(f212,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f199,f191,f49,f210])).

fof(f199,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(superposition,[],[f192,f50])).

fof(f193,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f185,f179,f49,f191])).

fof(f179,plain,
    ( spl2_16
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f185,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(superposition,[],[f180,f50])).

fof(f180,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f176,f171,f45,f179])).

fof(f171,plain,
    ( spl2_15
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f176,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(superposition,[],[f46,f173])).

fof(f173,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f162,f158,f41,f171])).

fof(f158,plain,
    ( spl2_14
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f162,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(superposition,[],[f42,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl2_14
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f154,f151,f118,f158])).

fof(f118,plain,
    ( spl2_10
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f154,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(superposition,[],[f152,f119])).

fof(f119,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f153,plain,
    ( spl2_13
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f142,f134,f95,f151])).

fof(f142,plain,
    ( ! [X4] : k5_xboole_0(k4_xboole_0(X4,X4),X4) = X4
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(superposition,[],[f135,f96])).

fof(f149,plain,(
    ~ spl2_12 ),
    inference(avatar_split_clause,[],[f30,f146])).

fof(f30,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f21,f23])).

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

fof(f136,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f83,f57,f49,f134])).

fof(f57,plain,
    ( spl2_5
  <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f83,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f34,f77])).

fof(f77,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f58,f50])).

fof(f58,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f24,f21,f23])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f120,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f101,f95,f41,f118])).

fof(f101,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f42,f96])).

fof(f116,plain,
    ( spl2_9
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f100,f95,f114])).

fof(f100,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)
    | ~ spl2_7 ),
    inference(superposition,[],[f96,f96])).

fof(f108,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f102,f95,f49,f106])).

fof(f102,plain,
    ( ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f50,f96])).

fof(f97,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f77,f57,f49,f95])).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f38,f57])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f33,f35])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f21,f23])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f53])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f23,f23])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f31,f41])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (24644)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (24652)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (24640)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (24646)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (24642)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24655)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (24647)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (24656)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (24650)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (24654)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (24641)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (24643)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (24645)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (24657)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (24649)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (24651)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (24651)Refutation not found, incomplete strategy% (24651)------------------------------
% 0.21/0.52  % (24651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24651)Memory used [KB]: 10490
% 0.21/0.52  % (24651)Time elapsed: 0.078 s
% 0.21/0.52  % (24651)------------------------------
% 0.21/0.52  % (24651)------------------------------
% 0.21/0.52  % (24648)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (24653)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 5.29/1.04  % (24644)Time limit reached!
% 5.29/1.04  % (24644)------------------------------
% 5.29/1.04  % (24644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.29/1.04  % (24644)Termination reason: Time limit
% 5.29/1.04  % (24644)Termination phase: Saturation
% 5.29/1.04  
% 5.29/1.04  % (24644)Memory used [KB]: 21236
% 5.29/1.04  % (24644)Time elapsed: 0.600 s
% 5.29/1.04  % (24644)------------------------------
% 5.29/1.04  % (24644)------------------------------
% 12.49/1.93  % (24646)Time limit reached!
% 12.49/1.93  % (24646)------------------------------
% 12.49/1.93  % (24646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.93  % (24646)Termination reason: Time limit
% 12.49/1.93  % (24646)Termination phase: Saturation
% 12.49/1.93  
% 12.49/1.93  % (24646)Memory used [KB]: 38250
% 12.49/1.93  % (24646)Time elapsed: 1.500 s
% 12.49/1.93  % (24646)------------------------------
% 12.49/1.93  % (24646)------------------------------
% 12.49/1.94  % (24645)Time limit reached!
% 12.49/1.94  % (24645)------------------------------
% 12.49/1.94  % (24645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.94  % (24645)Termination reason: Time limit
% 12.49/1.94  % (24645)Termination phase: Saturation
% 12.49/1.94  
% 12.49/1.94  % (24645)Memory used [KB]: 26609
% 12.49/1.94  % (24645)Time elapsed: 1.500 s
% 12.49/1.94  % (24645)------------------------------
% 12.49/1.94  % (24645)------------------------------
% 14.91/2.25  % (24642)Time limit reached!
% 14.91/2.25  % (24642)------------------------------
% 14.91/2.25  % (24642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.91/2.26  % (24642)Termination reason: Time limit
% 14.91/2.26  
% 14.91/2.26  % (24642)Memory used [KB]: 38890
% 14.91/2.26  % (24642)Time elapsed: 1.833 s
% 14.91/2.26  % (24642)------------------------------
% 14.91/2.26  % (24642)------------------------------
% 17.83/2.63  % (24652)Time limit reached!
% 17.83/2.63  % (24652)------------------------------
% 17.83/2.63  % (24652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.83/2.63  % (24652)Termination reason: Time limit
% 17.83/2.63  
% 17.83/2.63  % (24652)Memory used [KB]: 63453
% 17.83/2.63  % (24652)Time elapsed: 2.220 s
% 17.83/2.63  % (24652)------------------------------
% 17.83/2.63  % (24652)------------------------------
% 23.33/3.31  % (24647)Refutation found. Thanks to Tanya!
% 23.33/3.31  % SZS status Theorem for theBenchmark
% 23.33/3.31  % SZS output start Proof for theBenchmark
% 23.33/3.31  fof(f40553,plain,(
% 23.33/3.31    $false),
% 23.33/3.31    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f97,f108,f116,f120,f136,f149,f153,f161,f174,f181,f193,f212,f216,f255,f267,f308,f316,f339,f349,f372,f411,f442,f446,f519,f523,f527,f621,f633,f637,f681,f1072,f1080,f1204,f1327,f1403,f1791,f2108,f2644,f2828,f14582,f16155,f17815,f19122,f19823,f20240,f24942,f27426,f35964,f38600,f40134,f40508])).
% 23.33/3.31  fof(f40508,plain,(
% 23.33/3.31    spl2_12 | ~spl2_33 | ~spl2_36 | ~spl2_50 | ~spl2_113 | ~spl2_130 | ~spl2_157 | ~spl2_160),
% 23.33/3.31    inference(avatar_contradiction_clause,[],[f40507])).
% 23.33/3.31  fof(f40507,plain,(
% 23.33/3.31    $false | (spl2_12 | ~spl2_33 | ~spl2_36 | ~spl2_50 | ~spl2_113 | ~spl2_130 | ~spl2_157 | ~spl2_160)),
% 23.33/3.31    inference(subsumption_resolution,[],[f148,f40506])).
% 23.33/3.31  fof(f40506,plain,(
% 23.33/3.31    ( ! [X198,X197] : (k5_xboole_0(X197,X198) = k4_xboole_0(k5_xboole_0(X197,k4_xboole_0(X198,X197)),k4_xboole_0(X197,k4_xboole_0(X197,X198)))) ) | (~spl2_33 | ~spl2_36 | ~spl2_50 | ~spl2_113 | ~spl2_130 | ~spl2_157 | ~spl2_160)),
% 23.33/3.31    inference(forward_demodulation,[],[f40316,f40424])).
% 23.33/3.31  fof(f40424,plain,(
% 23.33/3.31    ( ! [X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(X21,k5_xboole_0(X21,X22))) ) | (~spl2_33 | ~spl2_36 | ~spl2_50 | ~spl2_113 | ~spl2_157 | ~spl2_160)),
% 23.33/3.31    inference(forward_demodulation,[],[f40423,f620])).
% 23.33/3.31  fof(f620,plain,(
% 23.33/3.31    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | ~spl2_36),
% 23.33/3.31    inference(avatar_component_clause,[],[f619])).
% 23.33/3.31  fof(f619,plain,(
% 23.33/3.31    spl2_36 <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 23.33/3.31  fof(f40423,plain,(
% 23.33/3.31    ( ! [X21,X22] : (k5_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(X21,k5_xboole_0(X21,X22))) ) | (~spl2_33 | ~spl2_50 | ~spl2_113 | ~spl2_157 | ~spl2_160)),
% 23.33/3.31    inference(forward_demodulation,[],[f40247,f38882])).
% 23.33/3.31  fof(f38882,plain,(
% 23.33/3.31    ( ! [X116,X117] : (k4_xboole_0(X116,X117) = k4_xboole_0(k5_xboole_0(X116,X117),k4_xboole_0(X117,X116))) ) | (~spl2_50 | ~spl2_113 | ~spl2_157)),
% 23.33/3.31    inference(forward_demodulation,[],[f38651,f1402])).
% 23.33/3.31  fof(f1402,plain,(
% 23.33/3.31    ( ! [X28,X26,X27] : (k4_xboole_0(X27,X26) = k4_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X28))) ) | ~spl2_50),
% 23.33/3.31    inference(avatar_component_clause,[],[f1401])).
% 23.33/3.31  fof(f1401,plain,(
% 23.33/3.31    spl2_50 <=> ! [X27,X26,X28] : k4_xboole_0(X27,X26) = k4_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X28))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 23.33/3.31  fof(f38651,plain,(
% 23.33/3.31    ( ! [X116,X117] : (k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(X117,X116)) = k4_xboole_0(k5_xboole_0(X116,X117),k4_xboole_0(X117,X116))) ) | (~spl2_113 | ~spl2_157)),
% 23.33/3.31    inference(superposition,[],[f38599,f20239])).
% 23.33/3.31  fof(f20239,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ) | ~spl2_113),
% 23.33/3.31    inference(avatar_component_clause,[],[f20238])).
% 23.33/3.31  fof(f20238,plain,(
% 23.33/3.31    spl2_113 <=> ! [X3,X2] : k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).
% 23.33/3.31  fof(f38599,plain,(
% 23.33/3.31    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k5_xboole_0(X5,X6),X6)) ) | ~spl2_157),
% 23.33/3.31    inference(avatar_component_clause,[],[f38598])).
% 23.33/3.31  fof(f38598,plain,(
% 23.33/3.31    spl2_157 <=> ! [X5,X6] : k4_xboole_0(X5,X6) = k4_xboole_0(k5_xboole_0(X5,X6),X6)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).
% 23.33/3.31  fof(f40247,plain,(
% 23.33/3.31    ( ! [X21,X22] : (k4_xboole_0(X21,k5_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)))) ) | (~spl2_33 | ~spl2_160)),
% 23.33/3.31    inference(superposition,[],[f518,f40133])).
% 23.33/3.31  fof(f40133,plain,(
% 23.33/3.31    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(k5_xboole_0(X4,X3),X4)) ) | ~spl2_160),
% 23.33/3.31    inference(avatar_component_clause,[],[f40132])).
% 23.33/3.31  fof(f40132,plain,(
% 23.33/3.31    spl2_160 <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k4_xboole_0(k5_xboole_0(X4,X3),X4)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_160])])).
% 23.33/3.31  fof(f518,plain,(
% 23.33/3.31    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ) | ~spl2_33),
% 23.33/3.31    inference(avatar_component_clause,[],[f517])).
% 23.33/3.31  fof(f517,plain,(
% 23.33/3.31    spl2_33 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 23.33/3.31  fof(f40316,plain,(
% 23.33/3.31    ( ! [X198,X197] : (k5_xboole_0(X197,X198) = k4_xboole_0(k5_xboole_0(X197,k4_xboole_0(X198,X197)),k4_xboole_0(X197,k5_xboole_0(X197,X198)))) ) | (~spl2_130 | ~spl2_160)),
% 23.33/3.31    inference(superposition,[],[f27425,f40133])).
% 23.33/3.31  fof(f27425,plain,(
% 23.33/3.31    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = X22) ) | ~spl2_130),
% 23.33/3.31    inference(avatar_component_clause,[],[f27424])).
% 23.33/3.31  fof(f27424,plain,(
% 23.33/3.31    spl2_130 <=> ! [X22,X21] : k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = X22),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).
% 23.33/3.31  fof(f148,plain,(
% 23.33/3.31    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_12),
% 23.33/3.31    inference(avatar_component_clause,[],[f146])).
% 23.33/3.31  fof(f146,plain,(
% 23.33/3.31    spl2_12 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 23.33/3.31  fof(f40134,plain,(
% 23.33/3.31    spl2_160 | ~spl2_126 | ~spl2_152),
% 23.33/3.31    inference(avatar_split_clause,[],[f38181,f35962,f24940,f40132])).
% 23.33/3.31  fof(f24940,plain,(
% 23.33/3.31    spl2_126 <=> ! [X32,X31] : k5_xboole_0(X31,X32) = k5_xboole_0(k4_xboole_0(X32,X31),k4_xboole_0(X31,X32))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).
% 23.33/3.31  fof(f35962,plain,(
% 23.33/3.31    spl2_152 <=> ! [X16,X15,X14] : k4_xboole_0(X16,X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_152])])).
% 23.33/3.31  fof(f38181,plain,(
% 23.33/3.31    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(k5_xboole_0(X4,X3),X4)) ) | (~spl2_126 | ~spl2_152)),
% 23.33/3.31    inference(superposition,[],[f35963,f24941])).
% 23.33/3.31  fof(f24941,plain,(
% 23.33/3.31    ( ! [X31,X32] : (k5_xboole_0(X31,X32) = k5_xboole_0(k4_xboole_0(X32,X31),k4_xboole_0(X31,X32))) ) | ~spl2_126),
% 23.33/3.31    inference(avatar_component_clause,[],[f24940])).
% 23.33/3.31  fof(f35963,plain,(
% 23.33/3.31    ( ! [X14,X15,X16] : (k4_xboole_0(X16,X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14)) ) | ~spl2_152),
% 23.33/3.31    inference(avatar_component_clause,[],[f35962])).
% 23.33/3.31  fof(f38600,plain,(
% 23.33/3.31    spl2_157 | ~spl2_113 | ~spl2_152),
% 23.33/3.31    inference(avatar_split_clause,[],[f38182,f35962,f20238,f38598])).
% 23.33/3.31  fof(f38182,plain,(
% 23.33/3.31    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k5_xboole_0(X5,X6),X6)) ) | (~spl2_113 | ~spl2_152)),
% 23.33/3.31    inference(superposition,[],[f35963,f20239])).
% 23.33/3.31  fof(f35964,plain,(
% 23.33/3.31    spl2_152 | ~spl2_9 | ~spl2_54 | ~spl2_106),
% 23.33/3.31    inference(avatar_split_clause,[],[f18224,f17813,f1789,f114,f35962])).
% 23.33/3.31  fof(f114,plain,(
% 23.33/3.31    spl2_9 <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 23.33/3.31  fof(f1789,plain,(
% 23.33/3.31    spl2_54 <=> ! [X27,X26,X28] : k4_xboole_0(X27,X28) = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 23.33/3.31  fof(f17813,plain,(
% 23.33/3.31    spl2_106 <=> ! [X5,X4,X6] : k4_xboole_0(X6,X4) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).
% 23.33/3.31  fof(f18224,plain,(
% 23.33/3.31    ( ! [X14,X15,X16] : (k4_xboole_0(X16,X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14)) ) | (~spl2_9 | ~spl2_54 | ~spl2_106)),
% 23.33/3.31    inference(forward_demodulation,[],[f18125,f115])).
% 23.33/3.31  fof(f115,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) ) | ~spl2_9),
% 23.33/3.31    inference(avatar_component_clause,[],[f114])).
% 23.33/3.31  fof(f18125,plain,(
% 23.33/3.31    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,X14),X14) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X16,X14),k4_xboole_0(X14,X15)),X14)) ) | (~spl2_54 | ~spl2_106)),
% 23.33/3.31    inference(superposition,[],[f17814,f1790])).
% 23.33/3.31  fof(f1790,plain,(
% 23.33/3.31    ( ! [X28,X26,X27] : (k4_xboole_0(X27,X28) = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))) ) | ~spl2_54),
% 23.33/3.31    inference(avatar_component_clause,[],[f1789])).
% 23.33/3.31  fof(f17814,plain,(
% 23.33/3.31    ( ! [X6,X4,X5] : (k4_xboole_0(X6,X4) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4)) ) | ~spl2_106),
% 23.33/3.31    inference(avatar_component_clause,[],[f17813])).
% 23.33/3.31  fof(f27426,plain,(
% 23.33/3.31    spl2_130 | ~spl2_26 | ~spl2_36 | ~spl2_39 | ~spl2_67 | ~spl2_94 | ~spl2_109),
% 23.33/3.31    inference(avatar_split_clause,[],[f19475,f19120,f14580,f2642,f631,f619,f347,f27424])).
% 23.33/3.31  fof(f347,plain,(
% 23.33/3.31    spl2_26 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 23.33/3.31  fof(f631,plain,(
% 23.33/3.31    spl2_39 <=> ! [X5,X4] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 23.33/3.31  fof(f2642,plain,(
% 23.33/3.31    spl2_67 <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 23.33/3.31  fof(f14580,plain,(
% 23.33/3.31    spl2_94 <=> ! [X3,X2] : k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).
% 23.33/3.31  fof(f19120,plain,(
% 23.33/3.31    spl2_109 <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X6,X7),X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).
% 23.33/3.31  fof(f19475,plain,(
% 23.33/3.31    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = X22) ) | (~spl2_26 | ~spl2_36 | ~spl2_39 | ~spl2_67 | ~spl2_94 | ~spl2_109)),
% 23.33/3.31    inference(backward_demodulation,[],[f15785,f19472])).
% 23.33/3.31  fof(f19472,plain,(
% 23.33/3.31    ( ! [X28,X27] : (k5_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X27,X28)) = X28) ) | (~spl2_26 | ~spl2_39 | ~spl2_67 | ~spl2_94 | ~spl2_109)),
% 23.33/3.31    inference(backward_demodulation,[],[f15788,f19469])).
% 23.33/3.31  fof(f19469,plain,(
% 23.33/3.31    ( ! [X78,X77] : (k4_xboole_0(X78,k4_xboole_0(X78,k5_xboole_0(X77,k4_xboole_0(X78,X77)))) = X78) ) | (~spl2_26 | ~spl2_67 | ~spl2_94 | ~spl2_109)),
% 23.33/3.31    inference(backward_demodulation,[],[f15808,f19197])).
% 23.33/3.31  fof(f19197,plain,(
% 23.33/3.31    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X11,X10))) = X11) ) | (~spl2_26 | ~spl2_109)),
% 23.33/3.31    inference(superposition,[],[f348,f19121])).
% 23.33/3.31  fof(f19121,plain,(
% 23.33/3.31    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6))) ) | ~spl2_109),
% 23.33/3.31    inference(avatar_component_clause,[],[f19120])).
% 23.33/3.31  fof(f348,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_26),
% 23.33/3.31    inference(avatar_component_clause,[],[f347])).
% 23.33/3.31  fof(f15808,plain,(
% 23.33/3.31    ( ! [X78,X77] : (k4_xboole_0(X78,k4_xboole_0(X78,k5_xboole_0(X77,k4_xboole_0(X78,X77)))) = k5_xboole_0(k4_xboole_0(X77,X78),k5_xboole_0(X77,k4_xboole_0(X78,X77)))) ) | (~spl2_67 | ~spl2_94)),
% 23.33/3.31    inference(superposition,[],[f2643,f14581])).
% 23.33/3.31  fof(f14581,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2)) ) | ~spl2_94),
% 23.33/3.31    inference(avatar_component_clause,[],[f14580])).
% 23.33/3.31  fof(f2643,plain,(
% 23.33/3.31    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | ~spl2_67),
% 23.33/3.31    inference(avatar_component_clause,[],[f2642])).
% 23.33/3.31  fof(f15788,plain,(
% 23.33/3.31    ( ! [X28,X27] : (k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X27,k4_xboole_0(X28,X27)))) = k5_xboole_0(k5_xboole_0(X27,k4_xboole_0(X28,X27)),k4_xboole_0(X27,X28))) ) | (~spl2_39 | ~spl2_94)),
% 23.33/3.31    inference(superposition,[],[f632,f14581])).
% 23.33/3.31  fof(f632,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl2_39),
% 23.33/3.31    inference(avatar_component_clause,[],[f631])).
% 23.33/3.31  fof(f15785,plain,(
% 23.33/3.31    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22)) = k5_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k4_xboole_0(X21,X22))) ) | (~spl2_36 | ~spl2_94)),
% 23.33/3.31    inference(superposition,[],[f620,f14581])).
% 23.33/3.31  fof(f24942,plain,(
% 23.33/3.31    spl2_126 | ~spl2_78 | ~spl2_111),
% 23.33/3.31    inference(avatar_split_clause,[],[f19924,f19821,f2826,f24940])).
% 23.33/3.31  fof(f2826,plain,(
% 23.33/3.31    spl2_78 <=> ! [X9,X11,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(X10,k5_xboole_0(X11,X9)))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 23.33/3.31  fof(f19821,plain,(
% 23.33/3.31    spl2_111 <=> ! [X11,X10] : k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X11,X10))) = X11),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).
% 23.33/3.31  fof(f19924,plain,(
% 23.33/3.31    ( ! [X31,X32] : (k5_xboole_0(X31,X32) = k5_xboole_0(k4_xboole_0(X32,X31),k4_xboole_0(X31,X32))) ) | (~spl2_78 | ~spl2_111)),
% 23.33/3.31    inference(superposition,[],[f2827,f19822])).
% 23.33/3.31  fof(f19822,plain,(
% 23.33/3.31    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X11,X10))) = X11) ) | ~spl2_111),
% 23.33/3.31    inference(avatar_component_clause,[],[f19821])).
% 23.33/3.31  fof(f2827,plain,(
% 23.33/3.31    ( ! [X10,X11,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(X10,k5_xboole_0(X11,X9)))) ) | ~spl2_78),
% 23.33/3.31    inference(avatar_component_clause,[],[f2826])).
% 23.33/3.31  fof(f20240,plain,(
% 23.33/3.31    spl2_113 | ~spl2_40 | ~spl2_46 | ~spl2_98),
% 23.33/3.31    inference(avatar_split_clause,[],[f18916,f16153,f1078,f635,f20238])).
% 23.33/3.31  fof(f635,plain,(
% 23.33/3.31    spl2_40 <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 23.33/3.31  fof(f1078,plain,(
% 23.33/3.31    spl2_46 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 23.33/3.31  fof(f16153,plain,(
% 23.33/3.31    spl2_98 <=> ! [X1,X0,X2] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 23.33/3.31  fof(f18916,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ) | (~spl2_40 | ~spl2_46 | ~spl2_98)),
% 23.33/3.31    inference(forward_demodulation,[],[f18697,f1079])).
% 23.33/3.31  fof(f1079,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_46),
% 23.33/3.31    inference(avatar_component_clause,[],[f1078])).
% 23.33/3.31  fof(f18697,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X3,X2))) ) | (~spl2_40 | ~spl2_98)),
% 23.33/3.31    inference(superposition,[],[f16154,f636])).
% 23.33/3.31  fof(f636,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5)) ) | ~spl2_40),
% 23.33/3.31    inference(avatar_component_clause,[],[f635])).
% 23.33/3.31  fof(f16154,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2)) ) | ~spl2_98),
% 23.33/3.31    inference(avatar_component_clause,[],[f16153])).
% 23.33/3.31  fof(f19823,plain,(
% 23.33/3.31    spl2_111 | ~spl2_26 | ~spl2_109),
% 23.33/3.31    inference(avatar_split_clause,[],[f19197,f19120,f347,f19821])).
% 23.33/3.31  fof(f19122,plain,(
% 23.33/3.31    spl2_109 | ~spl2_34 | ~spl2_46 | ~spl2_98),
% 23.33/3.31    inference(avatar_split_clause,[],[f18957,f16153,f1078,f521,f19120])).
% 23.33/3.31  fof(f521,plain,(
% 23.33/3.31    spl2_34 <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 23.33/3.31  fof(f18957,plain,(
% 23.33/3.31    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6))) ) | (~spl2_34 | ~spl2_46 | ~spl2_98)),
% 23.33/3.31    inference(forward_demodulation,[],[f18699,f1079])).
% 23.33/3.31  fof(f18699,plain,(
% 23.33/3.31    ( ! [X6,X7] : (k5_xboole_0(X6,k4_xboole_0(X7,X6)) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))),X7)) ) | (~spl2_34 | ~spl2_98)),
% 23.33/3.31    inference(superposition,[],[f16154,f522])).
% 23.33/3.31  fof(f522,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_34),
% 23.33/3.31    inference(avatar_component_clause,[],[f521])).
% 23.33/3.31  fof(f17815,plain,(
% 23.33/3.31    spl2_106 | ~spl2_20 | ~spl2_21 | ~spl2_41 | ~spl2_57),
% 23.33/3.31    inference(avatar_split_clause,[],[f2742,f2106,f679,f265,f253,f17813])).
% 23.33/3.31  fof(f253,plain,(
% 23.33/3.31    spl2_20 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 23.33/3.31  fof(f265,plain,(
% 23.33/3.31    spl2_21 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 23.33/3.31  fof(f679,plain,(
% 23.33/3.31    spl2_41 <=> ! [X5,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 23.33/3.31  fof(f2106,plain,(
% 23.33/3.31    spl2_57 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 23.33/3.31  fof(f2742,plain,(
% 23.33/3.31    ( ! [X6,X4,X5] : (k4_xboole_0(X6,X4) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4)) ) | (~spl2_20 | ~spl2_21 | ~spl2_41 | ~spl2_57)),
% 23.33/3.31    inference(forward_demodulation,[],[f2741,f254])).
% 23.33/3.31  fof(f254,plain,(
% 23.33/3.31    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_20),
% 23.33/3.31    inference(avatar_component_clause,[],[f253])).
% 23.33/3.31  fof(f2741,plain,(
% 23.33/3.31    ( ! [X6,X4,X5] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4) = k5_xboole_0(k4_xboole_0(X6,X4),k1_xboole_0)) ) | (~spl2_21 | ~spl2_41 | ~spl2_57)),
% 23.33/3.31    inference(forward_demodulation,[],[f2671,f266])).
% 23.33/3.31  fof(f266,plain,(
% 23.33/3.31    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_21),
% 23.33/3.31    inference(avatar_component_clause,[],[f265])).
% 23.33/3.31  fof(f2671,plain,(
% 23.33/3.31    ( ! [X6,X4,X5] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)),X4) = k5_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X4)))) ) | (~spl2_41 | ~spl2_57)),
% 23.33/3.31    inference(superposition,[],[f2107,f680])).
% 23.33/3.31  fof(f680,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) ) | ~spl2_41),
% 23.33/3.31    inference(avatar_component_clause,[],[f679])).
% 23.33/3.31  fof(f2107,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) ) | ~spl2_57),
% 23.33/3.31    inference(avatar_component_clause,[],[f2106])).
% 23.33/3.31  fof(f16155,plain,(
% 23.33/3.31    spl2_98 | ~spl2_2 | ~spl2_11),
% 23.33/3.31    inference(avatar_split_clause,[],[f144,f134,f45,f16153])).
% 23.33/3.31  fof(f45,plain,(
% 23.33/3.31    spl2_2 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 23.33/3.31  fof(f134,plain,(
% 23.33/3.31    spl2_11 <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 23.33/3.31  fof(f144,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2)) ) | (~spl2_2 | ~spl2_11)),
% 23.33/3.31    inference(superposition,[],[f46,f135])).
% 23.33/3.31  fof(f135,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_11),
% 23.33/3.31    inference(avatar_component_clause,[],[f134])).
% 23.33/3.31  fof(f46,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_2),
% 23.33/3.31    inference(avatar_component_clause,[],[f45])).
% 23.33/3.31  fof(f14582,plain,(
% 23.33/3.31    spl2_94 | ~spl2_20 | ~spl2_21 | ~spl2_25 | ~spl2_57),
% 23.33/3.31    inference(avatar_split_clause,[],[f2740,f2106,f337,f265,f253,f14580])).
% 23.33/3.31  fof(f337,plain,(
% 23.33/3.31    spl2_25 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 23.33/3.31  fof(f2740,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2)) ) | (~spl2_20 | ~spl2_21 | ~spl2_25 | ~spl2_57)),
% 23.33/3.31    inference(forward_demodulation,[],[f2739,f254])).
% 23.33/3.31  fof(f2739,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2) = k5_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0)) ) | (~spl2_21 | ~spl2_25 | ~spl2_57)),
% 23.33/3.31    inference(forward_demodulation,[],[f2670,f266])).
% 23.33/3.31  fof(f2670,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X2) = k5_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2)))) ) | (~spl2_25 | ~spl2_57)),
% 23.33/3.31    inference(superposition,[],[f2107,f338])).
% 23.33/3.31  fof(f338,plain,(
% 23.33/3.31    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_25),
% 23.33/3.31    inference(avatar_component_clause,[],[f337])).
% 23.33/3.31  fof(f2828,plain,(
% 23.33/3.31    spl2_78 | ~spl2_2 | ~spl2_32 | ~spl2_44),
% 23.33/3.31    inference(avatar_split_clause,[],[f1608,f1070,f444,f45,f2826])).
% 23.33/3.31  fof(f444,plain,(
% 23.33/3.31    spl2_32 <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 23.33/3.31  fof(f1070,plain,(
% 23.33/3.31    spl2_44 <=> ! [X11,X10,X12] : k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12)))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 23.33/3.31  fof(f1608,plain,(
% 23.33/3.31    ( ! [X10,X11,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(X10,k5_xboole_0(X11,X9)))) ) | (~spl2_2 | ~spl2_32 | ~spl2_44)),
% 23.33/3.31    inference(forward_demodulation,[],[f1577,f46])).
% 23.33/3.31  fof(f1577,plain,(
% 23.33/3.31    ( ! [X10,X11,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(X11,k5_xboole_0(k5_xboole_0(X10,X11),X9))) ) | (~spl2_32 | ~spl2_44)),
% 23.33/3.31    inference(superposition,[],[f1071,f445])).
% 23.33/3.31  fof(f445,plain,(
% 23.33/3.31    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | ~spl2_32),
% 23.33/3.31    inference(avatar_component_clause,[],[f444])).
% 23.33/3.31  fof(f1071,plain,(
% 23.33/3.31    ( ! [X12,X10,X11] : (k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12)))) ) | ~spl2_44),
% 23.33/3.31    inference(avatar_component_clause,[],[f1070])).
% 23.33/3.31  fof(f2644,plain,(
% 23.33/3.31    spl2_67 | ~spl2_31 | ~spl2_33),
% 23.33/3.31    inference(avatar_split_clause,[],[f546,f517,f440,f2642])).
% 23.33/3.31  fof(f440,plain,(
% 23.33/3.31    spl2_31 <=> ! [X5,X6] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 23.33/3.31  fof(f546,plain,(
% 23.33/3.31    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | (~spl2_31 | ~spl2_33)),
% 23.33/3.31    inference(superposition,[],[f441,f518])).
% 23.33/3.31  fof(f441,plain,(
% 23.33/3.31    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) ) | ~spl2_31),
% 23.33/3.31    inference(avatar_component_clause,[],[f440])).
% 23.33/3.31  fof(f2108,plain,(
% 23.33/3.31    spl2_57),
% 23.33/3.31    inference(avatar_split_clause,[],[f37,f2106])).
% 23.33/3.31  fof(f37,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 23.33/3.31    inference(definition_unfolding,[],[f28,f21,f21])).
% 23.33/3.31  fof(f21,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.33/3.31    inference(cnf_transformation,[],[f11])).
% 23.33/3.31  fof(f11,axiom,(
% 23.33/3.31    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.33/3.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 23.33/3.31  fof(f28,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 23.33/3.31    inference(cnf_transformation,[],[f6])).
% 23.33/3.31  fof(f6,axiom,(
% 23.33/3.31    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 23.33/3.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 23.33/3.31  fof(f1791,plain,(
% 23.33/3.31    spl2_54 | ~spl2_7 | ~spl2_50),
% 23.33/3.31    inference(avatar_split_clause,[],[f1445,f1401,f95,f1789])).
% 23.33/3.31  fof(f95,plain,(
% 23.33/3.31    spl2_7 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 23.33/3.31  fof(f1445,plain,(
% 23.33/3.31    ( ! [X28,X26,X27] : (k4_xboole_0(X27,X28) = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))) ) | (~spl2_7 | ~spl2_50)),
% 23.33/3.31    inference(superposition,[],[f96,f1402])).
% 23.33/3.31  fof(f96,plain,(
% 23.33/3.31    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | ~spl2_7),
% 23.33/3.31    inference(avatar_component_clause,[],[f95])).
% 23.33/3.31  fof(f1403,plain,(
% 23.33/3.31    spl2_50 | ~spl2_7 | ~spl2_49),
% 23.33/3.31    inference(avatar_split_clause,[],[f1337,f1325,f95,f1401])).
% 23.33/3.31  fof(f1325,plain,(
% 23.33/3.31    spl2_49 <=> ! [X16,X15,X17] : k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,X16),X17)) = X16),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 23.33/3.31  fof(f1337,plain,(
% 23.33/3.31    ( ! [X28,X26,X27] : (k4_xboole_0(X27,X26) = k4_xboole_0(k4_xboole_0(X27,X26),k4_xboole_0(X26,X28))) ) | (~spl2_7 | ~spl2_49)),
% 23.33/3.31    inference(superposition,[],[f1326,f96])).
% 23.33/3.31  fof(f1326,plain,(
% 23.33/3.31    ( ! [X17,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,X16),X17)) = X16) ) | ~spl2_49),
% 23.33/3.31    inference(avatar_component_clause,[],[f1325])).
% 23.33/3.31  fof(f1327,plain,(
% 23.33/3.31    spl2_49 | ~spl2_22 | ~spl2_41 | ~spl2_47),
% 23.33/3.31    inference(avatar_split_clause,[],[f1279,f1202,f679,f306,f1325])).
% 23.33/3.31  fof(f306,plain,(
% 23.33/3.31    spl2_22 <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 23.33/3.31  fof(f1202,plain,(
% 23.33/3.31    spl2_47 <=> ! [X18,X17,X19] : k4_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19)))) = X19),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 23.33/3.31  fof(f1279,plain,(
% 23.33/3.31    ( ! [X17,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,X16),X17)) = X16) ) | (~spl2_22 | ~spl2_41 | ~spl2_47)),
% 23.33/3.31    inference(forward_demodulation,[],[f1229,f307])).
% 23.33/3.31  fof(f307,plain,(
% 23.33/3.31    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) ) | ~spl2_22),
% 23.33/3.31    inference(avatar_component_clause,[],[f306])).
% 23.33/3.31  fof(f1229,plain,(
% 23.33/3.31    ( ! [X17,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),X17),k1_xboole_0)) = X16) ) | (~spl2_41 | ~spl2_47)),
% 23.33/3.31    inference(superposition,[],[f1203,f680])).
% 23.33/3.31  fof(f1203,plain,(
% 23.33/3.31    ( ! [X19,X17,X18] : (k4_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19)))) = X19) ) | ~spl2_47),
% 23.33/3.31    inference(avatar_component_clause,[],[f1202])).
% 23.33/3.31  fof(f1204,plain,(
% 23.33/3.31    spl2_47 | ~spl2_7 | ~spl2_35),
% 23.33/3.31    inference(avatar_split_clause,[],[f1115,f525,f95,f1202])).
% 23.33/3.31  fof(f525,plain,(
% 23.33/3.31    spl2_35 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 23.33/3.31  fof(f1115,plain,(
% 23.33/3.31    ( ! [X19,X17,X18] : (k4_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19)))) = X19) ) | (~spl2_7 | ~spl2_35)),
% 23.33/3.31    inference(superposition,[],[f96,f526])).
% 23.33/3.31  fof(f526,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl2_35),
% 23.33/3.31    inference(avatar_component_clause,[],[f525])).
% 23.33/3.31  fof(f1080,plain,(
% 23.33/3.31    spl2_46 | ~spl2_3 | ~spl2_36),
% 23.33/3.31    inference(avatar_split_clause,[],[f646,f619,f49,f1078])).
% 23.33/3.31  fof(f49,plain,(
% 23.33/3.31    spl2_3 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 23.33/3.31  fof(f646,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl2_3 | ~spl2_36)),
% 23.33/3.31    inference(superposition,[],[f620,f50])).
% 23.33/3.31  fof(f50,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_3),
% 23.33/3.31    inference(avatar_component_clause,[],[f49])).
% 23.33/3.31  fof(f1072,plain,(
% 23.33/3.31    spl2_44 | ~spl2_2 | ~spl2_29),
% 23.33/3.31    inference(avatar_split_clause,[],[f418,f409,f45,f1070])).
% 23.33/3.31  fof(f409,plain,(
% 23.33/3.31    spl2_29 <=> ! [X1,X2] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 23.33/3.31  fof(f418,plain,(
% 23.33/3.31    ( ! [X12,X10,X11] : (k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12)))) ) | (~spl2_2 | ~spl2_29)),
% 23.33/3.31    inference(superposition,[],[f410,f46])).
% 23.33/3.31  fof(f410,plain,(
% 23.33/3.31    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) ) | ~spl2_29),
% 23.33/3.31    inference(avatar_component_clause,[],[f409])).
% 23.33/3.31  fof(f681,plain,(
% 23.33/3.31    spl2_41 | ~spl2_4 | ~spl2_24 | ~spl2_33 | ~spl2_36),
% 23.33/3.31    inference(avatar_split_clause,[],[f667,f619,f517,f314,f53,f679])).
% 23.33/3.31  fof(f53,plain,(
% 23.33/3.31    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 23.33/3.31  fof(f314,plain,(
% 23.33/3.31    spl2_24 <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)),
% 23.33/3.31    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 23.33/3.31  fof(f667,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) ) | (~spl2_4 | ~spl2_24 | ~spl2_33 | ~spl2_36)),
% 23.33/3.31    inference(forward_demodulation,[],[f664,f315])).
% 23.33/3.31  fof(f315,plain,(
% 23.33/3.31    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | ~spl2_24),
% 23.33/3.31    inference(avatar_component_clause,[],[f314])).
% 23.33/3.31  fof(f664,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) ) | (~spl2_4 | ~spl2_33 | ~spl2_36)),
% 23.33/3.31    inference(backward_demodulation,[],[f531,f662])).
% 23.33/3.31  fof(f662,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ) | (~spl2_4 | ~spl2_33 | ~spl2_36)),
% 23.33/3.31    inference(forward_demodulation,[],[f641,f518])).
% 23.33/3.31  fof(f641,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))) = k5_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ) | (~spl2_4 | ~spl2_36)),
% 23.33/3.31    inference(superposition,[],[f620,f54])).
% 23.33/3.31  fof(f54,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_4),
% 23.33/3.31    inference(avatar_component_clause,[],[f53])).
% 23.33/3.31  fof(f531,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))))) ) | (~spl2_4 | ~spl2_33)),
% 23.33/3.31    inference(superposition,[],[f518,f54])).
% 23.33/3.31  fof(f637,plain,(
% 23.33/3.31    spl2_40 | ~spl2_26 | ~spl2_34),
% 23.33/3.31    inference(avatar_split_clause,[],[f588,f521,f347,f635])).
% 23.33/3.31  fof(f588,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5)) ) | (~spl2_26 | ~spl2_34)),
% 23.33/3.31    inference(superposition,[],[f348,f522])).
% 23.33/3.31  fof(f633,plain,(
% 23.33/3.31    spl2_39 | ~spl2_26 | ~spl2_33),
% 23.33/3.31    inference(avatar_split_clause,[],[f543,f517,f347,f631])).
% 23.33/3.31  fof(f543,plain,(
% 23.33/3.31    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_26 | ~spl2_33)),
% 23.33/3.31    inference(superposition,[],[f348,f518])).
% 23.33/3.31  fof(f621,plain,(
% 23.33/3.31    spl2_36 | ~spl2_3 | ~spl2_26),
% 23.33/3.31    inference(avatar_split_clause,[],[f351,f347,f49,f619])).
% 23.33/3.31  fof(f351,plain,(
% 23.33/3.31    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl2_3 | ~spl2_26)),
% 23.33/3.31    inference(superposition,[],[f348,f50])).
% 23.33/3.31  fof(f527,plain,(
% 23.33/3.31    spl2_35),
% 23.33/3.31    inference(avatar_split_clause,[],[f35,f525])).
% 23.33/3.31  fof(f35,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 23.33/3.31    inference(definition_unfolding,[],[f26,f23,f23])).
% 23.33/3.31  fof(f23,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.33/3.31    inference(cnf_transformation,[],[f7])).
% 23.33/3.31  fof(f7,axiom,(
% 23.33/3.31    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.33/3.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 23.33/3.31  fof(f26,plain,(
% 23.33/3.31    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 23.33/3.31    inference(cnf_transformation,[],[f8])).
% 23.33/3.31  fof(f8,axiom,(
% 23.33/3.31    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 23.33/3.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 23.33/3.31  fof(f523,plain,(
% 23.33/3.31    spl2_34 | ~spl2_4 | ~spl2_11),
% 23.33/3.31    inference(avatar_split_clause,[],[f137,f134,f53,f521])).
% 23.33/3.31  fof(f137,plain,(
% 23.33/3.31    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) ) | (~spl2_4 | ~spl2_11)),
% 23.33/3.31    inference(superposition,[],[f135,f54])).
% 23.33/3.31  fof(f519,plain,(
% 23.33/3.31    spl2_33 | ~spl2_3 | ~spl2_4),
% 23.33/3.31    inference(avatar_split_clause,[],[f70,f53,f49,f517])).
% 23.33/3.32  fof(f70,plain,(
% 23.33/3.32    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ) | (~spl2_3 | ~spl2_4)),
% 23.33/3.32    inference(superposition,[],[f50,f54])).
% 23.33/3.32  fof(f446,plain,(
% 23.33/3.32    spl2_32 | ~spl2_26 | ~spl2_29),
% 23.33/3.32    inference(avatar_split_clause,[],[f423,f409,f347,f444])).
% 23.33/3.32  fof(f423,plain,(
% 23.33/3.32    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | (~spl2_26 | ~spl2_29)),
% 23.33/3.32    inference(superposition,[],[f348,f410])).
% 23.33/3.32  fof(f442,plain,(
% 23.33/3.32    spl2_31 | ~spl2_29),
% 23.33/3.32    inference(avatar_split_clause,[],[f415,f409,f440])).
% 23.33/3.32  fof(f415,plain,(
% 23.33/3.32    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) ) | ~spl2_29),
% 23.33/3.32    inference(superposition,[],[f410,f410])).
% 23.33/3.32  fof(f411,plain,(
% 23.33/3.32    spl2_29 | ~spl2_20 | ~spl2_26 | ~spl2_28),
% 23.33/3.32    inference(avatar_split_clause,[],[f401,f370,f347,f253,f409])).
% 23.33/3.32  fof(f370,plain,(
% 23.33/3.32    spl2_28 <=> ! [X1,X2] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 23.33/3.32  fof(f401,plain,(
% 23.33/3.32    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) ) | (~spl2_20 | ~spl2_26 | ~spl2_28)),
% 23.33/3.32    inference(forward_demodulation,[],[f389,f254])).
% 23.33/3.32  fof(f389,plain,(
% 23.33/3.32    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0)) ) | (~spl2_26 | ~spl2_28)),
% 23.33/3.32    inference(superposition,[],[f348,f371])).
% 23.33/3.32  fof(f371,plain,(
% 23.33/3.32    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ) | ~spl2_28),
% 23.33/3.32    inference(avatar_component_clause,[],[f370])).
% 23.33/3.32  fof(f372,plain,(
% 23.33/3.32    spl2_28 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21),
% 23.33/3.32    inference(avatar_split_clause,[],[f292,f265,f214,f210,f191,f134,f106,f95,f53,f49,f45,f41,f370])).
% 23.33/3.32  fof(f41,plain,(
% 23.33/3.32    spl2_1 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 23.33/3.32  fof(f106,plain,(
% 23.33/3.32    spl2_8 <=> ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 23.33/3.32  fof(f191,plain,(
% 23.33/3.32    spl2_17 <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 23.33/3.32  fof(f210,plain,(
% 23.33/3.32    spl2_18 <=> ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 23.33/3.32  fof(f214,plain,(
% 23.33/3.32    spl2_19 <=> ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 23.33/3.32  fof(f292,plain,(
% 23.33/3.32    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21)),
% 23.33/3.32    inference(backward_demodulation,[],[f109,f283])).
% 23.33/3.32  fof(f283,plain,(
% 23.33/3.32    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21)),
% 23.33/3.32    inference(backward_demodulation,[],[f244,f274])).
% 23.33/3.32  fof(f274,plain,(
% 23.33/3.32    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) ) | (~spl2_7 | ~spl2_21)),
% 23.33/3.32    inference(superposition,[],[f96,f266])).
% 23.33/3.32  fof(f244,plain,(
% 23.33/3.32    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19)),
% 23.33/3.32    inference(backward_demodulation,[],[f215,f238])).
% 23.33/3.32  fof(f238,plain,(
% 23.33/3.32    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_11 | ~spl2_17 | ~spl2_18)),
% 23.33/3.32    inference(backward_demodulation,[],[f207,f227])).
% 23.33/3.32  fof(f227,plain,(
% 23.33/3.32    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2))) ) | (~spl2_11 | ~spl2_18)),
% 23.33/3.32    inference(superposition,[],[f135,f211])).
% 23.33/3.32  fof(f211,plain,(
% 23.33/3.32    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl2_18),
% 23.33/3.32    inference(avatar_component_clause,[],[f210])).
% 23.33/3.32  fof(f207,plain,(
% 23.33/3.32    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_17)),
% 23.33/3.32    inference(backward_demodulation,[],[f69,f206])).
% 23.33/3.32  fof(f206,plain,(
% 23.33/3.32    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl2_3 | ~spl2_4 | ~spl2_17)),
% 23.33/3.32    inference(forward_demodulation,[],[f194,f70])).
% 23.33/3.32  fof(f194,plain,(
% 23.33/3.32    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) ) | (~spl2_4 | ~spl2_17)),
% 23.33/3.32    inference(superposition,[],[f192,f54])).
% 23.33/3.32  fof(f192,plain,(
% 23.33/3.32    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl2_17),
% 23.33/3.32    inference(avatar_component_clause,[],[f191])).
% 23.33/3.32  fof(f69,plain,(
% 23.33/3.32    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) ) | (~spl2_1 | ~spl2_4)),
% 23.33/3.32    inference(superposition,[],[f42,f54])).
% 23.33/3.32  fof(f42,plain,(
% 23.33/3.32    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) ) | ~spl2_1),
% 23.33/3.32    inference(avatar_component_clause,[],[f41])).
% 23.33/3.32  fof(f215,plain,(
% 23.33/3.32    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | ~spl2_19),
% 23.33/3.32    inference(avatar_component_clause,[],[f214])).
% 23.33/3.32  fof(f109,plain,(
% 23.33/3.32    ( ! [X2,X1] : (k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ) | (~spl2_2 | ~spl2_8)),
% 23.33/3.32    inference(superposition,[],[f107,f46])).
% 23.33/3.32  fof(f107,plain,(
% 23.33/3.32    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) ) | ~spl2_8),
% 23.33/3.32    inference(avatar_component_clause,[],[f106])).
% 23.33/3.32  fof(f349,plain,(
% 23.33/3.32    spl2_26 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_11 | ~spl2_13 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21),
% 23.33/3.32    inference(avatar_split_clause,[],[f295,f265,f214,f210,f191,f151,f134,f106,f95,f53,f49,f45,f41,f347])).
% 23.33/3.32  fof(f151,plain,(
% 23.33/3.32    spl2_13 <=> ! [X4] : k5_xboole_0(k4_xboole_0(X4,X4),X4) = X4),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 23.33/3.32  fof(f295,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_11 | ~spl2_13 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21)),
% 23.33/3.32    inference(forward_demodulation,[],[f289,f287])).
% 23.33/3.32  fof(f287,plain,(
% 23.33/3.32    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = X4) ) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_11 | ~spl2_13 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21)),
% 23.33/3.32    inference(backward_demodulation,[],[f152,f283])).
% 23.33/3.32  fof(f152,plain,(
% 23.33/3.32    ( ! [X4] : (k5_xboole_0(k4_xboole_0(X4,X4),X4) = X4) ) | ~spl2_13),
% 23.33/3.32    inference(avatar_component_clause,[],[f151])).
% 23.33/3.32  fof(f289,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21)),
% 23.33/3.32    inference(backward_demodulation,[],[f110,f283])).
% 23.33/3.32  fof(f110,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_8)),
% 23.33/3.32    inference(superposition,[],[f46,f107])).
% 23.33/3.32  fof(f339,plain,(
% 23.33/3.32    spl2_25 | ~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21),
% 23.33/3.32    inference(avatar_split_clause,[],[f283,f265,f214,f210,f191,f134,f95,f53,f49,f41,f337])).
% 23.33/3.32  fof(f316,plain,(
% 23.33/3.32    spl2_24 | ~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21),
% 23.33/3.32    inference(avatar_split_clause,[],[f290,f265,f214,f210,f191,f134,f106,f95,f53,f49,f41,f314])).
% 23.33/3.32  fof(f290,plain,(
% 23.33/3.32    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_11 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_21)),
% 23.33/3.32    inference(backward_demodulation,[],[f107,f283])).
% 23.33/3.32  fof(f308,plain,(
% 23.33/3.32    spl2_22 | ~spl2_7 | ~spl2_21),
% 23.33/3.32    inference(avatar_split_clause,[],[f274,f265,f95,f306])).
% 23.33/3.32  fof(f267,plain,(
% 23.33/3.32    spl2_21 | ~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_11 | ~spl2_17 | ~spl2_18),
% 23.33/3.32    inference(avatar_split_clause,[],[f238,f210,f191,f134,f53,f49,f41,f265])).
% 23.33/3.32  fof(f255,plain,(
% 23.33/3.32    spl2_20 | ~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_11 | ~spl2_17 | ~spl2_18),
% 23.33/3.32    inference(avatar_split_clause,[],[f239,f210,f191,f134,f53,f49,f41,f253])).
% 23.33/3.32  fof(f239,plain,(
% 23.33/3.32    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_11 | ~spl2_17 | ~spl2_18)),
% 23.33/3.32    inference(backward_demodulation,[],[f42,f238])).
% 23.33/3.32  fof(f216,plain,(
% 23.33/3.32    spl2_19 | ~spl2_3 | ~spl2_4 | ~spl2_17),
% 23.33/3.32    inference(avatar_split_clause,[],[f206,f191,f53,f49,f214])).
% 23.33/3.32  fof(f212,plain,(
% 23.33/3.32    spl2_18 | ~spl2_3 | ~spl2_17),
% 23.33/3.32    inference(avatar_split_clause,[],[f199,f191,f49,f210])).
% 23.33/3.32  fof(f199,plain,(
% 23.33/3.32    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | (~spl2_3 | ~spl2_17)),
% 23.33/3.32    inference(superposition,[],[f192,f50])).
% 23.33/3.32  fof(f193,plain,(
% 23.33/3.32    spl2_17 | ~spl2_3 | ~spl2_16),
% 23.33/3.32    inference(avatar_split_clause,[],[f185,f179,f49,f191])).
% 23.33/3.32  fof(f179,plain,(
% 23.33/3.32    spl2_16 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 23.33/3.32  fof(f185,plain,(
% 23.33/3.32    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | (~spl2_3 | ~spl2_16)),
% 23.33/3.32    inference(superposition,[],[f180,f50])).
% 23.33/3.32  fof(f180,plain,(
% 23.33/3.32    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | ~spl2_16),
% 23.33/3.32    inference(avatar_component_clause,[],[f179])).
% 23.33/3.32  fof(f181,plain,(
% 23.33/3.32    spl2_16 | ~spl2_2 | ~spl2_15),
% 23.33/3.32    inference(avatar_split_clause,[],[f176,f171,f45,f179])).
% 23.33/3.32  fof(f171,plain,(
% 23.33/3.32    spl2_15 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 23.33/3.32  fof(f176,plain,(
% 23.33/3.32    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | (~spl2_2 | ~spl2_15)),
% 23.33/3.32    inference(superposition,[],[f46,f173])).
% 23.33/3.32  fof(f173,plain,(
% 23.33/3.32    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_15),
% 23.33/3.32    inference(avatar_component_clause,[],[f171])).
% 23.33/3.32  fof(f174,plain,(
% 23.33/3.32    spl2_15 | ~spl2_1 | ~spl2_14),
% 23.33/3.32    inference(avatar_split_clause,[],[f162,f158,f41,f171])).
% 23.33/3.32  fof(f158,plain,(
% 23.33/3.32    spl2_14 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 23.33/3.32  fof(f162,plain,(
% 23.33/3.32    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl2_1 | ~spl2_14)),
% 23.33/3.32    inference(superposition,[],[f42,f160])).
% 23.33/3.32  fof(f160,plain,(
% 23.33/3.32    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_14),
% 23.33/3.32    inference(avatar_component_clause,[],[f158])).
% 23.33/3.32  fof(f161,plain,(
% 23.33/3.32    spl2_14 | ~spl2_10 | ~spl2_13),
% 23.33/3.32    inference(avatar_split_clause,[],[f154,f151,f118,f158])).
% 23.33/3.32  fof(f118,plain,(
% 23.33/3.32    spl2_10 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 23.33/3.32  fof(f154,plain,(
% 23.33/3.32    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl2_10 | ~spl2_13)),
% 23.33/3.32    inference(superposition,[],[f152,f119])).
% 23.33/3.32  fof(f119,plain,(
% 23.33/3.32    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)) ) | ~spl2_10),
% 23.33/3.32    inference(avatar_component_clause,[],[f118])).
% 23.33/3.32  fof(f153,plain,(
% 23.33/3.32    spl2_13 | ~spl2_7 | ~spl2_11),
% 23.33/3.32    inference(avatar_split_clause,[],[f142,f134,f95,f151])).
% 23.33/3.32  fof(f142,plain,(
% 23.33/3.32    ( ! [X4] : (k5_xboole_0(k4_xboole_0(X4,X4),X4) = X4) ) | (~spl2_7 | ~spl2_11)),
% 23.33/3.32    inference(superposition,[],[f135,f96])).
% 23.33/3.32  fof(f149,plain,(
% 23.33/3.32    ~spl2_12),
% 23.33/3.32    inference(avatar_split_clause,[],[f30,f146])).
% 23.33/3.32  fof(f30,plain,(
% 23.33/3.32    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 23.33/3.32    inference(definition_unfolding,[],[f17,f21,f23])).
% 23.33/3.32  fof(f17,plain,(
% 23.33/3.32    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 23.33/3.32    inference(cnf_transformation,[],[f16])).
% 23.33/3.32  fof(f16,plain,(
% 23.33/3.32    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 23.33/3.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 23.33/3.32  fof(f15,plain,(
% 23.33/3.32    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 23.33/3.32    introduced(choice_axiom,[])).
% 23.33/3.32  fof(f14,plain,(
% 23.33/3.32    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.33/3.32    inference(ennf_transformation,[],[f13])).
% 23.33/3.32  fof(f13,negated_conjecture,(
% 23.33/3.32    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.33/3.32    inference(negated_conjecture,[],[f12])).
% 23.33/3.32  fof(f12,conjecture,(
% 23.33/3.32    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.33/3.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 23.33/3.32  fof(f136,plain,(
% 23.33/3.32    spl2_11 | ~spl2_3 | ~spl2_5),
% 23.33/3.32    inference(avatar_split_clause,[],[f83,f57,f49,f134])).
% 23.33/3.32  fof(f57,plain,(
% 23.33/3.32    spl2_5 <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0),
% 23.33/3.32    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 23.33/3.32  fof(f83,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | (~spl2_3 | ~spl2_5)),
% 23.33/3.32    inference(backward_demodulation,[],[f34,f77])).
% 23.33/3.32  fof(f77,plain,(
% 23.33/3.32    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | (~spl2_3 | ~spl2_5)),
% 23.33/3.32    inference(superposition,[],[f58,f50])).
% 23.33/3.32  fof(f58,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | ~spl2_5),
% 23.33/3.32    inference(avatar_component_clause,[],[f57])).
% 23.33/3.32  fof(f34,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 23.33/3.32    inference(definition_unfolding,[],[f24,f21,f23])).
% 23.33/3.32  fof(f24,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 23.33/3.32    inference(cnf_transformation,[],[f9])).
% 23.33/3.32  fof(f9,axiom,(
% 23.33/3.32    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 23.33/3.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 23.33/3.32  fof(f120,plain,(
% 23.33/3.32    spl2_10 | ~spl2_1 | ~spl2_7),
% 23.33/3.32    inference(avatar_split_clause,[],[f101,f95,f41,f118])).
% 23.33/3.32  fof(f101,plain,(
% 23.33/3.32    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)) ) | (~spl2_1 | ~spl2_7)),
% 23.33/3.32    inference(superposition,[],[f42,f96])).
% 23.33/3.32  fof(f116,plain,(
% 23.33/3.32    spl2_9 | ~spl2_7),
% 23.33/3.32    inference(avatar_split_clause,[],[f100,f95,f114])).
% 23.33/3.32  fof(f100,plain,(
% 23.33/3.32    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) ) | ~spl2_7),
% 23.33/3.32    inference(superposition,[],[f96,f96])).
% 23.33/3.32  fof(f108,plain,(
% 23.33/3.32    spl2_8 | ~spl2_3 | ~spl2_7),
% 23.33/3.32    inference(avatar_split_clause,[],[f102,f95,f49,f106])).
% 23.33/3.32  fof(f102,plain,(
% 23.33/3.32    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) ) | (~spl2_3 | ~spl2_7)),
% 23.33/3.32    inference(superposition,[],[f50,f96])).
% 23.33/3.32  fof(f97,plain,(
% 23.33/3.32    spl2_7 | ~spl2_3 | ~spl2_5),
% 23.33/3.32    inference(avatar_split_clause,[],[f77,f57,f49,f95])).
% 23.33/3.32  fof(f59,plain,(
% 23.33/3.32    spl2_5),
% 23.33/3.32    inference(avatar_split_clause,[],[f38,f57])).
% 23.33/3.32  fof(f38,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 23.33/3.32    inference(backward_demodulation,[],[f33,f35])).
% 23.33/3.32  fof(f33,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 23.33/3.32    inference(definition_unfolding,[],[f20,f21,f23])).
% 23.33/3.32  fof(f20,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 23.33/3.32    inference(cnf_transformation,[],[f5])).
% 23.33/3.32  fof(f5,axiom,(
% 23.33/3.32    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 23.33/3.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 23.33/3.32  fof(f55,plain,(
% 23.33/3.32    spl2_4),
% 23.33/3.32    inference(avatar_split_clause,[],[f32,f53])).
% 23.33/3.32  fof(f32,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.33/3.32    inference(definition_unfolding,[],[f19,f23,f23])).
% 23.33/3.32  fof(f19,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.33/3.32    inference(cnf_transformation,[],[f1])).
% 23.33/3.32  fof(f1,axiom,(
% 23.33/3.32    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.33/3.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 23.33/3.32  fof(f51,plain,(
% 23.33/3.32    spl2_3),
% 23.33/3.32    inference(avatar_split_clause,[],[f29,f49])).
% 23.33/3.32  fof(f29,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.33/3.32    inference(definition_unfolding,[],[f22,f23])).
% 23.33/3.32  fof(f22,plain,(
% 23.33/3.32    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.33/3.32    inference(cnf_transformation,[],[f2])).
% 23.33/3.32  fof(f2,axiom,(
% 23.33/3.32    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.33/3.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 23.33/3.32  fof(f47,plain,(
% 23.33/3.32    spl2_2),
% 23.33/3.32    inference(avatar_split_clause,[],[f25,f45])).
% 23.33/3.32  fof(f25,plain,(
% 23.33/3.32    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 23.33/3.32    inference(cnf_transformation,[],[f10])).
% 23.33/3.32  fof(f10,axiom,(
% 23.33/3.32    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 23.33/3.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 23.33/3.32  fof(f43,plain,(
% 23.33/3.32    spl2_1),
% 23.33/3.32    inference(avatar_split_clause,[],[f31,f41])).
% 23.33/3.32  fof(f31,plain,(
% 23.33/3.32    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 23.33/3.32    inference(definition_unfolding,[],[f18,f21])).
% 23.33/3.32  fof(f18,plain,(
% 23.33/3.32    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.33/3.32    inference(cnf_transformation,[],[f4])).
% 23.33/3.32  fof(f4,axiom,(
% 23.33/3.32    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 23.33/3.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 23.33/3.32  % SZS output end Proof for theBenchmark
% 23.33/3.32  % (24647)------------------------------
% 23.33/3.32  % (24647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.33/3.32  % (24647)Termination reason: Refutation
% 23.33/3.32  
% 23.33/3.32  % (24647)Memory used [KB]: 84305
% 23.33/3.32  % (24647)Time elapsed: 2.851 s
% 23.33/3.32  % (24647)------------------------------
% 23.33/3.32  % (24647)------------------------------
% 23.33/3.32  % (24639)Success in time 2.965 s
%------------------------------------------------------------------------------
