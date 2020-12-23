%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:53 EST 2020

% Result     : Theorem 4.66s
% Output     : Refutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  290 ( 723 expanded)
%              Number of leaves         :   62 ( 362 expanded)
%              Depth                    :   10
%              Number of atoms          :  838 (1715 expanded)
%              Number of equality atoms :  238 ( 671 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f57,f61,f84,f88,f104,f140,f161,f165,f169,f208,f235,f255,f275,f346,f414,f449,f465,f692,f830,f1106,f1160,f1164,f1246,f1383,f1500,f1590,f1594,f1874,f3205,f3209,f3838,f4139,f4241,f4253,f5096,f5104,f5112,f5128,f7624,f12510,f12804,f12816,f13995,f14007,f14802,f18761,f20134])).

fof(f20134,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_43
    | spl2_134
    | ~ spl2_138 ),
    inference(avatar_contradiction_clause,[],[f20133])).

fof(f20133,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_43
    | spl2_134
    | ~ spl2_138 ),
    inference(subsumption_resolution,[],[f20132,f1589])).

fof(f1589,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3)
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f1588])).

fof(f1588,plain,
    ( spl2_43
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f20132,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | spl2_134
    | ~ spl2_138 ),
    inference(forward_demodulation,[],[f20131,f254])).

fof(f254,plain,
    ( ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl2_17
  <=> ! [X5,X4] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f20131,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | spl2_134
    | ~ spl2_138 ),
    inference(forward_demodulation,[],[f20130,f39])).

fof(f39,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f20130,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl2_3
    | spl2_134
    | ~ spl2_138 ),
    inference(forward_demodulation,[],[f20127,f43])).

fof(f43,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f20127,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_134
    | ~ spl2_138 ),
    inference(superposition,[],[f14801,f18760])).

fof(f18760,plain,
    ( ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X17,k2_xboole_0(X16,X18))
    | ~ spl2_138 ),
    inference(avatar_component_clause,[],[f18759])).

fof(f18759,plain,
    ( spl2_138
  <=> ! [X16,X18,X17] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X17,k2_xboole_0(X16,X18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).

fof(f14801,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_134 ),
    inference(avatar_component_clause,[],[f14799])).

fof(f14799,plain,
    ( spl2_134
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_134])])).

fof(f18761,plain,
    ( spl2_138
    | ~ spl2_41
    | ~ spl2_128
    | ~ spl2_131 ),
    inference(avatar_split_clause,[],[f15307,f14005,f13993,f1381,f18759])).

fof(f1381,plain,
    ( spl2_41
  <=> ! [X5,X6] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f13993,plain,
    ( spl2_128
  <=> ! [X100,X102,X101] : k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).

fof(f14005,plain,
    ( spl2_131
  <=> ! [X9,X7,X8] : k2_xboole_0(X9,X7) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).

fof(f15307,plain,
    ( ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X17,k2_xboole_0(X16,X18))
    | ~ spl2_41
    | ~ spl2_128
    | ~ spl2_131 ),
    inference(backward_demodulation,[],[f14259,f15132])).

fof(f15132,plain,
    ( ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X16,X17),k2_xboole_0(X16,X18)) = k2_xboole_0(X18,k2_xboole_0(X16,X17))
    | ~ spl2_41
    | ~ spl2_131 ),
    inference(superposition,[],[f14006,f1382])).

fof(f1382,plain,
    ( ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f1381])).

fof(f14006,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X9,X7) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))
    | ~ spl2_131 ),
    inference(avatar_component_clause,[],[f14005])).

fof(f14259,plain,
    ( ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(k2_xboole_0(X16,X18),k2_xboole_0(X16,X17))
    | ~ spl2_41
    | ~ spl2_128 ),
    inference(superposition,[],[f13994,f1382])).

fof(f13994,plain,
    ( ! [X101,X102,X100] : k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100)
    | ~ spl2_128 ),
    inference(avatar_component_clause,[],[f13993])).

fof(f14802,plain,
    ( ~ spl2_134
    | ~ spl2_5
    | ~ spl2_7
    | spl2_88
    | ~ spl2_123 ),
    inference(avatar_split_clause,[],[f13023,f12802,f5093,f82,f55,f14799])).

fof(f55,plain,
    ( spl2_5
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f82,plain,
    ( spl2_7
  <=> ! [X5,X6] : k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f5093,plain,
    ( spl2_88
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f12802,plain,
    ( spl2_123
  <=> ! [X9,X7,X8] : k2_xboole_0(X7,X9) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).

fof(f13023,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_5
    | ~ spl2_7
    | spl2_88
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f13021,f83])).

fof(f83,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f13021,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_5
    | spl2_88
    | ~ spl2_123 ),
    inference(backward_demodulation,[],[f5095,f13020])).

fof(f13020,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(X29,X27) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27)
    | ~ spl2_5
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f12909,f56])).

fof(f56,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f12909,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(k2_xboole_0(X27,X29),X27)
    | ~ spl2_5
    | ~ spl2_123 ),
    inference(superposition,[],[f56,f12803])).

fof(f12803,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X7,X9) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))
    | ~ spl2_123 ),
    inference(avatar_component_clause,[],[f12802])).

fof(f5095,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_88 ),
    inference(avatar_component_clause,[],[f5093])).

fof(f14007,plain,
    ( spl2_131
    | ~ spl2_5
    | ~ spl2_96
    | ~ spl2_122
    | ~ spl2_126 ),
    inference(avatar_split_clause,[],[f13873,f12814,f12508,f5126,f55,f14005])).

fof(f5126,plain,
    ( spl2_96
  <=> ! [X25,X23,X24] : k2_xboole_0(X25,X23) = k2_xboole_0(k4_xboole_0(X24,X24),k2_xboole_0(X23,X25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f12508,plain,
    ( spl2_122
  <=> ! [X89,X87,X88] : k2_xboole_0(X87,X89) = k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).

fof(f12814,plain,
    ( spl2_126
  <=> ! [X20,X19,X21] : k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).

fof(f13873,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X9,X7) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))
    | ~ spl2_5
    | ~ spl2_96
    | ~ spl2_122
    | ~ spl2_126 ),
    inference(forward_demodulation,[],[f13691,f12778])).

fof(f12778,plain,
    ( ! [X158,X159,X157] : k2_xboole_0(X158,X157) = k2_xboole_0(k4_xboole_0(X158,k4_xboole_0(X157,X159)),X157)
    | ~ spl2_96
    | ~ spl2_122 ),
    inference(forward_demodulation,[],[f12651,f5127])).

fof(f5127,plain,
    ( ! [X24,X23,X25] : k2_xboole_0(X25,X23) = k2_xboole_0(k4_xboole_0(X24,X24),k2_xboole_0(X23,X25))
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f5126])).

fof(f12651,plain,
    ( ! [X158,X159,X157,X160] : k2_xboole_0(k4_xboole_0(X158,k4_xboole_0(X157,X159)),X157) = k2_xboole_0(k4_xboole_0(X160,X160),k2_xboole_0(X157,X158))
    | ~ spl2_96
    | ~ spl2_122 ),
    inference(superposition,[],[f5127,f12509])).

fof(f12509,plain,
    ( ! [X88,X87,X89] : k2_xboole_0(X87,X89) = k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88)))
    | ~ spl2_122 ),
    inference(avatar_component_clause,[],[f12508])).

fof(f13691,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)) = k2_xboole_0(k4_xboole_0(X9,k4_xboole_0(X7,X8)),X7)
    | ~ spl2_5
    | ~ spl2_126 ),
    inference(superposition,[],[f12815,f56])).

fof(f12815,plain,
    ( ! [X21,X19,X20] : k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19)
    | ~ spl2_126 ),
    inference(avatar_component_clause,[],[f12814])).

fof(f13995,plain,
    ( spl2_128
    | ~ spl2_57
    | ~ spl2_92
    | ~ spl2_123 ),
    inference(avatar_split_clause,[],[f13039,f12802,f5110,f3203,f13993])).

fof(f3203,plain,
    ( spl2_57
  <=> ! [X42,X41] : k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,X41) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f5110,plain,
    ( spl2_92
  <=> ! [X20,X22,X21] : k2_xboole_0(X20,X22) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f13039,plain,
    ( ! [X101,X102,X100] : k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100)
    | ~ spl2_57
    | ~ spl2_92
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f12932,f5111])).

fof(f5111,plain,
    ( ! [X21,X22,X20] : k2_xboole_0(X20,X22) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21))
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f5110])).

fof(f12932,plain,
    ( ! [X101,X102,X100] : k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100) = k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,k2_xboole_0(k4_xboole_0(X100,X101),X102)))
    | ~ spl2_57
    | ~ spl2_123 ),
    inference(superposition,[],[f3204,f12803])).

fof(f3204,plain,
    ( ! [X41,X42] : k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,X41)
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f3203])).

fof(f12816,plain,
    ( spl2_126
    | ~ spl2_6
    | ~ spl2_116
    | ~ spl2_122 ),
    inference(avatar_split_clause,[],[f12751,f12508,f7622,f59,f12814])).

fof(f59,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f7622,plain,
    ( spl2_116
  <=> ! [X98,X97,X99] : k2_xboole_0(X99,X97) = k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).

fof(f12751,plain,
    ( ! [X21,X19,X20] : k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19)
    | ~ spl2_6
    | ~ spl2_116
    | ~ spl2_122 ),
    inference(forward_demodulation,[],[f12610,f7623])).

fof(f7623,plain,
    ( ! [X99,X97,X98] : k2_xboole_0(X99,X97) = k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97))
    | ~ spl2_116 ),
    inference(avatar_component_clause,[],[f7622])).

fof(f12610,plain,
    ( ! [X21,X19,X20] : k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),k2_xboole_0(X19,X20))
    | ~ spl2_6
    | ~ spl2_122 ),
    inference(superposition,[],[f60,f12509])).

fof(f60,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f12804,plain,
    ( spl2_123
    | ~ spl2_5
    | ~ spl2_122 ),
    inference(avatar_split_clause,[],[f12702,f12508,f55,f12802])).

fof(f12702,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X7,X9) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))
    | ~ spl2_5
    | ~ spl2_122 ),
    inference(forward_demodulation,[],[f12575,f12509])).

fof(f12575,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)) = k2_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X7,X8)))
    | ~ spl2_5
    | ~ spl2_122 ),
    inference(superposition,[],[f12509,f56])).

fof(f12510,plain,
    ( spl2_122
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f12312,f4137,f233,f42,f12508])).

fof(f233,plain,
    ( spl2_16
  <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f4137,plain,
    ( spl2_73
  <=> ! [X5,X7,X6] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f12312,plain,
    ( ! [X88,X87,X89] : k2_xboole_0(X87,X89) = k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88)))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f12158,f43])).

fof(f12158,plain,
    ( ! [X88,X87,X89] : k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88))) = k2_xboole_0(X87,k4_xboole_0(X89,X87))
    | ~ spl2_16
    | ~ spl2_73 ),
    inference(superposition,[],[f4138,f234])).

fof(f234,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f233])).

fof(f4138,plain,
    ( ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f4137])).

fof(f7624,plain,
    ( spl2_116
    | ~ spl2_37
    | ~ spl2_42
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f6029,f5102,f1498,f1158,f7622])).

fof(f1158,plain,
    ( spl2_37
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1498,plain,
    ( spl2_42
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f5102,plain,
    ( spl2_90
  <=> ! [X3,X2,X4] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X2,X4),k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f6029,plain,
    ( ! [X99,X97,X98] : k2_xboole_0(X99,X97) = k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97))
    | ~ spl2_37
    | ~ spl2_42
    | ~ spl2_90 ),
    inference(forward_demodulation,[],[f5954,f1159])).

fof(f1159,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f1158])).

fof(f5954,plain,
    ( ! [X99,X97,X98] : k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97)) = k2_xboole_0(k2_xboole_0(X99,X97),k4_xboole_0(X97,X97))
    | ~ spl2_42
    | ~ spl2_90 ),
    inference(superposition,[],[f1499,f5103])).

fof(f5103,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X2,X4),k2_xboole_0(X3,X2))
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f5102])).

fof(f1499,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f1498])).

fof(f5128,plain,
    ( spl2_96
    | ~ spl2_39
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f4896,f4251,f1244,f5126])).

fof(f1244,plain,
    ( spl2_39
  <=> ! [X23,X24] : k4_xboole_0(X23,X23) = k4_xboole_0(X24,X24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f4251,plain,
    ( spl2_77
  <=> ! [X5,X4] : k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f4896,plain,
    ( ! [X24,X23,X25] : k2_xboole_0(X25,X23) = k2_xboole_0(k4_xboole_0(X24,X24),k2_xboole_0(X23,X25))
    | ~ spl2_39
    | ~ spl2_77 ),
    inference(superposition,[],[f4252,f1245])).

fof(f1245,plain,
    ( ! [X24,X23] : k4_xboole_0(X23,X23) = k4_xboole_0(X24,X24)
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f1244])).

fof(f4252,plain,
    ( ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(X4,X5))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f4251])).

fof(f5112,plain,
    ( spl2_92
    | ~ spl2_3
    | ~ spl2_37
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f4405,f3836,f1158,f42,f5110])).

fof(f3836,plain,
    ( spl2_61
  <=> ! [X5,X7,X6] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f4405,plain,
    ( ! [X21,X22,X20] : k2_xboole_0(X20,X22) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21))
    | ~ spl2_3
    | ~ spl2_37
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f4331,f1159])).

fof(f4331,plain,
    ( ! [X21,X22,X20] : k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21)) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X20))
    | ~ spl2_3
    | ~ spl2_61 ),
    inference(superposition,[],[f43,f3837])).

fof(f3837,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f3836])).

fof(f5104,plain,
    ( spl2_90
    | ~ spl2_2
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f4290,f3836,f38,f5102])).

fof(f4290,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X2,X4),k2_xboole_0(X3,X2))
    | ~ spl2_2
    | ~ spl2_61 ),
    inference(superposition,[],[f3837,f39])).

fof(f5096,plain,
    ( ~ spl2_88
    | ~ spl2_12
    | spl2_46
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f4716,f4239,f1871,f159,f5093])).

fof(f159,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f1871,plain,
    ( spl2_46
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f4239,plain,
    ( spl2_74
  <=> ! [X9,X11,X10] : k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f4716,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_12
    | spl2_46
    | ~ spl2_74 ),
    inference(backward_demodulation,[],[f1873,f4621])).

fof(f4621,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,X9)))
    | ~ spl2_12
    | ~ spl2_74 ),
    inference(superposition,[],[f4240,f160])).

fof(f160,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f4240,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9))
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f4239])).

fof(f1873,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_46 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f4253,plain,
    ( spl2_77
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_27
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f3728,f3207,f463,f138,f59,f4251])).

fof(f138,plain,
    ( spl2_11
  <=> ! [X11,X12] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f463,plain,
    ( spl2_27
  <=> ! [X3,X2] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f3207,plain,
    ( spl2_58
  <=> ! [X44,X43] : k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,X43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f3728,plain,
    ( ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(X4,X5))
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_27
    | ~ spl2_58 ),
    inference(forward_demodulation,[],[f3727,f145])).

fof(f145,plain,
    ( ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X8,X7))
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f139,f60])).

fof(f139,plain,
    ( ! [X12,X11] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f3727,plain,
    ( ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4)))
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_27
    | ~ spl2_58 ),
    inference(forward_demodulation,[],[f3635,f145])).

fof(f3635,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4))) = k2_xboole_0(k2_xboole_0(X5,X4),k2_xboole_0(X4,X5))
    | ~ spl2_27
    | ~ spl2_58 ),
    inference(superposition,[],[f3208,f464])).

fof(f464,plain,
    ( ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f463])).

fof(f3208,plain,
    ( ! [X43,X44] : k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,X43)
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f3207])).

fof(f4241,plain,
    ( spl2_74
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f1036,f828,f447,f344,f273,f233,f159,f42,f4239])).

fof(f273,plain,
    ( spl2_19
  <=> ! [X7,X6] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f344,plain,
    ( spl2_21
  <=> ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f447,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f828,plain,
    ( spl2_31
  <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1036,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9))
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f1035,f234])).

fof(f1035,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X11),k4_xboole_0(X9,X10))
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f1034,f854])).

fof(f854,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0)))
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_21
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f853,f345])).

fof(f345,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f344])).

fof(f853,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0))))
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f852,f43])).

fof(f852,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))))
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f833,f160])).

fof(f833,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))))
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(superposition,[],[f829,f160])).

fof(f829,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f828])).

fof(f1034,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X11),k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,X9))))
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f975,f160])).

fof(f975,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X11),k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X9)))
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(superposition,[],[f448,f274])).

fof(f274,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f273])).

fof(f448,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f447])).

fof(f4139,plain,
    ( spl2_73
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f177,f159,f42,f4137])).

fof(f177,plain,
    ( ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(superposition,[],[f43,f160])).

fof(f3838,plain,
    ( spl2_61
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f306,f273,f159,f86,f59,f46,f3836])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f86,plain,
    ( spl2_8
  <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f306,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f305,f302])).

fof(f302,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f99,f297])).

fof(f297,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f291,f281])).

fof(f281,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1)
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(superposition,[],[f274,f160])).

fof(f291,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f290,f60])).

fof(f290,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1)))
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f276,f160])).

fof(f276,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_19 ),
    inference(superposition,[],[f274,f47])).

fof(f47,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f99,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f47,f87])).

fof(f87,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f305,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(X5,k2_xboole_0(X5,X7))
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f284,f160])).

fof(f284,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X5,X5),X7)
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(superposition,[],[f160,f274])).

fof(f3209,plain,
    ( spl2_58
    | ~ spl2_3
    | ~ spl2_43
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f1787,f1592,f1588,f42,f3207])).

fof(f1592,plain,
    ( spl2_44
  <=> ! [X1,X2] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1787,plain,
    ( ! [X43,X44] : k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,X43)
    | ~ spl2_3
    | ~ spl2_43
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f1742,f43])).

fof(f1742,plain,
    ( ! [X43,X44] : k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,k4_xboole_0(X43,X44))
    | ~ spl2_43
    | ~ spl2_44 ),
    inference(superposition,[],[f1589,f1593])).

fof(f1593,plain,
    ( ! [X2,X1] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f1592])).

fof(f3205,plain,
    ( spl2_57
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_42
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f1786,f1592,f1498,f42,f38,f3203])).

fof(f1786,plain,
    ( ! [X41,X42] : k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,X41)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_42
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f1785,f43])).

fof(f1785,plain,
    ( ! [X41,X42] : k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,k4_xboole_0(X41,X42))
    | ~ spl2_2
    | ~ spl2_42
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f1741,f39])).

fof(f1741,plain,
    ( ! [X41,X42] : k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(k4_xboole_0(X41,X42),X42)
    | ~ spl2_42
    | ~ spl2_44 ),
    inference(superposition,[],[f1499,f1593])).

fof(f1874,plain,
    ( ~ spl2_46
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f1069,f828,f447,f253,f55,f46,f42,f38,f1871])).

fof(f1069,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f68,f1064])).

fof(f1064,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X3,X4),X5))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f1061,f39])).

fof(f1061,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),X3)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f1033,f1055])).

fof(f1055,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f1054,f254])).

fof(f1054,plain,
    ( ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k4_xboole_0(X11,X10))
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f987,f39])).

fof(f987,plain,
    ( ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,X11),X10) = k4_xboole_0(X10,k4_xboole_0(X11,X10))
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(superposition,[],[f448,f829])).

fof(f1033,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(X3,k4_xboole_0(X4,X3)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f973,f51])).

fof(f51,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f47,f43])).

fof(f973,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X4,X3)))
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(superposition,[],[f448,f56])).

fof(f68,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f32,f67])).

fof(f67,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f65,f43])).

fof(f65,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f43,f56])).

fof(f32,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f28,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f17,f25,f25,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f1594,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f1385,f1381,f38,f1592])).

fof(f1385,plain,
    ( ! [X2,X1] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1
    | ~ spl2_2
    | ~ spl2_41 ),
    inference(superposition,[],[f1382,f39])).

fof(f1590,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f1060,f828,f447,f412,f253,f55,f46,f42,f38,f1588])).

fof(f412,plain,
    ( spl2_22
  <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f1060,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f436,f1055])).

fof(f436,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f416,f51])).

fof(f416,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)))
    | ~ spl2_5
    | ~ spl2_22 ),
    inference(superposition,[],[f413,f56])).

fof(f413,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f412])).

fof(f1500,plain,
    ( spl2_42
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_14
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f1443,f1381,f167,f46,f38,f1498])).

fof(f167,plain,
    ( spl2_14
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f1443,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_14
    | ~ spl2_41 ),
    inference(backward_demodulation,[],[f381,f1385])).

fof(f381,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f168,f47])).

fof(f168,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1383,plain,
    ( spl2_41
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f1056,f828,f447,f253,f46,f42,f38,f1381])).

fof(f1056,plain,
    ( ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f51,f1055])).

fof(f1246,plain,
    ( spl2_39
    | ~ spl2_37
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f1211,f1162,f1158,f1244])).

fof(f1162,plain,
    ( spl2_38
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f1211,plain,
    ( ! [X24,X23] : k4_xboole_0(X23,X23) = k4_xboole_0(X24,X24)
    | ~ spl2_37
    | ~ spl2_38 ),
    inference(superposition,[],[f1163,f1159])).

fof(f1163,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1164,plain,
    ( spl2_38
    | ~ spl2_5
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f1145,f1104,f55,f1162])).

fof(f1104,plain,
    ( spl2_36
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X3)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f1145,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3
    | ~ spl2_5
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f1113,f1105])).

fof(f1105,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X3)) = X2
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f1113,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X2,X2)) = k2_xboole_0(k4_xboole_0(X2,X2),X3)
    | ~ spl2_5
    | ~ spl2_36 ),
    inference(superposition,[],[f1105,f56])).

fof(f1160,plain,
    ( spl2_37
    | ~ spl2_4
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f1144,f1104,f46,f1158])).

fof(f1144,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0
    | ~ spl2_4
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f1112,f1105])).

fof(f1112,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X1))
    | ~ spl2_4
    | ~ spl2_36 ),
    inference(superposition,[],[f1105,f47])).

fof(f1106,plain,
    ( spl2_36
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f989,f447,f412,f1104])).

fof(f989,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X3)) = X2
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(superposition,[],[f448,f413])).

fof(f830,plain,
    ( spl2_31
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f782,f690,f412,f828])).

fof(f690,plain,
    ( spl2_29
  <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f782,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(superposition,[],[f691,f413])).

fof(f691,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X5))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f690])).

fof(f692,plain,
    ( spl2_29
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f298,f273,f206,f159,f82,f42,f690])).

fof(f206,plain,
    ( spl2_15
  <=> ! [X5,X6] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f298,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X5))
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f228,f281])).

fof(f228,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),k4_xboole_0(X4,X5))
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f227,f43])).

fof(f227,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5))
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f211,f160])).

fof(f211,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5))
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(superposition,[],[f207,f83])).

fof(f207,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f206])).

fof(f465,plain,
    ( spl2_27
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f301,f273,f159,f59,f46,f463])).

fof(f301,plain,
    ( ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f75,f281])).

fof(f75,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f47,f60])).

fof(f449,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f31,f447])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f27,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f414,plain,
    ( spl2_22
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f380,f167,f163,f412])).

fof(f163,plain,
    ( spl2_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f380,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f168,f164])).

fof(f164,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f346,plain,
    ( spl2_21
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f281,f273,f159,f344])).

fof(f275,plain,
    ( spl2_19
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f245,f233,f46,f273])).

fof(f245,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(superposition,[],[f47,f234])).

fof(f255,plain,
    ( spl2_17
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f241,f233,f38,f253])).

fof(f241,plain,
    ( ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(superposition,[],[f234,f39])).

fof(f235,plain,
    ( spl2_16
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f215,f206,f163,f233])).

fof(f215,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(superposition,[],[f207,f164])).

fof(f208,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f202,f167,f163,f42,f206])).

fof(f202,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f192,f168])).

fof(f192,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6))
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(superposition,[],[f43,f164])).

fof(f169,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f30,f167])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f165,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f29,f163])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f161,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f26,f159])).

fof(f140,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f121,f102,f59,f34,f138])).

fof(f34,plain,
    ( spl2_1
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f102,plain,
    ( spl2_9
  <=> ! [X1,X2] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f121,plain,
    ( ! [X12,X11] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f119,f35])).

fof(f35,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f119,plain,
    ( ! [X12,X11] : k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X12,X11))
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f60,f103])).

fof(f103,plain,
    ( ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f93,f86,f38,f102])).

fof(f93,plain,
    ( ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f87,f39])).

fof(f88,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f67,f55,f42,f86])).

fof(f84,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f66,f55,f42,f82])).

fof(f66,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f64,f56])).

fof(f64,plain,
    ( ! [X6,X5] : k4_xboole_0(k4_xboole_0(X6,X5),X5) = k4_xboole_0(k2_xboole_0(X5,X6),X5)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f56,f43])).

fof(f61,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f53,f46,f42,f59])).

fof(f53,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f52,f43])).

fof(f52,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f43,f47])).

fof(f57,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f49,f46,f38,f55])).

fof(f49,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f47,f39])).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f36,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (5679)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (5693)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (5691)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (5682)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5685)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (5692)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (5684)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (5687)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (5678)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (5690)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (5686)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (5694)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (5683)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (5680)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (5681)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (5695)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (5689)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (5689)Refutation not found, incomplete strategy% (5689)------------------------------
% 0.21/0.51  % (5689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5689)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5689)Memory used [KB]: 10490
% 0.21/0.51  % (5689)Time elapsed: 0.098 s
% 0.21/0.51  % (5689)------------------------------
% 0.21/0.51  % (5689)------------------------------
% 0.21/0.53  % (5688)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.66/0.96  % (5685)Refutation found. Thanks to Tanya!
% 4.66/0.96  % SZS status Theorem for theBenchmark
% 4.66/0.96  % SZS output start Proof for theBenchmark
% 4.66/0.96  fof(f20135,plain,(
% 4.66/0.96    $false),
% 4.66/0.96    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f57,f61,f84,f88,f104,f140,f161,f165,f169,f208,f235,f255,f275,f346,f414,f449,f465,f692,f830,f1106,f1160,f1164,f1246,f1383,f1500,f1590,f1594,f1874,f3205,f3209,f3838,f4139,f4241,f4253,f5096,f5104,f5112,f5128,f7624,f12510,f12804,f12816,f13995,f14007,f14802,f18761,f20134])).
% 4.66/0.96  fof(f20134,plain,(
% 4.66/0.96    ~spl2_2 | ~spl2_3 | ~spl2_17 | ~spl2_43 | spl2_134 | ~spl2_138),
% 4.66/0.96    inference(avatar_contradiction_clause,[],[f20133])).
% 4.66/0.96  fof(f20133,plain,(
% 4.66/0.96    $false | (~spl2_2 | ~spl2_3 | ~spl2_17 | ~spl2_43 | spl2_134 | ~spl2_138)),
% 4.66/0.96    inference(subsumption_resolution,[],[f20132,f1589])).
% 4.66/0.96  fof(f1589,plain,(
% 4.66/0.96    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3)) ) | ~spl2_43),
% 4.66/0.96    inference(avatar_component_clause,[],[f1588])).
% 4.66/0.96  fof(f1588,plain,(
% 4.66/0.96    spl2_43 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 4.66/0.96  fof(f20132,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | (~spl2_2 | ~spl2_3 | ~spl2_17 | spl2_134 | ~spl2_138)),
% 4.66/0.96    inference(forward_demodulation,[],[f20131,f254])).
% 4.66/0.96  fof(f254,plain,(
% 4.66/0.96    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) ) | ~spl2_17),
% 4.66/0.96    inference(avatar_component_clause,[],[f253])).
% 4.66/0.96  fof(f253,plain,(
% 4.66/0.96    spl2_17 <=> ! [X5,X4] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 4.66/0.96  fof(f20131,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_2 | ~spl2_3 | spl2_134 | ~spl2_138)),
% 4.66/0.96    inference(forward_demodulation,[],[f20130,f39])).
% 4.66/0.96  fof(f39,plain,(
% 4.66/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_2),
% 4.66/0.96    inference(avatar_component_clause,[],[f38])).
% 4.66/0.96  fof(f38,plain,(
% 4.66/0.96    spl2_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 4.66/0.96  fof(f20130,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | (~spl2_3 | spl2_134 | ~spl2_138)),
% 4.66/0.96    inference(forward_demodulation,[],[f20127,f43])).
% 4.66/0.96  fof(f43,plain,(
% 4.66/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_3),
% 4.66/0.96    inference(avatar_component_clause,[],[f42])).
% 4.66/0.96  fof(f42,plain,(
% 4.66/0.96    spl2_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 4.66/0.96  fof(f20127,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | (spl2_134 | ~spl2_138)),
% 4.66/0.96    inference(superposition,[],[f14801,f18760])).
% 4.66/0.96  fof(f18760,plain,(
% 4.66/0.96    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X17,k2_xboole_0(X16,X18))) ) | ~spl2_138),
% 4.66/0.96    inference(avatar_component_clause,[],[f18759])).
% 4.66/0.96  fof(f18759,plain,(
% 4.66/0.96    spl2_138 <=> ! [X16,X18,X17] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X17,k2_xboole_0(X16,X18))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).
% 4.66/0.96  fof(f14801,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_134),
% 4.66/0.96    inference(avatar_component_clause,[],[f14799])).
% 4.66/0.96  fof(f14799,plain,(
% 4.66/0.96    spl2_134 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_134])])).
% 4.66/0.96  fof(f18761,plain,(
% 4.66/0.96    spl2_138 | ~spl2_41 | ~spl2_128 | ~spl2_131),
% 4.66/0.96    inference(avatar_split_clause,[],[f15307,f14005,f13993,f1381,f18759])).
% 4.66/0.96  fof(f1381,plain,(
% 4.66/0.96    spl2_41 <=> ! [X5,X6] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 4.66/0.96  fof(f13993,plain,(
% 4.66/0.96    spl2_128 <=> ! [X100,X102,X101] : k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).
% 4.66/0.96  fof(f14005,plain,(
% 4.66/0.96    spl2_131 <=> ! [X9,X7,X8] : k2_xboole_0(X9,X7) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).
% 4.66/0.96  fof(f15307,plain,(
% 4.66/0.96    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X17,k2_xboole_0(X16,X18))) ) | (~spl2_41 | ~spl2_128 | ~spl2_131)),
% 4.66/0.96    inference(backward_demodulation,[],[f14259,f15132])).
% 4.66/0.96  fof(f15132,plain,(
% 4.66/0.96    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),k2_xboole_0(X16,X18)) = k2_xboole_0(X18,k2_xboole_0(X16,X17))) ) | (~spl2_41 | ~spl2_131)),
% 4.66/0.96    inference(superposition,[],[f14006,f1382])).
% 4.66/0.96  fof(f1382,plain,(
% 4.66/0.96    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5) ) | ~spl2_41),
% 4.66/0.96    inference(avatar_component_clause,[],[f1381])).
% 4.66/0.96  fof(f14006,plain,(
% 4.66/0.96    ( ! [X8,X7,X9] : (k2_xboole_0(X9,X7) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))) ) | ~spl2_131),
% 4.66/0.96    inference(avatar_component_clause,[],[f14005])).
% 4.66/0.96  fof(f14259,plain,(
% 4.66/0.96    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(k2_xboole_0(X16,X18),k2_xboole_0(X16,X17))) ) | (~spl2_41 | ~spl2_128)),
% 4.66/0.96    inference(superposition,[],[f13994,f1382])).
% 4.66/0.96  fof(f13994,plain,(
% 4.66/0.96    ( ! [X101,X102,X100] : (k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100)) ) | ~spl2_128),
% 4.66/0.96    inference(avatar_component_clause,[],[f13993])).
% 4.66/0.96  fof(f14802,plain,(
% 4.66/0.96    ~spl2_134 | ~spl2_5 | ~spl2_7 | spl2_88 | ~spl2_123),
% 4.66/0.96    inference(avatar_split_clause,[],[f13023,f12802,f5093,f82,f55,f14799])).
% 4.66/0.96  fof(f55,plain,(
% 4.66/0.96    spl2_5 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 4.66/0.96  fof(f82,plain,(
% 4.66/0.96    spl2_7 <=> ! [X5,X6] : k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 4.66/0.96  fof(f5093,plain,(
% 4.66/0.96    spl2_88 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 4.66/0.96  fof(f12802,plain,(
% 4.66/0.96    spl2_123 <=> ! [X9,X7,X8] : k2_xboole_0(X7,X9) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).
% 4.66/0.96  fof(f13023,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_5 | ~spl2_7 | spl2_88 | ~spl2_123)),
% 4.66/0.96    inference(forward_demodulation,[],[f13021,f83])).
% 4.66/0.96  fof(f83,plain,(
% 4.66/0.96    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)) ) | ~spl2_7),
% 4.66/0.96    inference(avatar_component_clause,[],[f82])).
% 4.66/0.96  fof(f13021,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_5 | spl2_88 | ~spl2_123)),
% 4.66/0.96    inference(backward_demodulation,[],[f5095,f13020])).
% 4.66/0.96  fof(f13020,plain,(
% 4.66/0.96    ( ! [X28,X29,X27] : (k4_xboole_0(X29,X27) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27)) ) | (~spl2_5 | ~spl2_123)),
% 4.66/0.96    inference(forward_demodulation,[],[f12909,f56])).
% 4.66/0.96  fof(f56,plain,(
% 4.66/0.96    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) ) | ~spl2_5),
% 4.66/0.96    inference(avatar_component_clause,[],[f55])).
% 4.66/0.96  fof(f12909,plain,(
% 4.66/0.96    ( ! [X28,X29,X27] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(k2_xboole_0(X27,X29),X27)) ) | (~spl2_5 | ~spl2_123)),
% 4.66/0.96    inference(superposition,[],[f56,f12803])).
% 4.66/0.96  fof(f12803,plain,(
% 4.66/0.96    ( ! [X8,X7,X9] : (k2_xboole_0(X7,X9) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))) ) | ~spl2_123),
% 4.66/0.96    inference(avatar_component_clause,[],[f12802])).
% 4.66/0.96  fof(f5095,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_88),
% 4.66/0.96    inference(avatar_component_clause,[],[f5093])).
% 4.66/0.96  fof(f14007,plain,(
% 4.66/0.96    spl2_131 | ~spl2_5 | ~spl2_96 | ~spl2_122 | ~spl2_126),
% 4.66/0.96    inference(avatar_split_clause,[],[f13873,f12814,f12508,f5126,f55,f14005])).
% 4.66/0.96  fof(f5126,plain,(
% 4.66/0.96    spl2_96 <=> ! [X25,X23,X24] : k2_xboole_0(X25,X23) = k2_xboole_0(k4_xboole_0(X24,X24),k2_xboole_0(X23,X25))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 4.66/0.96  fof(f12508,plain,(
% 4.66/0.96    spl2_122 <=> ! [X89,X87,X88] : k2_xboole_0(X87,X89) = k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88)))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).
% 4.66/0.96  fof(f12814,plain,(
% 4.66/0.96    spl2_126 <=> ! [X20,X19,X21] : k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).
% 4.66/0.96  fof(f13873,plain,(
% 4.66/0.96    ( ! [X8,X7,X9] : (k2_xboole_0(X9,X7) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))) ) | (~spl2_5 | ~spl2_96 | ~spl2_122 | ~spl2_126)),
% 4.66/0.96    inference(forward_demodulation,[],[f13691,f12778])).
% 4.66/0.96  fof(f12778,plain,(
% 4.66/0.96    ( ! [X158,X159,X157] : (k2_xboole_0(X158,X157) = k2_xboole_0(k4_xboole_0(X158,k4_xboole_0(X157,X159)),X157)) ) | (~spl2_96 | ~spl2_122)),
% 4.66/0.96    inference(forward_demodulation,[],[f12651,f5127])).
% 4.66/0.96  fof(f5127,plain,(
% 4.66/0.96    ( ! [X24,X23,X25] : (k2_xboole_0(X25,X23) = k2_xboole_0(k4_xboole_0(X24,X24),k2_xboole_0(X23,X25))) ) | ~spl2_96),
% 4.66/0.96    inference(avatar_component_clause,[],[f5126])).
% 4.66/0.96  fof(f12651,plain,(
% 4.66/0.96    ( ! [X158,X159,X157,X160] : (k2_xboole_0(k4_xboole_0(X158,k4_xboole_0(X157,X159)),X157) = k2_xboole_0(k4_xboole_0(X160,X160),k2_xboole_0(X157,X158))) ) | (~spl2_96 | ~spl2_122)),
% 4.66/0.96    inference(superposition,[],[f5127,f12509])).
% 4.66/0.96  fof(f12509,plain,(
% 4.66/0.96    ( ! [X88,X87,X89] : (k2_xboole_0(X87,X89) = k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88)))) ) | ~spl2_122),
% 4.66/0.96    inference(avatar_component_clause,[],[f12508])).
% 4.66/0.96  fof(f13691,plain,(
% 4.66/0.96    ( ! [X8,X7,X9] : (k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)) = k2_xboole_0(k4_xboole_0(X9,k4_xboole_0(X7,X8)),X7)) ) | (~spl2_5 | ~spl2_126)),
% 4.66/0.96    inference(superposition,[],[f12815,f56])).
% 4.66/0.96  fof(f12815,plain,(
% 4.66/0.96    ( ! [X21,X19,X20] : (k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19)) ) | ~spl2_126),
% 4.66/0.96    inference(avatar_component_clause,[],[f12814])).
% 4.66/0.96  fof(f13995,plain,(
% 4.66/0.96    spl2_128 | ~spl2_57 | ~spl2_92 | ~spl2_123),
% 4.66/0.96    inference(avatar_split_clause,[],[f13039,f12802,f5110,f3203,f13993])).
% 4.66/0.96  fof(f3203,plain,(
% 4.66/0.96    spl2_57 <=> ! [X42,X41] : k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,X41)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 4.66/0.96  fof(f5110,plain,(
% 4.66/0.96    spl2_92 <=> ! [X20,X22,X21] : k2_xboole_0(X20,X22) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 4.66/0.96  fof(f13039,plain,(
% 4.66/0.96    ( ! [X101,X102,X100] : (k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100)) ) | (~spl2_57 | ~spl2_92 | ~spl2_123)),
% 4.66/0.96    inference(forward_demodulation,[],[f12932,f5111])).
% 4.66/0.96  fof(f5111,plain,(
% 4.66/0.96    ( ! [X21,X22,X20] : (k2_xboole_0(X20,X22) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21))) ) | ~spl2_92),
% 4.66/0.96    inference(avatar_component_clause,[],[f5110])).
% 4.66/0.96  fof(f12932,plain,(
% 4.66/0.96    ( ! [X101,X102,X100] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(X100,X101),X102),X100) = k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,k2_xboole_0(k4_xboole_0(X100,X101),X102)))) ) | (~spl2_57 | ~spl2_123)),
% 4.66/0.96    inference(superposition,[],[f3204,f12803])).
% 4.66/0.96  fof(f3204,plain,(
% 4.66/0.96    ( ! [X41,X42] : (k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,X41)) ) | ~spl2_57),
% 4.66/0.96    inference(avatar_component_clause,[],[f3203])).
% 4.66/0.96  fof(f12816,plain,(
% 4.66/0.96    spl2_126 | ~spl2_6 | ~spl2_116 | ~spl2_122),
% 4.66/0.96    inference(avatar_split_clause,[],[f12751,f12508,f7622,f59,f12814])).
% 4.66/0.96  fof(f59,plain,(
% 4.66/0.96    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 4.66/0.96  fof(f7622,plain,(
% 4.66/0.96    spl2_116 <=> ! [X98,X97,X99] : k2_xboole_0(X99,X97) = k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).
% 4.66/0.96  fof(f12751,plain,(
% 4.66/0.96    ( ! [X21,X19,X20] : (k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19)) ) | (~spl2_6 | ~spl2_116 | ~spl2_122)),
% 4.66/0.96    inference(forward_demodulation,[],[f12610,f7623])).
% 4.66/0.96  fof(f7623,plain,(
% 4.66/0.96    ( ! [X99,X97,X98] : (k2_xboole_0(X99,X97) = k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97))) ) | ~spl2_116),
% 4.66/0.96    inference(avatar_component_clause,[],[f7622])).
% 4.66/0.96  fof(f12610,plain,(
% 4.66/0.96    ( ! [X21,X19,X20] : (k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),X19) = k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X19,X21)),k2_xboole_0(X19,X20))) ) | (~spl2_6 | ~spl2_122)),
% 4.66/0.96    inference(superposition,[],[f60,f12509])).
% 4.66/0.96  fof(f60,plain,(
% 4.66/0.96    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | ~spl2_6),
% 4.66/0.96    inference(avatar_component_clause,[],[f59])).
% 4.66/0.96  fof(f12804,plain,(
% 4.66/0.96    spl2_123 | ~spl2_5 | ~spl2_122),
% 4.66/0.96    inference(avatar_split_clause,[],[f12702,f12508,f55,f12802])).
% 4.66/0.96  fof(f12702,plain,(
% 4.66/0.96    ( ! [X8,X7,X9] : (k2_xboole_0(X7,X9) = k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))) ) | (~spl2_5 | ~spl2_122)),
% 4.66/0.96    inference(forward_demodulation,[],[f12575,f12509])).
% 4.66/0.96  fof(f12575,plain,(
% 4.66/0.96    ( ! [X8,X7,X9] : (k2_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)) = k2_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X7,X8)))) ) | (~spl2_5 | ~spl2_122)),
% 4.66/0.96    inference(superposition,[],[f12509,f56])).
% 4.66/0.96  fof(f12510,plain,(
% 4.66/0.96    spl2_122 | ~spl2_3 | ~spl2_16 | ~spl2_73),
% 4.66/0.96    inference(avatar_split_clause,[],[f12312,f4137,f233,f42,f12508])).
% 4.66/0.96  fof(f233,plain,(
% 4.66/0.96    spl2_16 <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 4.66/0.96  fof(f4137,plain,(
% 4.66/0.96    spl2_73 <=> ! [X5,X7,X6] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 4.66/0.96  fof(f12312,plain,(
% 4.66/0.96    ( ! [X88,X87,X89] : (k2_xboole_0(X87,X89) = k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88)))) ) | (~spl2_3 | ~spl2_16 | ~spl2_73)),
% 4.66/0.96    inference(forward_demodulation,[],[f12158,f43])).
% 4.66/0.96  fof(f12158,plain,(
% 4.66/0.96    ( ! [X88,X87,X89] : (k2_xboole_0(X87,k4_xboole_0(X89,k4_xboole_0(X87,X88))) = k2_xboole_0(X87,k4_xboole_0(X89,X87))) ) | (~spl2_16 | ~spl2_73)),
% 4.66/0.96    inference(superposition,[],[f4138,f234])).
% 4.66/0.96  fof(f234,plain,(
% 4.66/0.96    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) ) | ~spl2_16),
% 4.66/0.96    inference(avatar_component_clause,[],[f233])).
% 4.66/0.96  fof(f4138,plain,(
% 4.66/0.96    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | ~spl2_73),
% 4.66/0.96    inference(avatar_component_clause,[],[f4137])).
% 4.66/0.96  fof(f7624,plain,(
% 4.66/0.96    spl2_116 | ~spl2_37 | ~spl2_42 | ~spl2_90),
% 4.66/0.96    inference(avatar_split_clause,[],[f6029,f5102,f1498,f1158,f7622])).
% 4.66/0.96  fof(f1158,plain,(
% 4.66/0.96    spl2_37 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 4.66/0.96  fof(f1498,plain,(
% 4.66/0.96    spl2_42 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 4.66/0.96  fof(f5102,plain,(
% 4.66/0.96    spl2_90 <=> ! [X3,X2,X4] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X2,X4),k2_xboole_0(X3,X2))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 4.66/0.96  fof(f6029,plain,(
% 4.66/0.96    ( ! [X99,X97,X98] : (k2_xboole_0(X99,X97) = k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97))) ) | (~spl2_37 | ~spl2_42 | ~spl2_90)),
% 4.66/0.96    inference(forward_demodulation,[],[f5954,f1159])).
% 4.66/0.96  fof(f1159,plain,(
% 4.66/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0) ) | ~spl2_37),
% 4.66/0.96    inference(avatar_component_clause,[],[f1158])).
% 4.66/0.96  fof(f5954,plain,(
% 4.66/0.96    ( ! [X99,X97,X98] : (k2_xboole_0(k4_xboole_0(X97,X98),k2_xboole_0(X99,X97)) = k2_xboole_0(k2_xboole_0(X99,X97),k4_xboole_0(X97,X97))) ) | (~spl2_42 | ~spl2_90)),
% 4.66/0.96    inference(superposition,[],[f1499,f5103])).
% 4.66/0.96  fof(f5103,plain,(
% 4.66/0.96    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X2,X4),k2_xboole_0(X3,X2))) ) | ~spl2_90),
% 4.66/0.96    inference(avatar_component_clause,[],[f5102])).
% 4.66/0.96  fof(f1499,plain,(
% 4.66/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) ) | ~spl2_42),
% 4.66/0.96    inference(avatar_component_clause,[],[f1498])).
% 4.66/0.96  fof(f5128,plain,(
% 4.66/0.96    spl2_96 | ~spl2_39 | ~spl2_77),
% 4.66/0.96    inference(avatar_split_clause,[],[f4896,f4251,f1244,f5126])).
% 4.66/0.96  fof(f1244,plain,(
% 4.66/0.96    spl2_39 <=> ! [X23,X24] : k4_xboole_0(X23,X23) = k4_xboole_0(X24,X24)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 4.66/0.96  fof(f4251,plain,(
% 4.66/0.96    spl2_77 <=> ! [X5,X4] : k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(X4,X5))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 4.66/0.96  fof(f4896,plain,(
% 4.66/0.96    ( ! [X24,X23,X25] : (k2_xboole_0(X25,X23) = k2_xboole_0(k4_xboole_0(X24,X24),k2_xboole_0(X23,X25))) ) | (~spl2_39 | ~spl2_77)),
% 4.66/0.96    inference(superposition,[],[f4252,f1245])).
% 4.66/0.96  fof(f1245,plain,(
% 4.66/0.96    ( ! [X24,X23] : (k4_xboole_0(X23,X23) = k4_xboole_0(X24,X24)) ) | ~spl2_39),
% 4.66/0.96    inference(avatar_component_clause,[],[f1244])).
% 4.66/0.96  fof(f4252,plain,(
% 4.66/0.96    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(X4,X5))) ) | ~spl2_77),
% 4.66/0.96    inference(avatar_component_clause,[],[f4251])).
% 4.66/0.96  fof(f5112,plain,(
% 4.66/0.96    spl2_92 | ~spl2_3 | ~spl2_37 | ~spl2_61),
% 4.66/0.96    inference(avatar_split_clause,[],[f4405,f3836,f1158,f42,f5110])).
% 4.66/0.96  fof(f3836,plain,(
% 4.66/0.96    spl2_61 <=> ! [X5,X7,X6] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 4.66/0.96  fof(f4405,plain,(
% 4.66/0.96    ( ! [X21,X22,X20] : (k2_xboole_0(X20,X22) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21))) ) | (~spl2_3 | ~spl2_37 | ~spl2_61)),
% 4.66/0.96    inference(forward_demodulation,[],[f4331,f1159])).
% 4.66/0.96  fof(f4331,plain,(
% 4.66/0.96    ( ! [X21,X22,X20] : (k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X21)) = k2_xboole_0(k2_xboole_0(X20,X22),k4_xboole_0(X20,X20))) ) | (~spl2_3 | ~spl2_61)),
% 4.66/0.96    inference(superposition,[],[f43,f3837])).
% 4.66/0.96  fof(f3837,plain,(
% 4.66/0.96    ( ! [X6,X7,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7))) ) | ~spl2_61),
% 4.66/0.96    inference(avatar_component_clause,[],[f3836])).
% 4.66/0.96  fof(f5104,plain,(
% 4.66/0.96    spl2_90 | ~spl2_2 | ~spl2_61),
% 4.66/0.96    inference(avatar_split_clause,[],[f4290,f3836,f38,f5102])).
% 4.66/0.96  fof(f4290,plain,(
% 4.66/0.96    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X2,X4),k2_xboole_0(X3,X2))) ) | (~spl2_2 | ~spl2_61)),
% 4.66/0.96    inference(superposition,[],[f3837,f39])).
% 4.66/0.96  fof(f5096,plain,(
% 4.66/0.96    ~spl2_88 | ~spl2_12 | spl2_46 | ~spl2_74),
% 4.66/0.96    inference(avatar_split_clause,[],[f4716,f4239,f1871,f159,f5093])).
% 4.66/0.96  fof(f159,plain,(
% 4.66/0.96    spl2_12 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 4.66/0.96  fof(f1871,plain,(
% 4.66/0.96    spl2_46 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 4.66/0.96  fof(f4239,plain,(
% 4.66/0.96    spl2_74 <=> ! [X9,X11,X10] : k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9))),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 4.66/0.96  fof(f4716,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_12 | spl2_46 | ~spl2_74)),
% 4.66/0.96    inference(backward_demodulation,[],[f1873,f4621])).
% 4.66/0.96  fof(f4621,plain,(
% 4.66/0.96    ( ! [X10,X11,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,X9)))) ) | (~spl2_12 | ~spl2_74)),
% 4.66/0.96    inference(superposition,[],[f4240,f160])).
% 4.66/0.96  fof(f160,plain,(
% 4.66/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_12),
% 4.66/0.96    inference(avatar_component_clause,[],[f159])).
% 4.66/0.96  fof(f4240,plain,(
% 4.66/0.96    ( ! [X10,X11,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9))) ) | ~spl2_74),
% 4.66/0.96    inference(avatar_component_clause,[],[f4239])).
% 4.66/0.96  fof(f1873,plain,(
% 4.66/0.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_46),
% 4.66/0.96    inference(avatar_component_clause,[],[f1871])).
% 4.66/0.96  fof(f4253,plain,(
% 4.66/0.96    spl2_77 | ~spl2_6 | ~spl2_11 | ~spl2_27 | ~spl2_58),
% 4.66/0.96    inference(avatar_split_clause,[],[f3728,f3207,f463,f138,f59,f4251])).
% 4.66/0.96  fof(f138,plain,(
% 4.66/0.96    spl2_11 <=> ! [X11,X12] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)),
% 4.66/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 4.66/0.97  fof(f463,plain,(
% 4.66/0.97    spl2_27 <=> ! [X3,X2] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2)),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 4.66/0.97  fof(f3207,plain,(
% 4.66/0.97    spl2_58 <=> ! [X44,X43] : k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,X43)),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 4.66/0.97  fof(f3728,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(X4,X5))) ) | (~spl2_6 | ~spl2_11 | ~spl2_27 | ~spl2_58)),
% 4.66/0.97    inference(forward_demodulation,[],[f3727,f145])).
% 4.66/0.97  fof(f145,plain,(
% 4.66/0.97    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X8,X7))) ) | (~spl2_6 | ~spl2_11)),
% 4.66/0.97    inference(superposition,[],[f139,f60])).
% 4.66/0.97  fof(f139,plain,(
% 4.66/0.97    ( ! [X12,X11] : (k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)) ) | ~spl2_11),
% 4.66/0.97    inference(avatar_component_clause,[],[f138])).
% 4.66/0.97  fof(f3727,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4)))) ) | (~spl2_6 | ~spl2_11 | ~spl2_27 | ~spl2_58)),
% 4.66/0.97    inference(forward_demodulation,[],[f3635,f145])).
% 4.66/0.97  fof(f3635,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X4),k2_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4))) = k2_xboole_0(k2_xboole_0(X5,X4),k2_xboole_0(X4,X5))) ) | (~spl2_27 | ~spl2_58)),
% 4.66/0.97    inference(superposition,[],[f3208,f464])).
% 4.66/0.97  fof(f464,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2)) ) | ~spl2_27),
% 4.66/0.97    inference(avatar_component_clause,[],[f463])).
% 4.66/0.97  fof(f3208,plain,(
% 4.66/0.97    ( ! [X43,X44] : (k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,X43)) ) | ~spl2_58),
% 4.66/0.97    inference(avatar_component_clause,[],[f3207])).
% 4.66/0.97  fof(f4241,plain,(
% 4.66/0.97    spl2_74 | ~spl2_3 | ~spl2_12 | ~spl2_16 | ~spl2_19 | ~spl2_21 | ~spl2_23 | ~spl2_31),
% 4.66/0.97    inference(avatar_split_clause,[],[f1036,f828,f447,f344,f273,f233,f159,f42,f4239])).
% 4.66/0.97  fof(f273,plain,(
% 4.66/0.97    spl2_19 <=> ! [X7,X6] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 4.66/0.97  fof(f344,plain,(
% 4.66/0.97    spl2_21 <=> ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1)),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 4.66/0.97  fof(f447,plain,(
% 4.66/0.97    spl2_23 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 4.66/0.97  fof(f828,plain,(
% 4.66/0.97    spl2_31 <=> ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 4.66/0.97  fof(f1036,plain,(
% 4.66/0.97    ( ! [X10,X11,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9))) ) | (~spl2_3 | ~spl2_12 | ~spl2_16 | ~spl2_19 | ~spl2_21 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f1035,f234])).
% 4.66/0.97  fof(f1035,plain,(
% 4.66/0.97    ( ! [X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X11),k4_xboole_0(X9,X10))) ) | (~spl2_3 | ~spl2_12 | ~spl2_19 | ~spl2_21 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f1034,f854])).
% 4.66/0.97  fof(f854,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0)))) ) | (~spl2_3 | ~spl2_12 | ~spl2_21 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f853,f345])).
% 4.66/0.97  fof(f345,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1)) ) | ~spl2_21),
% 4.66/0.97    inference(avatar_component_clause,[],[f344])).
% 4.66/0.97  fof(f853,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0))))) ) | (~spl2_3 | ~spl2_12 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f852,f43])).
% 4.66/0.97  fof(f852,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))))) ) | (~spl2_12 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f833,f160])).
% 4.66/0.97  fof(f833,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))))) ) | (~spl2_12 | ~spl2_31)),
% 4.66/0.97    inference(superposition,[],[f829,f160])).
% 4.66/0.97  fof(f829,plain,(
% 4.66/0.97    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_31),
% 4.66/0.97    inference(avatar_component_clause,[],[f828])).
% 4.66/0.97  fof(f1034,plain,(
% 4.66/0.97    ( ! [X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X11),k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,X9))))) ) | (~spl2_12 | ~spl2_19 | ~spl2_23)),
% 4.66/0.97    inference(forward_demodulation,[],[f975,f160])).
% 4.66/0.97  fof(f975,plain,(
% 4.66/0.97    ( ! [X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X11,X9)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X11),k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X9)))) ) | (~spl2_19 | ~spl2_23)),
% 4.66/0.97    inference(superposition,[],[f448,f274])).
% 4.66/0.97  fof(f274,plain,(
% 4.66/0.97    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)) ) | ~spl2_19),
% 4.66/0.97    inference(avatar_component_clause,[],[f273])).
% 4.66/0.97  fof(f448,plain,(
% 4.66/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl2_23),
% 4.66/0.97    inference(avatar_component_clause,[],[f447])).
% 4.66/0.97  fof(f4139,plain,(
% 4.66/0.97    spl2_73 | ~spl2_3 | ~spl2_12),
% 4.66/0.97    inference(avatar_split_clause,[],[f177,f159,f42,f4137])).
% 4.66/0.97  fof(f177,plain,(
% 4.66/0.97    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | (~spl2_3 | ~spl2_12)),
% 4.66/0.97    inference(superposition,[],[f43,f160])).
% 4.66/0.97  fof(f3838,plain,(
% 4.66/0.97    spl2_61 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_12 | ~spl2_19),
% 4.66/0.97    inference(avatar_split_clause,[],[f306,f273,f159,f86,f59,f46,f3836])).
% 4.66/0.97  fof(f46,plain,(
% 4.66/0.97    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 4.66/0.97  fof(f86,plain,(
% 4.66/0.97    spl2_8 <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 4.66/0.97  fof(f306,plain,(
% 4.66/0.97    ( ! [X6,X7,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7))) ) | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(forward_demodulation,[],[f305,f302])).
% 4.66/0.97  fof(f302,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5)) ) | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(backward_demodulation,[],[f99,f297])).
% 4.66/0.97  fof(f297,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(backward_demodulation,[],[f291,f281])).
% 4.66/0.97  fof(f281,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1)) ) | (~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(superposition,[],[f274,f160])).
% 4.66/0.97  fof(f291,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(forward_demodulation,[],[f290,f60])).
% 4.66/0.97  fof(f290,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1)))) ) | (~spl2_4 | ~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(forward_demodulation,[],[f276,f160])).
% 4.66/0.97  fof(f276,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_19)),
% 4.66/0.97    inference(superposition,[],[f274,f47])).
% 4.66/0.97  fof(f47,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl2_4),
% 4.66/0.97    inference(avatar_component_clause,[],[f46])).
% 4.66/0.97  fof(f99,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) ) | (~spl2_4 | ~spl2_8)),
% 4.66/0.97    inference(superposition,[],[f47,f87])).
% 4.66/0.97  fof(f87,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) ) | ~spl2_8),
% 4.66/0.97    inference(avatar_component_clause,[],[f86])).
% 4.66/0.97  fof(f305,plain,(
% 4.66/0.97    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(X5,k2_xboole_0(X5,X7))) ) | (~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(forward_demodulation,[],[f284,f160])).
% 4.66/0.97  fof(f284,plain,(
% 4.66/0.97    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X5,X5),X7)) ) | (~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(superposition,[],[f160,f274])).
% 4.66/0.97  fof(f3209,plain,(
% 4.66/0.97    spl2_58 | ~spl2_3 | ~spl2_43 | ~spl2_44),
% 4.66/0.97    inference(avatar_split_clause,[],[f1787,f1592,f1588,f42,f3207])).
% 4.66/0.97  fof(f1592,plain,(
% 4.66/0.97    spl2_44 <=> ! [X1,X2] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 4.66/0.97  fof(f1787,plain,(
% 4.66/0.97    ( ! [X43,X44] : (k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,X43)) ) | (~spl2_3 | ~spl2_43 | ~spl2_44)),
% 4.66/0.97    inference(forward_demodulation,[],[f1742,f43])).
% 4.66/0.97  fof(f1742,plain,(
% 4.66/0.97    ( ! [X43,X44] : (k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X43,X44)) = k2_xboole_0(X44,k4_xboole_0(X43,X44))) ) | (~spl2_43 | ~spl2_44)),
% 4.66/0.97    inference(superposition,[],[f1589,f1593])).
% 4.66/0.97  fof(f1593,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1) ) | ~spl2_44),
% 4.66/0.97    inference(avatar_component_clause,[],[f1592])).
% 4.66/0.97  fof(f3205,plain,(
% 4.66/0.97    spl2_57 | ~spl2_2 | ~spl2_3 | ~spl2_42 | ~spl2_44),
% 4.66/0.97    inference(avatar_split_clause,[],[f1786,f1592,f1498,f42,f38,f3203])).
% 4.66/0.97  fof(f1786,plain,(
% 4.66/0.97    ( ! [X41,X42] : (k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,X41)) ) | (~spl2_2 | ~spl2_3 | ~spl2_42 | ~spl2_44)),
% 4.66/0.97    inference(forward_demodulation,[],[f1785,f43])).
% 4.66/0.97  fof(f1785,plain,(
% 4.66/0.97    ( ! [X41,X42] : (k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(X42,k4_xboole_0(X41,X42))) ) | (~spl2_2 | ~spl2_42 | ~spl2_44)),
% 4.66/0.97    inference(forward_demodulation,[],[f1741,f39])).
% 4.66/0.97  fof(f1741,plain,(
% 4.66/0.97    ( ! [X41,X42] : (k2_xboole_0(k2_xboole_0(X41,X42),k4_xboole_0(X41,X42)) = k2_xboole_0(k4_xboole_0(X41,X42),X42)) ) | (~spl2_42 | ~spl2_44)),
% 4.66/0.97    inference(superposition,[],[f1499,f1593])).
% 4.66/0.97  fof(f1874,plain,(
% 4.66/0.97    ~spl2_46 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_23 | ~spl2_31),
% 4.66/0.97    inference(avatar_split_clause,[],[f1069,f828,f447,f253,f55,f46,f42,f38,f1871])).
% 4.66/0.97  fof(f1069,plain,(
% 4.66/0.97    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(backward_demodulation,[],[f68,f1064])).
% 4.66/0.97  fof(f1064,plain,(
% 4.66/0.97    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X3,X4),X5))) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f1061,f39])).
% 4.66/0.97  fof(f1061,plain,(
% 4.66/0.97    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),X3)) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(backward_demodulation,[],[f1033,f1055])).
% 4.66/0.97  fof(f1055,plain,(
% 4.66/0.97    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10) ) | (~spl2_2 | ~spl2_17 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f1054,f254])).
% 4.66/0.97  fof(f1054,plain,(
% 4.66/0.97    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k4_xboole_0(X11,X10))) ) | (~spl2_2 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(forward_demodulation,[],[f987,f39])).
% 4.66/0.97  fof(f987,plain,(
% 4.66/0.97    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,X11),X10) = k4_xboole_0(X10,k4_xboole_0(X11,X10))) ) | (~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(superposition,[],[f448,f829])).
% 4.66/0.97  fof(f1033,plain,(
% 4.66/0.97    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(X3,k4_xboole_0(X4,X3)))) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_23)),
% 4.66/0.97    inference(forward_demodulation,[],[f973,f51])).
% 4.66/0.97  fof(f51,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) ) | (~spl2_3 | ~spl2_4)),
% 4.66/0.97    inference(superposition,[],[f47,f43])).
% 4.66/0.97  fof(f973,plain,(
% 4.66/0.97    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X4,X3)))) ) | (~spl2_5 | ~spl2_23)),
% 4.66/0.97    inference(superposition,[],[f448,f56])).
% 4.66/0.97  fof(f68,plain,(
% 4.66/0.97    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | (~spl2_3 | ~spl2_5)),
% 4.66/0.97    inference(backward_demodulation,[],[f32,f67])).
% 4.66/0.97  fof(f67,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) ) | (~spl2_3 | ~spl2_5)),
% 4.66/0.97    inference(forward_demodulation,[],[f65,f43])).
% 4.66/0.97  fof(f65,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) ) | (~spl2_3 | ~spl2_5)),
% 4.66/0.97    inference(superposition,[],[f43,f56])).
% 4.66/0.97  fof(f32,plain,(
% 4.66/0.97    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 4.66/0.97    inference(backward_demodulation,[],[f28,f26])).
% 4.66/0.97  fof(f26,plain,(
% 4.66/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.66/0.97    inference(cnf_transformation,[],[f6])).
% 4.66/0.97  fof(f6,axiom,(
% 4.66/0.97    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.66/0.97  fof(f28,plain,(
% 4.66/0.97    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 4.66/0.97    inference(definition_unfolding,[],[f17,f25,f25,f20])).
% 4.66/0.97  fof(f20,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.66/0.97    inference(cnf_transformation,[],[f8])).
% 4.66/0.97  fof(f8,axiom,(
% 4.66/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.66/0.97  fof(f25,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 4.66/0.97    inference(cnf_transformation,[],[f2])).
% 4.66/0.97  fof(f2,axiom,(
% 4.66/0.97    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 4.66/0.97  fof(f17,plain,(
% 4.66/0.97    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.66/0.97    inference(cnf_transformation,[],[f16])).
% 4.66/0.97  fof(f16,plain,(
% 4.66/0.97    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.66/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 4.66/0.97  fof(f15,plain,(
% 4.66/0.97    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.66/0.97    introduced(choice_axiom,[])).
% 4.66/0.97  fof(f14,plain,(
% 4.66/0.97    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.66/0.97    inference(ennf_transformation,[],[f12])).
% 4.66/0.97  fof(f12,negated_conjecture,(
% 4.66/0.97    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.66/0.97    inference(negated_conjecture,[],[f11])).
% 4.66/0.97  fof(f11,conjecture,(
% 4.66/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 4.66/0.97  fof(f1594,plain,(
% 4.66/0.97    spl2_44 | ~spl2_2 | ~spl2_41),
% 4.66/0.97    inference(avatar_split_clause,[],[f1385,f1381,f38,f1592])).
% 4.66/0.97  fof(f1385,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1) ) | (~spl2_2 | ~spl2_41)),
% 4.66/0.97    inference(superposition,[],[f1382,f39])).
% 4.66/0.97  fof(f1590,plain,(
% 4.66/0.97    spl2_43 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_22 | ~spl2_23 | ~spl2_31),
% 4.66/0.97    inference(avatar_split_clause,[],[f1060,f828,f447,f412,f253,f55,f46,f42,f38,f1588])).
% 4.66/0.97  fof(f412,plain,(
% 4.66/0.97    spl2_22 <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 4.66/0.97  fof(f1060,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3)) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_22 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(backward_demodulation,[],[f436,f1055])).
% 4.66/0.97  fof(f436,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2)))) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_22)),
% 4.66/0.97    inference(forward_demodulation,[],[f416,f51])).
% 4.66/0.97  fof(f416,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)))) ) | (~spl2_5 | ~spl2_22)),
% 4.66/0.97    inference(superposition,[],[f413,f56])).
% 4.66/0.97  fof(f413,plain,(
% 4.66/0.97    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3) ) | ~spl2_22),
% 4.66/0.97    inference(avatar_component_clause,[],[f412])).
% 4.66/0.97  fof(f1500,plain,(
% 4.66/0.97    spl2_42 | ~spl2_2 | ~spl2_4 | ~spl2_14 | ~spl2_41),
% 4.66/0.97    inference(avatar_split_clause,[],[f1443,f1381,f167,f46,f38,f1498])).
% 4.66/0.97  fof(f167,plain,(
% 4.66/0.97    spl2_14 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 4.66/0.97  fof(f1443,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_4 | ~spl2_14 | ~spl2_41)),
% 4.66/0.97    inference(backward_demodulation,[],[f381,f1385])).
% 4.66/0.97  fof(f381,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_14)),
% 4.66/0.97    inference(superposition,[],[f168,f47])).
% 4.66/0.97  fof(f168,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_14),
% 4.66/0.97    inference(avatar_component_clause,[],[f167])).
% 4.66/0.97  fof(f1383,plain,(
% 4.66/0.97    spl2_41 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_17 | ~spl2_23 | ~spl2_31),
% 4.66/0.97    inference(avatar_split_clause,[],[f1056,f828,f447,f253,f46,f42,f38,f1381])).
% 4.66/0.97  fof(f1056,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_17 | ~spl2_23 | ~spl2_31)),
% 4.66/0.97    inference(backward_demodulation,[],[f51,f1055])).
% 4.66/0.97  fof(f1246,plain,(
% 4.66/0.97    spl2_39 | ~spl2_37 | ~spl2_38),
% 4.66/0.97    inference(avatar_split_clause,[],[f1211,f1162,f1158,f1244])).
% 4.66/0.97  fof(f1162,plain,(
% 4.66/0.97    spl2_38 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 4.66/0.97  fof(f1211,plain,(
% 4.66/0.97    ( ! [X24,X23] : (k4_xboole_0(X23,X23) = k4_xboole_0(X24,X24)) ) | (~spl2_37 | ~spl2_38)),
% 4.66/0.97    inference(superposition,[],[f1163,f1159])).
% 4.66/0.97  fof(f1163,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3) ) | ~spl2_38),
% 4.66/0.97    inference(avatar_component_clause,[],[f1162])).
% 4.66/0.97  fof(f1164,plain,(
% 4.66/0.97    spl2_38 | ~spl2_5 | ~spl2_36),
% 4.66/0.97    inference(avatar_split_clause,[],[f1145,f1104,f55,f1162])).
% 4.66/0.97  fof(f1104,plain,(
% 4.66/0.97    spl2_36 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X3)) = X2),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 4.66/0.97  fof(f1145,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3) ) | (~spl2_5 | ~spl2_36)),
% 4.66/0.97    inference(forward_demodulation,[],[f1113,f1105])).
% 4.66/0.97  fof(f1105,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X3)) = X2) ) | ~spl2_36),
% 4.66/0.97    inference(avatar_component_clause,[],[f1104])).
% 4.66/0.97  fof(f1113,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X2,X2)) = k2_xboole_0(k4_xboole_0(X2,X2),X3)) ) | (~spl2_5 | ~spl2_36)),
% 4.66/0.97    inference(superposition,[],[f1105,f56])).
% 4.66/0.97  fof(f1160,plain,(
% 4.66/0.97    spl2_37 | ~spl2_4 | ~spl2_36),
% 4.66/0.97    inference(avatar_split_clause,[],[f1144,f1104,f46,f1158])).
% 4.66/0.97  fof(f1144,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0) ) | (~spl2_4 | ~spl2_36)),
% 4.66/0.97    inference(forward_demodulation,[],[f1112,f1105])).
% 4.66/0.97  fof(f1112,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X1))) ) | (~spl2_4 | ~spl2_36)),
% 4.66/0.97    inference(superposition,[],[f1105,f47])).
% 4.66/0.97  fof(f1106,plain,(
% 4.66/0.97    spl2_36 | ~spl2_22 | ~spl2_23),
% 4.66/0.97    inference(avatar_split_clause,[],[f989,f447,f412,f1104])).
% 4.66/0.97  fof(f989,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X3)) = X2) ) | (~spl2_22 | ~spl2_23)),
% 4.66/0.97    inference(superposition,[],[f448,f413])).
% 4.66/0.97  fof(f830,plain,(
% 4.66/0.97    spl2_31 | ~spl2_22 | ~spl2_29),
% 4.66/0.97    inference(avatar_split_clause,[],[f782,f690,f412,f828])).
% 4.66/0.97  fof(f690,plain,(
% 4.66/0.97    spl2_29 <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X5))),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 4.66/0.97  fof(f782,plain,(
% 4.66/0.97    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_22 | ~spl2_29)),
% 4.66/0.97    inference(superposition,[],[f691,f413])).
% 4.66/0.97  fof(f691,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X5))) ) | ~spl2_29),
% 4.66/0.97    inference(avatar_component_clause,[],[f690])).
% 4.66/0.97  fof(f692,plain,(
% 4.66/0.97    spl2_29 | ~spl2_3 | ~spl2_7 | ~spl2_12 | ~spl2_15 | ~spl2_19),
% 4.66/0.97    inference(avatar_split_clause,[],[f298,f273,f206,f159,f82,f42,f690])).
% 4.66/0.97  fof(f206,plain,(
% 4.66/0.97    spl2_15 <=> ! [X5,X6] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 4.66/0.97  fof(f298,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X5))) ) | (~spl2_3 | ~spl2_7 | ~spl2_12 | ~spl2_15 | ~spl2_19)),
% 4.66/0.97    inference(backward_demodulation,[],[f228,f281])).
% 4.66/0.97  fof(f228,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),k4_xboole_0(X4,X5))) ) | (~spl2_3 | ~spl2_7 | ~spl2_12 | ~spl2_15)),
% 4.66/0.97    inference(forward_demodulation,[],[f227,f43])).
% 4.66/0.97  fof(f227,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5))) ) | (~spl2_7 | ~spl2_12 | ~spl2_15)),
% 4.66/0.97    inference(forward_demodulation,[],[f211,f160])).
% 4.66/0.97  fof(f211,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5))) ) | (~spl2_7 | ~spl2_15)),
% 4.66/0.97    inference(superposition,[],[f207,f83])).
% 4.66/0.97  fof(f207,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5) ) | ~spl2_15),
% 4.66/0.97    inference(avatar_component_clause,[],[f206])).
% 4.66/0.97  fof(f465,plain,(
% 4.66/0.97    spl2_27 | ~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19),
% 4.66/0.97    inference(avatar_split_clause,[],[f301,f273,f159,f59,f46,f463])).
% 4.66/0.97  fof(f301,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2)) ) | (~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19)),
% 4.66/0.97    inference(backward_demodulation,[],[f75,f281])).
% 4.66/0.97  fof(f75,plain,(
% 4.66/0.97    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) ) | (~spl2_4 | ~spl2_6)),
% 4.66/0.97    inference(superposition,[],[f47,f60])).
% 4.66/0.97  fof(f449,plain,(
% 4.66/0.97    spl2_23),
% 4.66/0.97    inference(avatar_split_clause,[],[f31,f447])).
% 4.66/0.97  fof(f31,plain,(
% 4.66/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 4.66/0.97    inference(definition_unfolding,[],[f27,f20])).
% 4.66/0.97  fof(f27,plain,(
% 4.66/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 4.66/0.97    inference(cnf_transformation,[],[f10])).
% 4.66/0.97  fof(f10,axiom,(
% 4.66/0.97    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 4.66/0.97  fof(f414,plain,(
% 4.66/0.97    spl2_22 | ~spl2_13 | ~spl2_14),
% 4.66/0.97    inference(avatar_split_clause,[],[f380,f167,f163,f412])).
% 4.66/0.97  fof(f163,plain,(
% 4.66/0.97    spl2_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 4.66/0.97  fof(f380,plain,(
% 4.66/0.97    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3) ) | (~spl2_13 | ~spl2_14)),
% 4.66/0.97    inference(superposition,[],[f168,f164])).
% 4.66/0.97  fof(f164,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_13),
% 4.66/0.97    inference(avatar_component_clause,[],[f163])).
% 4.66/0.97  fof(f346,plain,(
% 4.66/0.97    spl2_21 | ~spl2_12 | ~spl2_19),
% 4.66/0.97    inference(avatar_split_clause,[],[f281,f273,f159,f344])).
% 4.66/0.97  fof(f275,plain,(
% 4.66/0.97    spl2_19 | ~spl2_4 | ~spl2_16),
% 4.66/0.97    inference(avatar_split_clause,[],[f245,f233,f46,f273])).
% 4.66/0.97  fof(f245,plain,(
% 4.66/0.97    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)) ) | (~spl2_4 | ~spl2_16)),
% 4.66/0.97    inference(superposition,[],[f47,f234])).
% 4.66/0.97  fof(f255,plain,(
% 4.66/0.97    spl2_17 | ~spl2_2 | ~spl2_16),
% 4.66/0.97    inference(avatar_split_clause,[],[f241,f233,f38,f253])).
% 4.66/0.97  fof(f241,plain,(
% 4.66/0.97    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) ) | (~spl2_2 | ~spl2_16)),
% 4.66/0.97    inference(superposition,[],[f234,f39])).
% 4.66/0.97  fof(f235,plain,(
% 4.66/0.97    spl2_16 | ~spl2_13 | ~spl2_15),
% 4.66/0.97    inference(avatar_split_clause,[],[f215,f206,f163,f233])).
% 4.66/0.97  fof(f215,plain,(
% 4.66/0.97    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) ) | (~spl2_13 | ~spl2_15)),
% 4.66/0.97    inference(superposition,[],[f207,f164])).
% 4.66/0.97  fof(f208,plain,(
% 4.66/0.97    spl2_15 | ~spl2_3 | ~spl2_13 | ~spl2_14),
% 4.66/0.97    inference(avatar_split_clause,[],[f202,f167,f163,f42,f206])).
% 4.66/0.97  fof(f202,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5) ) | (~spl2_3 | ~spl2_13 | ~spl2_14)),
% 4.66/0.97    inference(forward_demodulation,[],[f192,f168])).
% 4.66/0.97  fof(f192,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6))) ) | (~spl2_3 | ~spl2_13)),
% 4.66/0.97    inference(superposition,[],[f43,f164])).
% 4.66/0.97  fof(f169,plain,(
% 4.66/0.97    spl2_14),
% 4.66/0.97    inference(avatar_split_clause,[],[f30,f167])).
% 4.66/0.97  fof(f30,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 4.66/0.97    inference(definition_unfolding,[],[f24,f20])).
% 4.66/0.97  fof(f24,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 4.66/0.97    inference(cnf_transformation,[],[f9])).
% 4.66/0.97  fof(f9,axiom,(
% 4.66/0.97    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 4.66/0.97  fof(f165,plain,(
% 4.66/0.97    spl2_13),
% 4.66/0.97    inference(avatar_split_clause,[],[f29,f163])).
% 4.66/0.97  fof(f29,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.66/0.97    inference(definition_unfolding,[],[f22,f20])).
% 4.66/0.97  fof(f22,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.66/0.97    inference(cnf_transformation,[],[f7])).
% 4.66/0.97  fof(f7,axiom,(
% 4.66/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.66/0.97  fof(f161,plain,(
% 4.66/0.97    spl2_12),
% 4.66/0.97    inference(avatar_split_clause,[],[f26,f159])).
% 4.66/0.97  fof(f140,plain,(
% 4.66/0.97    spl2_11 | ~spl2_1 | ~spl2_6 | ~spl2_9),
% 4.66/0.97    inference(avatar_split_clause,[],[f121,f102,f59,f34,f138])).
% 4.66/0.97  fof(f34,plain,(
% 4.66/0.97    spl2_1 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 4.66/0.97  fof(f102,plain,(
% 4.66/0.97    spl2_9 <=> ! [X1,X2] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))),
% 4.66/0.97    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 4.66/0.97  fof(f121,plain,(
% 4.66/0.97    ( ! [X12,X11] : (k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)) ) | (~spl2_1 | ~spl2_6 | ~spl2_9)),
% 4.66/0.97    inference(forward_demodulation,[],[f119,f35])).
% 4.66/0.97  fof(f35,plain,(
% 4.66/0.97    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_1),
% 4.66/0.97    inference(avatar_component_clause,[],[f34])).
% 4.66/0.97  fof(f119,plain,(
% 4.66/0.97    ( ! [X12,X11] : (k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X12,X11))) ) | (~spl2_6 | ~spl2_9)),
% 4.66/0.97    inference(superposition,[],[f60,f103])).
% 4.66/0.97  fof(f103,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl2_9),
% 4.66/0.97    inference(avatar_component_clause,[],[f102])).
% 4.66/0.97  fof(f104,plain,(
% 4.66/0.97    spl2_9 | ~spl2_2 | ~spl2_8),
% 4.66/0.97    inference(avatar_split_clause,[],[f93,f86,f38,f102])).
% 4.66/0.97  fof(f93,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl2_2 | ~spl2_8)),
% 4.66/0.97    inference(superposition,[],[f87,f39])).
% 4.66/0.97  fof(f88,plain,(
% 4.66/0.97    spl2_8 | ~spl2_3 | ~spl2_5),
% 4.66/0.97    inference(avatar_split_clause,[],[f67,f55,f42,f86])).
% 4.66/0.97  fof(f84,plain,(
% 4.66/0.97    spl2_7 | ~spl2_3 | ~spl2_5),
% 4.66/0.97    inference(avatar_split_clause,[],[f66,f55,f42,f82])).
% 4.66/0.97  fof(f66,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)) ) | (~spl2_3 | ~spl2_5)),
% 4.66/0.97    inference(forward_demodulation,[],[f64,f56])).
% 4.66/0.97  fof(f64,plain,(
% 4.66/0.97    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X6,X5),X5) = k4_xboole_0(k2_xboole_0(X5,X6),X5)) ) | (~spl2_3 | ~spl2_5)),
% 4.66/0.97    inference(superposition,[],[f56,f43])).
% 4.66/0.97  fof(f61,plain,(
% 4.66/0.97    spl2_6 | ~spl2_3 | ~spl2_4),
% 4.66/0.97    inference(avatar_split_clause,[],[f53,f46,f42,f59])).
% 4.66/0.97  fof(f53,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_4)),
% 4.66/0.97    inference(forward_demodulation,[],[f52,f43])).
% 4.66/0.97  fof(f52,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_4)),
% 4.66/0.97    inference(superposition,[],[f43,f47])).
% 4.66/0.97  fof(f57,plain,(
% 4.66/0.97    spl2_5 | ~spl2_2 | ~spl2_4),
% 4.66/0.97    inference(avatar_split_clause,[],[f49,f46,f38,f55])).
% 4.66/0.97  fof(f49,plain,(
% 4.66/0.97    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) ) | (~spl2_2 | ~spl2_4)),
% 4.66/0.97    inference(superposition,[],[f47,f39])).
% 4.66/0.97  fof(f48,plain,(
% 4.66/0.97    spl2_4),
% 4.66/0.97    inference(avatar_split_clause,[],[f23,f46])).
% 4.66/0.97  fof(f23,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 4.66/0.97    inference(cnf_transformation,[],[f5])).
% 4.66/0.97  fof(f5,axiom,(
% 4.66/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 4.66/0.97  fof(f44,plain,(
% 4.66/0.97    spl2_3),
% 4.66/0.97    inference(avatar_split_clause,[],[f21,f42])).
% 4.66/0.97  fof(f21,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.66/0.97    inference(cnf_transformation,[],[f4])).
% 4.66/0.97  fof(f4,axiom,(
% 4.66/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.66/0.97  fof(f40,plain,(
% 4.66/0.97    spl2_2),
% 4.66/0.97    inference(avatar_split_clause,[],[f19,f38])).
% 4.66/0.97  fof(f19,plain,(
% 4.66/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.66/0.97    inference(cnf_transformation,[],[f1])).
% 4.66/0.97  fof(f1,axiom,(
% 4.66/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.66/0.97  fof(f36,plain,(
% 4.66/0.97    spl2_1),
% 4.66/0.97    inference(avatar_split_clause,[],[f18,f34])).
% 4.66/0.97  fof(f18,plain,(
% 4.66/0.97    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.66/0.97    inference(cnf_transformation,[],[f13])).
% 4.66/0.97  fof(f13,plain,(
% 4.66/0.97    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.66/0.97    inference(rectify,[],[f3])).
% 4.66/0.97  fof(f3,axiom,(
% 4.66/0.97    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.66/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.66/0.97  % SZS output end Proof for theBenchmark
% 4.66/0.97  % (5685)------------------------------
% 4.66/0.97  % (5685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/0.97  % (5685)Termination reason: Refutation
% 4.66/0.97  
% 4.66/0.97  % (5685)Memory used [KB]: 21364
% 4.66/0.97  % (5685)Time elapsed: 0.502 s
% 4.66/0.97  % (5685)------------------------------
% 4.66/0.97  % (5685)------------------------------
% 4.66/0.97  % (5677)Success in time 0.615 s
%------------------------------------------------------------------------------
