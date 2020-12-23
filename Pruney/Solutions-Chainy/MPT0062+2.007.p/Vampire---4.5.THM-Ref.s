%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:16 EST 2020

% Result     : Theorem 20.87s
% Output     : Refutation 20.87s
% Verified   : 
% Statistics : Number of formulae       :  289 ( 693 expanded)
%              Number of leaves         :   66 ( 355 expanded)
%              Depth                    :   11
%              Number of atoms          :  802 (1637 expanded)
%              Number of equality atoms :  232 ( 636 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50080,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f49,f53,f78,f94,f110,f148,f152,f156,f213,f249,f253,f319,f484,f726,f743,f791,f812,f816,f820,f1163,f1175,f1179,f1462,f1501,f2164,f2172,f2184,f2824,f3035,f3047,f3060,f3138,f3694,f3860,f3973,f4087,f4213,f4297,f4465,f5649,f5901,f7090,f7199,f7594,f9081,f18665,f18729,f30579,f35165,f39773,f43534,f43570,f49847])).

fof(f49847,plain,
    ( spl2_58
    | ~ spl2_181
    | ~ spl2_188
    | ~ spl2_195
    | ~ spl2_204 ),
    inference(avatar_contradiction_clause,[],[f49845])).

fof(f49845,plain,
    ( $false
    | spl2_58
    | ~ spl2_181
    | ~ spl2_188
    | ~ spl2_195
    | ~ spl2_204 ),
    inference(subsumption_resolution,[],[f3059,f49844])).

fof(f49844,plain,
    ( ! [X277,X279,X278] : k2_xboole_0(k4_xboole_0(X279,X277),k4_xboole_0(X277,X278)) = k4_xboole_0(k2_xboole_0(X279,X277),k4_xboole_0(X278,k4_xboole_0(X278,X277)))
    | ~ spl2_181
    | ~ spl2_188
    | ~ spl2_195
    | ~ spl2_204 ),
    inference(backward_demodulation,[],[f44702,f49511])).

fof(f49511,plain,
    ( ! [X189,X190,X188] : k2_xboole_0(k4_xboole_0(X190,X188),k4_xboole_0(X188,X189)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X188,X189),X190),k4_xboole_0(X189,k4_xboole_0(X189,X188)))
    | ~ spl2_181
    | ~ spl2_204 ),
    inference(superposition,[],[f43569,f35164])).

fof(f35164,plain,
    ( ! [X116,X117] : k4_xboole_0(X116,k4_xboole_0(X116,X117)) = k4_xboole_0(X117,k4_xboole_0(X117,X116))
    | ~ spl2_181 ),
    inference(avatar_component_clause,[],[f35163])).

fof(f35163,plain,
    ( spl2_181
  <=> ! [X117,X116] : k4_xboole_0(X116,k4_xboole_0(X116,X117)) = k4_xboole_0(X117,k4_xboole_0(X117,X116)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).

fof(f43569,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(X4,X5),X3)
    | ~ spl2_204 ),
    inference(avatar_component_clause,[],[f43568])).

fof(f43568,plain,
    ( spl2_204
  <=> ! [X3,X5,X4] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(X4,X5),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_204])])).

fof(f44702,plain,
    ( ! [X277,X279,X278] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X277,X278),X279),k4_xboole_0(X278,k4_xboole_0(X278,X277))) = k4_xboole_0(k2_xboole_0(X279,X277),k4_xboole_0(X278,k4_xboole_0(X278,X277)))
    | ~ spl2_188
    | ~ spl2_195 ),
    inference(superposition,[],[f43533,f39772])).

fof(f39772,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4
    | ~ spl2_188 ),
    inference(avatar_component_clause,[],[f39771])).

fof(f39771,plain,
    ( spl2_188
  <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).

fof(f43533,plain,
    ( ! [X21,X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),X21) = k4_xboole_0(k2_xboole_0(X20,k2_xboole_0(X19,X21)),X21)
    | ~ spl2_195 ),
    inference(avatar_component_clause,[],[f43532])).

fof(f43532,plain,
    ( spl2_195
  <=> ! [X20,X19,X21] : k4_xboole_0(k2_xboole_0(X19,X20),X21) = k4_xboole_0(k2_xboole_0(X20,k2_xboole_0(X19,X21)),X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).

fof(f3059,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_58 ),
    inference(avatar_component_clause,[],[f3057])).

fof(f3057,plain,
    ( spl2_58
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f43570,plain,
    ( spl2_204
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_36
    | ~ spl2_37
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f7036,f5899,f5647,f4211,f1177,f1173,f789,f741,f47,f38,f34,f30,f43568])).

fof(f30,plain,
    ( spl2_1
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f34,plain,
    ( spl2_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f38,plain,
    ( spl2_3
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f741,plain,
    ( spl2_24
  <=> ! [X5,X4] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f789,plain,
    ( spl2_26
  <=> ! [X7,X8] : k4_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1173,plain,
    ( spl2_36
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f1177,plain,
    ( spl2_37
  <=> ! [X32,X31,X33] : k2_xboole_0(X33,X31) = k2_xboole_0(X31,k2_xboole_0(k4_xboole_0(X31,X32),X33)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f4211,plain,
    ( spl2_70
  <=> ! [X40,X41] : k4_xboole_0(X40,k4_xboole_0(X41,X41)) = X40 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f5647,plain,
    ( spl2_77
  <=> ! [X9,X8,X10] : k4_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X10,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f5899,plain,
    ( spl2_78
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f7036,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(X4,X5),X3)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_36
    | ~ spl2_37
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f7035,f2203])).

fof(f2203,plain,
    ( ! [X4,X2,X3] : k2_xboole_0(k4_xboole_0(X4,X3),X2) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X4),X3))
    | ~ spl2_36
    | ~ spl2_37 ),
    inference(superposition,[],[f1178,f1174])).

fof(f1174,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f1173])).

fof(f1178,plain,
    ( ! [X33,X31,X32] : k2_xboole_0(X33,X31) = k2_xboole_0(X31,k2_xboole_0(k4_xboole_0(X31,X32),X33))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f7035,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X3,X4),X5))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f7030,f31])).

fof(f31,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f7030,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),X3)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(backward_demodulation,[],[f6985,f7024])).

fof(f7024,plain,
    ( ! [X88,X85] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = X85
    | ~ spl2_1
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f7023,f742])).

fof(f742,plain,
    ( ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f741])).

fof(f7023,plain,
    ( ! [X88,X85] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(X85,k4_xboole_0(X85,X88))
    | ~ spl2_1
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f7022,f31])).

fof(f7022,plain,
    ( ! [X88,X85] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(k4_xboole_0(X85,X88),X85)
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f7021,f4212])).

fof(f4212,plain,
    ( ! [X41,X40] : k4_xboole_0(X40,k4_xboole_0(X41,X41)) = X40
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f4211])).

fof(f7021,plain,
    ( ! [X88,X85,X86] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(k4_xboole_0(X85,X88),k4_xboole_0(X85,k4_xboole_0(X86,X86)))
    | ~ spl2_26
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f6894,f790])).

fof(f790,plain,
    ( ! [X8,X7] : k4_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,X7)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f789])).

fof(f6894,plain,
    ( ! [X88,X87,X85,X86] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(k4_xboole_0(X85,X88),k4_xboole_0(X85,k4_xboole_0(k4_xboole_0(X86,X87),X86)))
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(superposition,[],[f5900,f5648])).

fof(f5648,plain,
    ( ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X10,X10)
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f5647])).

fof(f5900,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f5899])).

fof(f6985,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(X3,k4_xboole_0(X4,X3)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f6870,f43])).

fof(f43,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f39,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f6870,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X4,X3)))
    | ~ spl2_4
    | ~ spl2_78 ),
    inference(superposition,[],[f5900,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f43534,plain,
    ( spl2_195
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f861,f810,f38,f43532])).

fof(f810,plain,
    ( spl2_27
  <=> ! [X1,X0,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f861,plain,
    ( ! [X21,X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),X21) = k4_xboole_0(k2_xboole_0(X20,k2_xboole_0(X19,X21)),X21)
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(superposition,[],[f39,f811])).

fof(f811,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f810])).

fof(f39773,plain,
    ( spl2_188
    | ~ spl2_29
    | ~ spl2_181 ),
    inference(avatar_split_clause,[],[f36151,f35163,f818,f39771])).

fof(f818,plain,
    ( spl2_29
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f36151,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4
    | ~ spl2_29
    | ~ spl2_181 ),
    inference(superposition,[],[f819,f35164])).

fof(f819,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f818])).

fof(f35165,plain,
    ( spl2_181
    | ~ spl2_98
    | ~ spl2_154
    | ~ spl2_171 ),
    inference(avatar_split_clause,[],[f30835,f30577,f18663,f7592,f35163])).

fof(f7592,plain,
    ( spl2_98
  <=> ! [X1,X2] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f18663,plain,
    ( spl2_154
  <=> ! [X115,X117,X116] : k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k4_xboole_0(X115,X117) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).

fof(f30577,plain,
    ( spl2_171
  <=> ! [X25,X24] : k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25))) = X25 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).

fof(f30835,plain,
    ( ! [X116,X117] : k4_xboole_0(X116,k4_xboole_0(X116,X117)) = k4_xboole_0(X117,k4_xboole_0(X117,X116))
    | ~ spl2_98
    | ~ spl2_154
    | ~ spl2_171 ),
    inference(forward_demodulation,[],[f30744,f18664])).

fof(f18664,plain,
    ( ! [X116,X117,X115] : k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k4_xboole_0(X115,X117)
    | ~ spl2_154 ),
    inference(avatar_component_clause,[],[f18663])).

fof(f30744,plain,
    ( ! [X116,X117] : k4_xboole_0(X117,k4_xboole_0(X117,X116)) = k4_xboole_0(X116,k4_xboole_0(X116,k4_xboole_0(X117,k4_xboole_0(X117,X116))))
    | ~ spl2_98
    | ~ spl2_171 ),
    inference(superposition,[],[f7593,f30578])).

fof(f30578,plain,
    ( ! [X24,X25] : k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25))) = X25
    | ~ spl2_171 ),
    inference(avatar_component_clause,[],[f30577])).

fof(f7593,plain,
    ( ! [X2,X1] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f7592])).

fof(f30579,plain,
    ( spl2_171
    | ~ spl2_2
    | ~ spl2_67
    | ~ spl2_170 ),
    inference(avatar_split_clause,[],[f30560,f18727,f3858,f34,f30577])).

fof(f3858,plain,
    ( spl2_67
  <=> ! [X77,X76] : k2_xboole_0(X76,k4_xboole_0(X77,X77)) = X76 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f18727,plain,
    ( spl2_170
  <=> ! [X117,X116] : k4_xboole_0(X116,X116) = k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).

fof(f30560,plain,
    ( ! [X24,X25] : k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25))) = X25
    | ~ spl2_2
    | ~ spl2_67
    | ~ spl2_170 ),
    inference(forward_demodulation,[],[f30434,f3859])).

fof(f3859,plain,
    ( ! [X76,X77] : k2_xboole_0(X76,k4_xboole_0(X77,X77)) = X76
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f3858])).

fof(f30434,plain,
    ( ! [X24,X25] : k2_xboole_0(X25,k4_xboole_0(X24,X24)) = k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25)))
    | ~ spl2_2
    | ~ spl2_170 ),
    inference(superposition,[],[f35,f18728])).

fof(f18728,plain,
    ( ! [X116,X117] : k4_xboole_0(X116,X116) = k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117)
    | ~ spl2_170 ),
    inference(avatar_component_clause,[],[f18727])).

fof(f18729,plain,
    ( spl2_170
    | ~ spl2_52
    | ~ spl2_94
    | ~ spl2_104 ),
    inference(avatar_split_clause,[],[f9208,f9079,f7088,f3033,f18727])).

fof(f3033,plain,
    ( spl2_52
  <=> ! [X11,X13,X12] : k4_xboole_0(X11,X11) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f7088,plain,
    ( spl2_94
  <=> ! [X85,X88] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = X85 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).

fof(f9079,plain,
    ( spl2_104
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f9208,plain,
    ( ! [X116,X117] : k4_xboole_0(X116,X116) = k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117)
    | ~ spl2_52
    | ~ spl2_94
    | ~ spl2_104 ),
    inference(forward_demodulation,[],[f9177,f3034])).

fof(f3034,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(X11,X11) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11)
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f3033])).

fof(f9177,plain,
    ( ! [X116,X117] : k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117),X116)
    | ~ spl2_94
    | ~ spl2_104 ),
    inference(superposition,[],[f7089,f9080])).

fof(f9080,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f9079])).

fof(f7089,plain,
    ( ! [X88,X85] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = X85
    | ~ spl2_94 ),
    inference(avatar_component_clause,[],[f7088])).

fof(f18665,plain,
    ( spl2_154
    | ~ spl2_67
    | ~ spl2_78
    | ~ spl2_94 ),
    inference(avatar_split_clause,[],[f7195,f7088,f5899,f3858,f18663])).

fof(f7195,plain,
    ( ! [X116,X117,X115] : k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k4_xboole_0(X115,X117)
    | ~ spl2_67
    | ~ spl2_78
    | ~ spl2_94 ),
    inference(forward_demodulation,[],[f7161,f3859])).

fof(f7161,plain,
    ( ! [X116,X117,X115] : k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k2_xboole_0(k4_xboole_0(X115,X117),k4_xboole_0(X115,X115))
    | ~ spl2_78
    | ~ spl2_94 ),
    inference(superposition,[],[f5900,f7089])).

fof(f9081,plain,
    ( spl2_104
    | ~ spl2_13
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f6904,f5899,f154,f9079])).

fof(f154,plain,
    ( spl2_13
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f6904,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0
    | ~ spl2_13
    | ~ spl2_78 ),
    inference(superposition,[],[f5900,f155])).

fof(f155,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f7594,plain,
    ( spl2_98
    | ~ spl2_1
    | ~ spl2_95 ),
    inference(avatar_split_clause,[],[f7205,f7197,f30,f7592])).

fof(f7197,plain,
    ( spl2_95
  <=> ! [X5,X4] : k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f7205,plain,
    ( ! [X2,X1] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1
    | ~ spl2_1
    | ~ spl2_95 ),
    inference(superposition,[],[f7198,f31])).

fof(f7198,plain,
    ( ! [X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f7197])).

fof(f7199,plain,
    ( spl2_95
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f7025,f5899,f5647,f4211,f789,f741,f38,f34,f30,f7197])).

fof(f7025,plain,
    ( ! [X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(backward_demodulation,[],[f43,f7024])).

fof(f7090,plain,
    ( spl2_94
    | ~ spl2_1
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_70
    | ~ spl2_77
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f7024,f5899,f5647,f4211,f789,f741,f30,f7088])).

fof(f5901,plain,(
    spl2_78 ),
    inference(avatar_split_clause,[],[f28,f5899])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f23,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f5649,plain,
    ( spl2_77
    | ~ spl2_55
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f5560,f4463,f3045,f5647])).

fof(f3045,plain,
    ( spl2_55
  <=> ! [X18,X17,X19] : k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(X18,X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f4463,plain,
    ( spl2_72
  <=> ! [X16,X15,X14] : k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X16,X16),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f5560,plain,
    ( ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X10,X10)
    | ~ spl2_55
    | ~ spl2_72 ),
    inference(superposition,[],[f3046,f4464])).

fof(f4464,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X16,X16),X14)
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f4463])).

fof(f3046,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(X18,X17)
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f3045])).

fof(f4465,plain,
    ( spl2_72
    | ~ spl2_69
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f4303,f4295,f4085,f4463])).

fof(f4085,plain,
    ( spl2_69
  <=> ! [X55,X56] : k4_xboole_0(X56,X56) = k4_xboole_0(X55,X55) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f4295,plain,
    ( spl2_71
  <=> ! [X73,X72] : k4_xboole_0(X72,X72) = k4_xboole_0(k4_xboole_0(X73,X73),X72) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f4303,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X16,X16),X14)
    | ~ spl2_69
    | ~ spl2_71 ),
    inference(superposition,[],[f4296,f4086])).

fof(f4086,plain,
    ( ! [X56,X55] : k4_xboole_0(X56,X56) = k4_xboole_0(X55,X55)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f4085])).

fof(f4296,plain,
    ( ! [X72,X73] : k4_xboole_0(X72,X72) = k4_xboole_0(k4_xboole_0(X73,X73),X72)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f4295])).

fof(f4297,plain,
    ( spl2_71
    | ~ spl2_52
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f3782,f3692,f3033,f4295])).

fof(f3692,plain,
    ( spl2_65
  <=> ! [X3,X2] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f3782,plain,
    ( ! [X72,X73] : k4_xboole_0(X72,X72) = k4_xboole_0(k4_xboole_0(X73,X73),X72)
    | ~ spl2_52
    | ~ spl2_65 ),
    inference(superposition,[],[f3034,f3693])).

fof(f3693,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f3692])).

fof(f4213,plain,
    ( spl2_70
    | ~ spl2_20
    | ~ spl2_40
    | ~ spl2_65
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f3939,f3858,f3692,f1499,f482,f4211])).

fof(f482,plain,
    ( spl2_20
  <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1499,plain,
    ( spl2_40
  <=> ! [X20,X22,X21] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),X20) = X20 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f3939,plain,
    ( ! [X41,X40] : k4_xboole_0(X40,k4_xboole_0(X41,X41)) = X40
    | ~ spl2_20
    | ~ spl2_40
    | ~ spl2_65
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f3876,f3783])).

fof(f3783,plain,
    ( ! [X74,X75] : k2_xboole_0(k4_xboole_0(X75,X75),X74) = X74
    | ~ spl2_40
    | ~ spl2_65 ),
    inference(superposition,[],[f1500,f3693])).

fof(f1500,plain,
    ( ! [X21,X22,X20] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),X20) = X20
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f3876,plain,
    ( ! [X41,X40] : k4_xboole_0(X40,k4_xboole_0(X41,X41)) = k2_xboole_0(k4_xboole_0(X41,X41),X40)
    | ~ spl2_20
    | ~ spl2_67 ),
    inference(superposition,[],[f3859,f483])).

fof(f483,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f482])).

fof(f4087,plain,
    ( spl2_69
    | ~ spl2_67
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f3995,f3971,f3858,f4085])).

fof(f3971,plain,
    ( spl2_68
  <=> ! [X75,X74] : k2_xboole_0(k4_xboole_0(X75,X75),X74) = X74 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f3995,plain,
    ( ! [X56,X55] : k4_xboole_0(X56,X56) = k4_xboole_0(X55,X55)
    | ~ spl2_67
    | ~ spl2_68 ),
    inference(superposition,[],[f3972,f3859])).

fof(f3972,plain,
    ( ! [X74,X75] : k2_xboole_0(k4_xboole_0(X75,X75),X74) = X74
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f3971])).

fof(f3973,plain,
    ( spl2_68
    | ~ spl2_40
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f3783,f3692,f1499,f3971])).

fof(f3860,plain,
    ( spl2_67
    | ~ spl2_39
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f3784,f3692,f1460,f3858])).

fof(f1460,plain,
    ( spl2_39
  <=> ! [X44,X43,X45] : k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45)) = X43 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f3784,plain,
    ( ! [X76,X77] : k2_xboole_0(X76,k4_xboole_0(X77,X77)) = X76
    | ~ spl2_39
    | ~ spl2_65 ),
    inference(superposition,[],[f1461,f3693])).

fof(f1461,plain,
    ( ! [X45,X43,X44] : k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45)) = X43
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f3694,plain,
    ( spl2_65
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_26
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f3190,f3136,f789,f76,f47,f38,f3692])).

fof(f76,plain,
    ( spl2_7
  <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f3136,plain,
    ( spl2_59
  <=> ! [X5,X6] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f3190,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_26
    | ~ spl2_59 ),
    inference(backward_demodulation,[],[f804,f3187])).

fof(f3187,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5)
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_59 ),
    inference(backward_demodulation,[],[f88,f3186])).

fof(f3186,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_59 ),
    inference(forward_demodulation,[],[f3143,f3137])).

fof(f3137,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f3136])).

fof(f3143,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_59 ),
    inference(superposition,[],[f3137,f39])).

fof(f88,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f39,f77])).

fof(f77,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f804,plain,
    ( ! [X2,X3] : k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f793,f88])).

fof(f793,plain,
    ( ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))
    | ~ spl2_4
    | ~ spl2_26 ),
    inference(superposition,[],[f790,f48])).

fof(f3138,plain,
    ( spl2_59
    | ~ spl2_12
    | ~ spl2_26
    | ~ spl2_50
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f3115,f3033,f2822,f789,f150,f3136])).

fof(f150,plain,
    ( spl2_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f2822,plain,
    ( spl2_50
  <=> ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = X11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f3115,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))
    | ~ spl2_12
    | ~ spl2_26
    | ~ spl2_50
    | ~ spl2_52 ),
    inference(backward_demodulation,[],[f798,f3079])).

fof(f3079,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X2))
    | ~ spl2_50
    | ~ spl2_52 ),
    inference(superposition,[],[f2823,f3034])).

fof(f2823,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = X11
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f2822])).

fof(f798,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X5)))
    | ~ spl2_12
    | ~ spl2_26 ),
    inference(superposition,[],[f151,f790])).

fof(f151,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f3060,plain,(
    ~ spl2_58 ),
    inference(avatar_split_clause,[],[f25,f3057])).

fof(f25,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f3047,plain,
    ( spl2_55
    | ~ spl2_4
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f2491,f2170,f47,f3045])).

fof(f2170,plain,
    ( spl2_44
  <=> ! [X40,X42,X41] : k2_xboole_0(X40,X42) = k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f2491,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(X18,X17)
    | ~ spl2_4
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f2455,f48])).

fof(f2455,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(k2_xboole_0(X17,X18),X17)
    | ~ spl2_4
    | ~ spl2_44 ),
    inference(superposition,[],[f48,f2171])).

fof(f2171,plain,
    ( ! [X41,X42,X40] : k2_xboole_0(X40,X42) = k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41)))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f2170])).

fof(f3035,plain,
    ( spl2_52
    | ~ spl2_4
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f1475,f1460,f47,f3033])).

fof(f1475,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(X11,X11) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11)
    | ~ spl2_4
    | ~ spl2_39 ),
    inference(superposition,[],[f48,f1461])).

fof(f2824,plain,
    ( spl2_50
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_42
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f2793,f2182,f2162,f724,f34,f30,f2822])).

fof(f724,plain,
    ( spl2_23
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f2162,plain,
    ( spl2_42
  <=> ! [X11,X12] : k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f2182,plain,
    ( spl2_47
  <=> ! [X55,X56,X57] : k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,X57) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f2793,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = X11
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_42
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f2792,f725])).

fof(f725,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f724])).

fof(f2792,plain,
    ( ! [X12,X11] : k2_xboole_0(X11,X11) = k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_42
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f2791,f35])).

fof(f2791,plain,
    ( ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,X11)) = k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12))
    | ~ spl2_1
    | ~ spl2_42
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f2736,f31])).

fof(f2736,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = k2_xboole_0(k4_xboole_0(X11,X11),X11)
    | ~ spl2_42
    | ~ spl2_47 ),
    inference(superposition,[],[f2183,f2163])).

fof(f2163,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X11))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f2162])).

fof(f2183,plain,
    ( ! [X57,X56,X55] : k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,X57)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f2184,plain,
    ( spl2_47
    | ~ spl2_2
    | ~ spl2_33
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f2041,f1177,f1161,f34,f2182])).

fof(f1161,plain,
    ( spl2_33
  <=> ! [X20,X19,X21] : k2_xboole_0(X19,X21) = k2_xboole_0(X19,k2_xboole_0(k4_xboole_0(X19,X20),X21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f2041,plain,
    ( ! [X57,X56,X55] : k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,X57)
    | ~ spl2_2
    | ~ spl2_33
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f1991,f1162])).

fof(f1162,plain,
    ( ! [X21,X19,X20] : k2_xboole_0(X19,X21) = k2_xboole_0(X19,k2_xboole_0(k4_xboole_0(X19,X20),X21))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1991,plain,
    ( ! [X57,X56,X55] : k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,k2_xboole_0(k4_xboole_0(X55,X56),X57))
    | ~ spl2_2
    | ~ spl2_37 ),
    inference(superposition,[],[f1178,f35])).

fof(f2172,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f1432,f1161,f34,f2170])).

fof(f1432,plain,
    ( ! [X41,X42,X40] : k2_xboole_0(X40,X42) = k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41)))
    | ~ spl2_2
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f1398,f1162])).

fof(f1398,plain,
    ( ! [X41,X42,X40] : k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41))) = k2_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X41),X42))
    | ~ spl2_2
    | ~ spl2_33 ),
    inference(superposition,[],[f1162,f35])).

fof(f2164,plain,
    ( spl2_42
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f801,f789,f741,f2162])).

fof(f801,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X11))
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(superposition,[],[f742,f790])).

fof(f1501,plain,
    ( spl2_40
    | ~ spl2_8
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f1477,f1460,f92,f1499])).

fof(f92,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f1477,plain,
    ( ! [X21,X22,X20] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),X20) = X20
    | ~ spl2_8
    | ~ spl2_39 ),
    inference(superposition,[],[f93,f1461])).

fof(f93,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1462,plain,
    ( spl2_39
    | ~ spl2_24
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f1433,f1161,f741,f1460])).

fof(f1433,plain,
    ( ! [X45,X43,X44] : k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45)) = X43
    | ~ spl2_24
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f1399,f742])).

fof(f1399,plain,
    ( ! [X45,X43,X44] : k2_xboole_0(X43,k4_xboole_0(X43,X44)) = k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45))
    | ~ spl2_24
    | ~ spl2_33 ),
    inference(superposition,[],[f1162,f742])).

fof(f1179,plain,
    ( spl2_37
    | ~ spl2_24
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f925,f814,f741,f1177])).

fof(f814,plain,
    ( spl2_28
  <=> ! [X9,X7,X8] : k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f925,plain,
    ( ! [X33,X31,X32] : k2_xboole_0(X33,X31) = k2_xboole_0(X31,k2_xboole_0(k4_xboole_0(X31,X32),X33))
    | ~ spl2_24
    | ~ spl2_28 ),
    inference(superposition,[],[f815,f742])).

fof(f815,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f814])).

fof(f1175,plain,(
    spl2_36 ),
    inference(avatar_split_clause,[],[f24,f1173])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f1163,plain,
    ( spl2_33
    | ~ spl2_11
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f756,f741,f146,f1161])).

fof(f146,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f756,plain,
    ( ! [X21,X19,X20] : k2_xboole_0(X19,X21) = k2_xboole_0(X19,k2_xboole_0(k4_xboole_0(X19,X20),X21))
    | ~ spl2_11
    | ~ spl2_24 ),
    inference(superposition,[],[f147,f742])).

fof(f147,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f820,plain,
    ( spl2_29
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f676,f154,f150,f818])).

fof(f676,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(superposition,[],[f155,f151])).

fof(f816,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f168,f146,f30,f814])).

fof(f168,plain,
    ( ! [X8,X7,X9] : k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(superposition,[],[f147,f31])).

fof(f812,plain,
    ( spl2_27
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f157,f146,f30,f810])).

fof(f157,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(superposition,[],[f147,f31])).

fof(f791,plain,
    ( spl2_26
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f751,f741,f47,f789])).

fof(f751,plain,
    ( ! [X8,X7] : k4_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,X7)
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(superposition,[],[f48,f742])).

fof(f743,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f716,f482,f154,f150,f34,f30,f741])).

fof(f716,plain,
    ( ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(backward_demodulation,[],[f672,f682])).

fof(f682,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(superposition,[],[f155,f483])).

fof(f672,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X4) = k2_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f671,f31])).

fof(f671,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X4) = k2_xboole_0(k4_xboole_0(X4,X5),X4)
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f661,f483])).

fof(f661,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X4) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5))
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(superposition,[],[f35,f151])).

fof(f726,plain,
    ( spl2_23
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f700,f251,f154,f724])).

fof(f251,plain,
    ( spl2_16
  <=> ! [X9,X10] : k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(X10,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f700,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f699,f155])).

fof(f699,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X0)
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f675,f252])).

fof(f252,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(X10,X9)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f675,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X1)),k4_xboole_0(k2_xboole_0(X0,X0),X1))
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(superposition,[],[f155,f252])).

fof(f484,plain,
    ( spl2_20
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f354,f317,f76,f34,f482])).

fof(f317,plain,
    ( spl2_17
  <=> ! [X3,X2] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f354,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f330,f77])).

fof(f330,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,k2_xboole_0(X4,X5))
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(superposition,[],[f318,f35])).

fof(f318,plain,
    ( ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f317])).

fof(f319,plain,
    ( spl2_17
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f257,f247,f146,f317])).

fof(f247,plain,
    ( spl2_15
  <=> ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X6),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f257,plain,
    ( ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(superposition,[],[f248,f147])).

fof(f248,plain,
    ( ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X6),X5)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f247])).

fof(f253,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f239,f211,f47,f251])).

fof(f211,plain,
    ( spl2_14
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f239,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(X10,X9)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f224,f48])).

fof(f224,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(k2_xboole_0(X9,X10),X9)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f48,f212])).

fof(f212,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f211])).

fof(f249,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f216,f211,f30,f247])).

fof(f216,plain,
    ( ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X6),X5)
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(superposition,[],[f212,f31])).

fof(f213,plain,
    ( spl2_14
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f166,f146,f108,f211])).

fof(f108,plain,
    ( spl2_9
  <=> ! [X11,X12] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f166,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1))
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(superposition,[],[f147,f109])).

fof(f109,plain,
    ( ! [X12,X11] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f156,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f27,f154])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f152,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f26,f150])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f148,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f22,f146])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f110,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f106,f92,f76,f51,f30,f108])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f106,plain,
    ( ! [X12,X11] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f104,f90])).

fof(f90,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f89,f77])).

fof(f89,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f87,f31])).

fof(f87,plain,
    ( ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(superposition,[],[f52,f77])).

fof(f52,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f104,plain,
    ( ! [X12,X11] : k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X12,X11))
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(superposition,[],[f52,f93])).

fof(f94,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f82,f76,f30,f92])).

fof(f82,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f77,f31])).

fof(f78,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f59,f47,f34,f76])).

fof(f59,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f57,f35])).

fof(f57,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f35,f48])).

fof(f53,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f45,f38,f34,f51])).

fof(f45,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f44,f35])).

fof(f44,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f35,f39])).

fof(f49,plain,
    ( spl2_4
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f41,f38,f30,f47])).

fof(f41,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f39,f31])).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.42  % (7793)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (7781)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (7779)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (7790)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (7782)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (7780)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (7789)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (7777)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (7785)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (7792)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (7788)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (7784)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (7778)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (7786)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (7783)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (7787)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (7788)Refutation not found, incomplete strategy% (7788)------------------------------
% 0.20/0.50  % (7788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7788)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7788)Memory used [KB]: 10490
% 0.20/0.50  % (7788)Time elapsed: 0.091 s
% 0.20/0.50  % (7788)------------------------------
% 0.20/0.50  % (7788)------------------------------
% 0.20/0.50  % (7794)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (7791)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 5.24/1.02  % (7781)Time limit reached!
% 5.24/1.02  % (7781)------------------------------
% 5.24/1.02  % (7781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.02  % (7781)Termination reason: Time limit
% 5.24/1.02  % (7781)Termination phase: Saturation
% 5.24/1.02  
% 5.24/1.02  % (7781)Memory used [KB]: 15607
% 5.24/1.02  % (7781)Time elapsed: 0.600 s
% 5.24/1.02  % (7781)------------------------------
% 5.24/1.02  % (7781)------------------------------
% 12.32/1.95  % (7783)Time limit reached!
% 12.32/1.95  % (7783)------------------------------
% 12.32/1.95  % (7783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.32/1.95  % (7783)Termination reason: Time limit
% 12.32/1.95  % (7783)Termination phase: Saturation
% 12.32/1.95  
% 12.32/1.95  % (7783)Memory used [KB]: 26865
% 12.32/1.95  % (7783)Time elapsed: 1.500 s
% 12.32/1.95  % (7783)------------------------------
% 12.32/1.95  % (7783)------------------------------
% 14.12/2.13  % (7782)Time limit reached!
% 14.12/2.13  % (7782)------------------------------
% 14.12/2.13  % (7782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.12/2.13  % (7782)Termination reason: Time limit
% 14.12/2.13  % (7782)Termination phase: Saturation
% 14.12/2.13  
% 14.12/2.13  % (7782)Memory used [KB]: 43368
% 14.12/2.13  % (7782)Time elapsed: 1.500 s
% 14.12/2.13  % (7782)------------------------------
% 14.12/2.13  % (7782)------------------------------
% 14.82/2.22  % (7779)Time limit reached!
% 14.82/2.22  % (7779)------------------------------
% 14.82/2.22  % (7779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.82/2.22  % (7779)Termination reason: Time limit
% 14.82/2.22  % (7779)Termination phase: Saturation
% 14.82/2.22  
% 14.82/2.22  % (7779)Memory used [KB]: 42088
% 14.82/2.22  % (7779)Time elapsed: 1.800 s
% 14.82/2.22  % (7779)------------------------------
% 14.82/2.22  % (7779)------------------------------
% 17.83/2.62  % (7789)Time limit reached!
% 17.83/2.62  % (7789)------------------------------
% 17.83/2.62  % (7789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.83/2.62  % (7789)Termination reason: Time limit
% 17.83/2.62  % (7789)Termination phase: Saturation
% 17.83/2.62  
% 17.83/2.62  % (7789)Memory used [KB]: 42856
% 17.83/2.62  % (7789)Time elapsed: 2.200 s
% 17.83/2.62  % (7789)------------------------------
% 17.83/2.62  % (7789)------------------------------
% 20.87/3.00  % (7784)Refutation found. Thanks to Tanya!
% 20.87/3.00  % SZS status Theorem for theBenchmark
% 20.87/3.00  % SZS output start Proof for theBenchmark
% 20.87/3.00  fof(f50080,plain,(
% 20.87/3.00    $false),
% 20.87/3.00    inference(avatar_sat_refutation,[],[f32,f36,f40,f49,f53,f78,f94,f110,f148,f152,f156,f213,f249,f253,f319,f484,f726,f743,f791,f812,f816,f820,f1163,f1175,f1179,f1462,f1501,f2164,f2172,f2184,f2824,f3035,f3047,f3060,f3138,f3694,f3860,f3973,f4087,f4213,f4297,f4465,f5649,f5901,f7090,f7199,f7594,f9081,f18665,f18729,f30579,f35165,f39773,f43534,f43570,f49847])).
% 20.87/3.00  fof(f49847,plain,(
% 20.87/3.00    spl2_58 | ~spl2_181 | ~spl2_188 | ~spl2_195 | ~spl2_204),
% 20.87/3.00    inference(avatar_contradiction_clause,[],[f49845])).
% 20.87/3.00  fof(f49845,plain,(
% 20.87/3.00    $false | (spl2_58 | ~spl2_181 | ~spl2_188 | ~spl2_195 | ~spl2_204)),
% 20.87/3.00    inference(subsumption_resolution,[],[f3059,f49844])).
% 20.87/3.00  fof(f49844,plain,(
% 20.87/3.00    ( ! [X277,X279,X278] : (k2_xboole_0(k4_xboole_0(X279,X277),k4_xboole_0(X277,X278)) = k4_xboole_0(k2_xboole_0(X279,X277),k4_xboole_0(X278,k4_xboole_0(X278,X277)))) ) | (~spl2_181 | ~spl2_188 | ~spl2_195 | ~spl2_204)),
% 20.87/3.00    inference(backward_demodulation,[],[f44702,f49511])).
% 20.87/3.00  fof(f49511,plain,(
% 20.87/3.00    ( ! [X189,X190,X188] : (k2_xboole_0(k4_xboole_0(X190,X188),k4_xboole_0(X188,X189)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X188,X189),X190),k4_xboole_0(X189,k4_xboole_0(X189,X188)))) ) | (~spl2_181 | ~spl2_204)),
% 20.87/3.00    inference(superposition,[],[f43569,f35164])).
% 20.87/3.00  fof(f35164,plain,(
% 20.87/3.00    ( ! [X116,X117] : (k4_xboole_0(X116,k4_xboole_0(X116,X117)) = k4_xboole_0(X117,k4_xboole_0(X117,X116))) ) | ~spl2_181),
% 20.87/3.00    inference(avatar_component_clause,[],[f35163])).
% 20.87/3.00  fof(f35163,plain,(
% 20.87/3.00    spl2_181 <=> ! [X117,X116] : k4_xboole_0(X116,k4_xboole_0(X116,X117)) = k4_xboole_0(X117,k4_xboole_0(X117,X116))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).
% 20.87/3.00  fof(f43569,plain,(
% 20.87/3.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(X4,X5),X3)) ) | ~spl2_204),
% 20.87/3.00    inference(avatar_component_clause,[],[f43568])).
% 20.87/3.00  fof(f43568,plain,(
% 20.87/3.00    spl2_204 <=> ! [X3,X5,X4] : k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(X4,X5),X3)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_204])])).
% 20.87/3.00  fof(f44702,plain,(
% 20.87/3.00    ( ! [X277,X279,X278] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X277,X278),X279),k4_xboole_0(X278,k4_xboole_0(X278,X277))) = k4_xboole_0(k2_xboole_0(X279,X277),k4_xboole_0(X278,k4_xboole_0(X278,X277)))) ) | (~spl2_188 | ~spl2_195)),
% 20.87/3.00    inference(superposition,[],[f43533,f39772])).
% 20.87/3.00  fof(f39772,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4) ) | ~spl2_188),
% 20.87/3.00    inference(avatar_component_clause,[],[f39771])).
% 20.87/3.00  fof(f39771,plain,(
% 20.87/3.00    spl2_188 <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).
% 20.87/3.00  fof(f43533,plain,(
% 20.87/3.00    ( ! [X21,X19,X20] : (k4_xboole_0(k2_xboole_0(X19,X20),X21) = k4_xboole_0(k2_xboole_0(X20,k2_xboole_0(X19,X21)),X21)) ) | ~spl2_195),
% 20.87/3.00    inference(avatar_component_clause,[],[f43532])).
% 20.87/3.00  fof(f43532,plain,(
% 20.87/3.00    spl2_195 <=> ! [X20,X19,X21] : k4_xboole_0(k2_xboole_0(X19,X20),X21) = k4_xboole_0(k2_xboole_0(X20,k2_xboole_0(X19,X21)),X21)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).
% 20.87/3.00  fof(f3059,plain,(
% 20.87/3.00    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_58),
% 20.87/3.00    inference(avatar_component_clause,[],[f3057])).
% 20.87/3.00  fof(f3057,plain,(
% 20.87/3.00    spl2_58 <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 20.87/3.00  fof(f43570,plain,(
% 20.87/3.00    spl2_204 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_24 | ~spl2_26 | ~spl2_36 | ~spl2_37 | ~spl2_70 | ~spl2_77 | ~spl2_78),
% 20.87/3.00    inference(avatar_split_clause,[],[f7036,f5899,f5647,f4211,f1177,f1173,f789,f741,f47,f38,f34,f30,f43568])).
% 20.87/3.00  fof(f30,plain,(
% 20.87/3.00    spl2_1 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 20.87/3.00  fof(f34,plain,(
% 20.87/3.00    spl2_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 20.87/3.00  fof(f38,plain,(
% 20.87/3.00    spl2_3 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 20.87/3.00  fof(f47,plain,(
% 20.87/3.00    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 20.87/3.00  fof(f741,plain,(
% 20.87/3.00    spl2_24 <=> ! [X5,X4] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 20.87/3.00  fof(f789,plain,(
% 20.87/3.00    spl2_26 <=> ! [X7,X8] : k4_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,X7)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 20.87/3.00  fof(f1173,plain,(
% 20.87/3.00    spl2_36 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 20.87/3.00  fof(f1177,plain,(
% 20.87/3.00    spl2_37 <=> ! [X32,X31,X33] : k2_xboole_0(X33,X31) = k2_xboole_0(X31,k2_xboole_0(k4_xboole_0(X31,X32),X33))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 20.87/3.00  fof(f4211,plain,(
% 20.87/3.00    spl2_70 <=> ! [X40,X41] : k4_xboole_0(X40,k4_xboole_0(X41,X41)) = X40),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 20.87/3.00  fof(f5647,plain,(
% 20.87/3.00    spl2_77 <=> ! [X9,X8,X10] : k4_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X10,X10)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 20.87/3.00  fof(f5899,plain,(
% 20.87/3.00    spl2_78 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 20.87/3.00  fof(f7036,plain,(
% 20.87/3.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(X4,X5),X3)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_24 | ~spl2_26 | ~spl2_36 | ~spl2_37 | ~spl2_70 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(forward_demodulation,[],[f7035,f2203])).
% 20.87/3.00  fof(f2203,plain,(
% 20.87/3.00    ( ! [X4,X2,X3] : (k2_xboole_0(k4_xboole_0(X4,X3),X2) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X4),X3))) ) | (~spl2_36 | ~spl2_37)),
% 20.87/3.00    inference(superposition,[],[f1178,f1174])).
% 20.87/3.00  fof(f1174,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl2_36),
% 20.87/3.00    inference(avatar_component_clause,[],[f1173])).
% 20.87/3.00  fof(f1178,plain,(
% 20.87/3.00    ( ! [X33,X31,X32] : (k2_xboole_0(X33,X31) = k2_xboole_0(X31,k2_xboole_0(k4_xboole_0(X31,X32),X33))) ) | ~spl2_37),
% 20.87/3.00    inference(avatar_component_clause,[],[f1177])).
% 20.87/3.00  fof(f7035,plain,(
% 20.87/3.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X3,X4),X5))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_24 | ~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(forward_demodulation,[],[f7030,f31])).
% 20.87/3.00  fof(f31,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_1),
% 20.87/3.00    inference(avatar_component_clause,[],[f30])).
% 20.87/3.00  fof(f7030,plain,(
% 20.87/3.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),X3)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_24 | ~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(backward_demodulation,[],[f6985,f7024])).
% 20.87/3.00  fof(f7024,plain,(
% 20.87/3.00    ( ! [X88,X85] : (k4_xboole_0(X85,k4_xboole_0(X88,X85)) = X85) ) | (~spl2_1 | ~spl2_24 | ~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(forward_demodulation,[],[f7023,f742])).
% 20.87/3.00  fof(f742,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) ) | ~spl2_24),
% 20.87/3.00    inference(avatar_component_clause,[],[f741])).
% 20.87/3.00  fof(f7023,plain,(
% 20.87/3.00    ( ! [X88,X85] : (k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(X85,k4_xboole_0(X85,X88))) ) | (~spl2_1 | ~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(forward_demodulation,[],[f7022,f31])).
% 20.87/3.00  fof(f7022,plain,(
% 20.87/3.00    ( ! [X88,X85] : (k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(k4_xboole_0(X85,X88),X85)) ) | (~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(forward_demodulation,[],[f7021,f4212])).
% 20.87/3.00  fof(f4212,plain,(
% 20.87/3.00    ( ! [X41,X40] : (k4_xboole_0(X40,k4_xboole_0(X41,X41)) = X40) ) | ~spl2_70),
% 20.87/3.00    inference(avatar_component_clause,[],[f4211])).
% 20.87/3.00  fof(f7021,plain,(
% 20.87/3.00    ( ! [X88,X85,X86] : (k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(k4_xboole_0(X85,X88),k4_xboole_0(X85,k4_xboole_0(X86,X86)))) ) | (~spl2_26 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(forward_demodulation,[],[f6894,f790])).
% 20.87/3.00  fof(f790,plain,(
% 20.87/3.00    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,X7)) ) | ~spl2_26),
% 20.87/3.00    inference(avatar_component_clause,[],[f789])).
% 20.87/3.00  fof(f6894,plain,(
% 20.87/3.00    ( ! [X88,X87,X85,X86] : (k4_xboole_0(X85,k4_xboole_0(X88,X85)) = k2_xboole_0(k4_xboole_0(X85,X88),k4_xboole_0(X85,k4_xboole_0(k4_xboole_0(X86,X87),X86)))) ) | (~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(superposition,[],[f5900,f5648])).
% 20.87/3.00  fof(f5648,plain,(
% 20.87/3.00    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X10,X10)) ) | ~spl2_77),
% 20.87/3.00    inference(avatar_component_clause,[],[f5647])).
% 20.87/3.00  fof(f5900,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl2_78),
% 20.87/3.00    inference(avatar_component_clause,[],[f5899])).
% 20.87/3.00  fof(f6985,plain,(
% 20.87/3.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(X3,k4_xboole_0(X4,X3)))) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_78)),
% 20.87/3.00    inference(forward_demodulation,[],[f6870,f43])).
% 20.87/3.00  fof(f43,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) ) | (~spl2_2 | ~spl2_3)),
% 20.87/3.00    inference(superposition,[],[f39,f35])).
% 20.87/3.00  fof(f35,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_2),
% 20.87/3.00    inference(avatar_component_clause,[],[f34])).
% 20.87/3.00  fof(f39,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) ) | ~spl2_3),
% 20.87/3.00    inference(avatar_component_clause,[],[f38])).
% 20.87/3.00  fof(f6870,plain,(
% 20.87/3.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X3,X4),X5),k4_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X4,X3)))) ) | (~spl2_4 | ~spl2_78)),
% 20.87/3.00    inference(superposition,[],[f5900,f48])).
% 20.87/3.00  fof(f48,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | ~spl2_4),
% 20.87/3.00    inference(avatar_component_clause,[],[f47])).
% 20.87/3.00  fof(f43534,plain,(
% 20.87/3.00    spl2_195 | ~spl2_3 | ~spl2_27),
% 20.87/3.00    inference(avatar_split_clause,[],[f861,f810,f38,f43532])).
% 20.87/3.00  fof(f810,plain,(
% 20.87/3.00    spl2_27 <=> ! [X1,X0,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 20.87/3.00  fof(f861,plain,(
% 20.87/3.00    ( ! [X21,X19,X20] : (k4_xboole_0(k2_xboole_0(X19,X20),X21) = k4_xboole_0(k2_xboole_0(X20,k2_xboole_0(X19,X21)),X21)) ) | (~spl2_3 | ~spl2_27)),
% 20.87/3.00    inference(superposition,[],[f39,f811])).
% 20.87/3.00  fof(f811,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) ) | ~spl2_27),
% 20.87/3.00    inference(avatar_component_clause,[],[f810])).
% 20.87/3.00  fof(f39773,plain,(
% 20.87/3.00    spl2_188 | ~spl2_29 | ~spl2_181),
% 20.87/3.00    inference(avatar_split_clause,[],[f36151,f35163,f818,f39771])).
% 20.87/3.00  fof(f818,plain,(
% 20.87/3.00    spl2_29 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 20.87/3.00  fof(f36151,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4) ) | (~spl2_29 | ~spl2_181)),
% 20.87/3.00    inference(superposition,[],[f819,f35164])).
% 20.87/3.00  fof(f819,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | ~spl2_29),
% 20.87/3.00    inference(avatar_component_clause,[],[f818])).
% 20.87/3.00  fof(f35165,plain,(
% 20.87/3.00    spl2_181 | ~spl2_98 | ~spl2_154 | ~spl2_171),
% 20.87/3.00    inference(avatar_split_clause,[],[f30835,f30577,f18663,f7592,f35163])).
% 20.87/3.00  fof(f7592,plain,(
% 20.87/3.00    spl2_98 <=> ! [X1,X2] : k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 20.87/3.00  fof(f18663,plain,(
% 20.87/3.00    spl2_154 <=> ! [X115,X117,X116] : k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k4_xboole_0(X115,X117)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).
% 20.87/3.00  fof(f30577,plain,(
% 20.87/3.00    spl2_171 <=> ! [X25,X24] : k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25))) = X25),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).
% 20.87/3.00  fof(f30835,plain,(
% 20.87/3.00    ( ! [X116,X117] : (k4_xboole_0(X116,k4_xboole_0(X116,X117)) = k4_xboole_0(X117,k4_xboole_0(X117,X116))) ) | (~spl2_98 | ~spl2_154 | ~spl2_171)),
% 20.87/3.00    inference(forward_demodulation,[],[f30744,f18664])).
% 20.87/3.00  fof(f18664,plain,(
% 20.87/3.00    ( ! [X116,X117,X115] : (k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k4_xboole_0(X115,X117)) ) | ~spl2_154),
% 20.87/3.00    inference(avatar_component_clause,[],[f18663])).
% 20.87/3.00  fof(f30744,plain,(
% 20.87/3.00    ( ! [X116,X117] : (k4_xboole_0(X117,k4_xboole_0(X117,X116)) = k4_xboole_0(X116,k4_xboole_0(X116,k4_xboole_0(X117,k4_xboole_0(X117,X116))))) ) | (~spl2_98 | ~spl2_171)),
% 20.87/3.00    inference(superposition,[],[f7593,f30578])).
% 20.87/3.00  fof(f30578,plain,(
% 20.87/3.00    ( ! [X24,X25] : (k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25))) = X25) ) | ~spl2_171),
% 20.87/3.00    inference(avatar_component_clause,[],[f30577])).
% 20.87/3.00  fof(f7593,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1) ) | ~spl2_98),
% 20.87/3.00    inference(avatar_component_clause,[],[f7592])).
% 20.87/3.00  fof(f30579,plain,(
% 20.87/3.00    spl2_171 | ~spl2_2 | ~spl2_67 | ~spl2_170),
% 20.87/3.00    inference(avatar_split_clause,[],[f30560,f18727,f3858,f34,f30577])).
% 20.87/3.00  fof(f3858,plain,(
% 20.87/3.00    spl2_67 <=> ! [X77,X76] : k2_xboole_0(X76,k4_xboole_0(X77,X77)) = X76),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 20.87/3.00  fof(f18727,plain,(
% 20.87/3.00    spl2_170 <=> ! [X117,X116] : k4_xboole_0(X116,X116) = k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).
% 20.87/3.00  fof(f30560,plain,(
% 20.87/3.00    ( ! [X24,X25] : (k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25))) = X25) ) | (~spl2_2 | ~spl2_67 | ~spl2_170)),
% 20.87/3.00    inference(forward_demodulation,[],[f30434,f3859])).
% 20.87/3.00  fof(f3859,plain,(
% 20.87/3.00    ( ! [X76,X77] : (k2_xboole_0(X76,k4_xboole_0(X77,X77)) = X76) ) | ~spl2_67),
% 20.87/3.00    inference(avatar_component_clause,[],[f3858])).
% 20.87/3.00  fof(f30434,plain,(
% 20.87/3.00    ( ! [X24,X25] : (k2_xboole_0(X25,k4_xboole_0(X24,X24)) = k2_xboole_0(X25,k4_xboole_0(X24,k4_xboole_0(X24,X25)))) ) | (~spl2_2 | ~spl2_170)),
% 20.87/3.00    inference(superposition,[],[f35,f18728])).
% 20.87/3.00  fof(f18728,plain,(
% 20.87/3.00    ( ! [X116,X117] : (k4_xboole_0(X116,X116) = k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117)) ) | ~spl2_170),
% 20.87/3.00    inference(avatar_component_clause,[],[f18727])).
% 20.87/3.00  fof(f18729,plain,(
% 20.87/3.00    spl2_170 | ~spl2_52 | ~spl2_94 | ~spl2_104),
% 20.87/3.00    inference(avatar_split_clause,[],[f9208,f9079,f7088,f3033,f18727])).
% 20.87/3.00  fof(f3033,plain,(
% 20.87/3.00    spl2_52 <=> ! [X11,X13,X12] : k4_xboole_0(X11,X11) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 20.87/3.00  fof(f7088,plain,(
% 20.87/3.00    spl2_94 <=> ! [X85,X88] : k4_xboole_0(X85,k4_xboole_0(X88,X85)) = X85),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).
% 20.87/3.00  fof(f9079,plain,(
% 20.87/3.00    spl2_104 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 20.87/3.00  fof(f9208,plain,(
% 20.87/3.00    ( ! [X116,X117] : (k4_xboole_0(X116,X116) = k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117)) ) | (~spl2_52 | ~spl2_94 | ~spl2_104)),
% 20.87/3.00    inference(forward_demodulation,[],[f9177,f3034])).
% 20.87/3.00  fof(f3034,plain,(
% 20.87/3.00    ( ! [X12,X13,X11] : (k4_xboole_0(X11,X11) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11)) ) | ~spl2_52),
% 20.87/3.00    inference(avatar_component_clause,[],[f3033])).
% 20.87/3.00  fof(f9177,plain,(
% 20.87/3.00    ( ! [X116,X117] : (k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X116,k4_xboole_0(X116,X117)),X117),X116)) ) | (~spl2_94 | ~spl2_104)),
% 20.87/3.00    inference(superposition,[],[f7089,f9080])).
% 20.87/3.00  fof(f9080,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0) ) | ~spl2_104),
% 20.87/3.00    inference(avatar_component_clause,[],[f9079])).
% 20.87/3.00  fof(f7089,plain,(
% 20.87/3.00    ( ! [X88,X85] : (k4_xboole_0(X85,k4_xboole_0(X88,X85)) = X85) ) | ~spl2_94),
% 20.87/3.00    inference(avatar_component_clause,[],[f7088])).
% 20.87/3.00  fof(f18665,plain,(
% 20.87/3.00    spl2_154 | ~spl2_67 | ~spl2_78 | ~spl2_94),
% 20.87/3.00    inference(avatar_split_clause,[],[f7195,f7088,f5899,f3858,f18663])).
% 20.87/3.00  fof(f7195,plain,(
% 20.87/3.00    ( ! [X116,X117,X115] : (k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k4_xboole_0(X115,X117)) ) | (~spl2_67 | ~spl2_78 | ~spl2_94)),
% 20.87/3.00    inference(forward_demodulation,[],[f7161,f3859])).
% 20.87/3.00  fof(f7161,plain,(
% 20.87/3.00    ( ! [X116,X117,X115] : (k4_xboole_0(X115,k4_xboole_0(X117,k4_xboole_0(X116,X115))) = k2_xboole_0(k4_xboole_0(X115,X117),k4_xboole_0(X115,X115))) ) | (~spl2_78 | ~spl2_94)),
% 20.87/3.00    inference(superposition,[],[f5900,f7089])).
% 20.87/3.00  fof(f9081,plain,(
% 20.87/3.00    spl2_104 | ~spl2_13 | ~spl2_78),
% 20.87/3.00    inference(avatar_split_clause,[],[f6904,f5899,f154,f9079])).
% 20.87/3.00  fof(f154,plain,(
% 20.87/3.00    spl2_13 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 20.87/3.00  fof(f6904,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0) ) | (~spl2_13 | ~spl2_78)),
% 20.87/3.00    inference(superposition,[],[f5900,f155])).
% 20.87/3.00  fof(f155,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_13),
% 20.87/3.00    inference(avatar_component_clause,[],[f154])).
% 20.87/3.00  fof(f7594,plain,(
% 20.87/3.00    spl2_98 | ~spl2_1 | ~spl2_95),
% 20.87/3.00    inference(avatar_split_clause,[],[f7205,f7197,f30,f7592])).
% 20.87/3.00  fof(f7197,plain,(
% 20.87/3.00    spl2_95 <=> ! [X5,X4] : k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 20.87/3.00  fof(f7205,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) = X1) ) | (~spl2_1 | ~spl2_95)),
% 20.87/3.00    inference(superposition,[],[f7198,f31])).
% 20.87/3.00  fof(f7198,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4) ) | ~spl2_95),
% 20.87/3.00    inference(avatar_component_clause,[],[f7197])).
% 20.87/3.00  fof(f7199,plain,(
% 20.87/3.00    spl2_95 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_24 | ~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78),
% 20.87/3.00    inference(avatar_split_clause,[],[f7025,f5899,f5647,f4211,f789,f741,f38,f34,f30,f7197])).
% 20.87/3.00  fof(f7025,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_24 | ~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78)),
% 20.87/3.00    inference(backward_demodulation,[],[f43,f7024])).
% 20.87/3.00  fof(f7090,plain,(
% 20.87/3.00    spl2_94 | ~spl2_1 | ~spl2_24 | ~spl2_26 | ~spl2_70 | ~spl2_77 | ~spl2_78),
% 20.87/3.00    inference(avatar_split_clause,[],[f7024,f5899,f5647,f4211,f789,f741,f30,f7088])).
% 20.87/3.00  fof(f5901,plain,(
% 20.87/3.00    spl2_78),
% 20.87/3.00    inference(avatar_split_clause,[],[f28,f5899])).
% 20.87/3.00  fof(f28,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 20.87/3.00    inference(definition_unfolding,[],[f23,f17])).
% 20.87/3.00  fof(f17,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 20.87/3.00    inference(cnf_transformation,[],[f6])).
% 20.87/3.00  fof(f6,axiom,(
% 20.87/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 20.87/3.00  fof(f23,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 20.87/3.00    inference(cnf_transformation,[],[f9])).
% 20.87/3.00  fof(f9,axiom,(
% 20.87/3.00    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 20.87/3.00  fof(f5649,plain,(
% 20.87/3.00    spl2_77 | ~spl2_55 | ~spl2_72),
% 20.87/3.00    inference(avatar_split_clause,[],[f5560,f4463,f3045,f5647])).
% 20.87/3.00  fof(f3045,plain,(
% 20.87/3.00    spl2_55 <=> ! [X18,X17,X19] : k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(X18,X17)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 20.87/3.00  fof(f4463,plain,(
% 20.87/3.00    spl2_72 <=> ! [X16,X15,X14] : k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X16,X16),X14)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 20.87/3.00  fof(f5560,plain,(
% 20.87/3.00    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X10,X10)) ) | (~spl2_55 | ~spl2_72)),
% 20.87/3.00    inference(superposition,[],[f3046,f4464])).
% 20.87/3.00  fof(f4464,plain,(
% 20.87/3.00    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X16,X16),X14)) ) | ~spl2_72),
% 20.87/3.00    inference(avatar_component_clause,[],[f4463])).
% 20.87/3.00  fof(f3046,plain,(
% 20.87/3.00    ( ! [X19,X17,X18] : (k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(X18,X17)) ) | ~spl2_55),
% 20.87/3.00    inference(avatar_component_clause,[],[f3045])).
% 20.87/3.00  fof(f4465,plain,(
% 20.87/3.00    spl2_72 | ~spl2_69 | ~spl2_71),
% 20.87/3.00    inference(avatar_split_clause,[],[f4303,f4295,f4085,f4463])).
% 20.87/3.00  fof(f4085,plain,(
% 20.87/3.00    spl2_69 <=> ! [X55,X56] : k4_xboole_0(X56,X56) = k4_xboole_0(X55,X55)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 20.87/3.00  fof(f4295,plain,(
% 20.87/3.00    spl2_71 <=> ! [X73,X72] : k4_xboole_0(X72,X72) = k4_xboole_0(k4_xboole_0(X73,X73),X72)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 20.87/3.00  fof(f4303,plain,(
% 20.87/3.00    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X16,X16),X14)) ) | (~spl2_69 | ~spl2_71)),
% 20.87/3.00    inference(superposition,[],[f4296,f4086])).
% 20.87/3.00  fof(f4086,plain,(
% 20.87/3.00    ( ! [X56,X55] : (k4_xboole_0(X56,X56) = k4_xboole_0(X55,X55)) ) | ~spl2_69),
% 20.87/3.00    inference(avatar_component_clause,[],[f4085])).
% 20.87/3.00  fof(f4296,plain,(
% 20.87/3.00    ( ! [X72,X73] : (k4_xboole_0(X72,X72) = k4_xboole_0(k4_xboole_0(X73,X73),X72)) ) | ~spl2_71),
% 20.87/3.00    inference(avatar_component_clause,[],[f4295])).
% 20.87/3.00  fof(f4297,plain,(
% 20.87/3.00    spl2_71 | ~spl2_52 | ~spl2_65),
% 20.87/3.00    inference(avatar_split_clause,[],[f3782,f3692,f3033,f4295])).
% 20.87/3.00  fof(f3692,plain,(
% 20.87/3.00    spl2_65 <=> ! [X3,X2] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 20.87/3.00  fof(f3782,plain,(
% 20.87/3.00    ( ! [X72,X73] : (k4_xboole_0(X72,X72) = k4_xboole_0(k4_xboole_0(X73,X73),X72)) ) | (~spl2_52 | ~spl2_65)),
% 20.87/3.00    inference(superposition,[],[f3034,f3693])).
% 20.87/3.00  fof(f3693,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))) ) | ~spl2_65),
% 20.87/3.00    inference(avatar_component_clause,[],[f3692])).
% 20.87/3.00  fof(f4213,plain,(
% 20.87/3.00    spl2_70 | ~spl2_20 | ~spl2_40 | ~spl2_65 | ~spl2_67),
% 20.87/3.00    inference(avatar_split_clause,[],[f3939,f3858,f3692,f1499,f482,f4211])).
% 20.87/3.00  fof(f482,plain,(
% 20.87/3.00    spl2_20 <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 20.87/3.00  fof(f1499,plain,(
% 20.87/3.00    spl2_40 <=> ! [X20,X22,X21] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),X20) = X20),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 20.87/3.00  fof(f3939,plain,(
% 20.87/3.00    ( ! [X41,X40] : (k4_xboole_0(X40,k4_xboole_0(X41,X41)) = X40) ) | (~spl2_20 | ~spl2_40 | ~spl2_65 | ~spl2_67)),
% 20.87/3.00    inference(forward_demodulation,[],[f3876,f3783])).
% 20.87/3.00  fof(f3783,plain,(
% 20.87/3.00    ( ! [X74,X75] : (k2_xboole_0(k4_xboole_0(X75,X75),X74) = X74) ) | (~spl2_40 | ~spl2_65)),
% 20.87/3.00    inference(superposition,[],[f1500,f3693])).
% 20.87/3.00  fof(f1500,plain,(
% 20.87/3.00    ( ! [X21,X22,X20] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),X20) = X20) ) | ~spl2_40),
% 20.87/3.00    inference(avatar_component_clause,[],[f1499])).
% 20.87/3.00  fof(f3876,plain,(
% 20.87/3.00    ( ! [X41,X40] : (k4_xboole_0(X40,k4_xboole_0(X41,X41)) = k2_xboole_0(k4_xboole_0(X41,X41),X40)) ) | (~spl2_20 | ~spl2_67)),
% 20.87/3.00    inference(superposition,[],[f3859,f483])).
% 20.87/3.00  fof(f483,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5)) ) | ~spl2_20),
% 20.87/3.00    inference(avatar_component_clause,[],[f482])).
% 20.87/3.00  fof(f4087,plain,(
% 20.87/3.00    spl2_69 | ~spl2_67 | ~spl2_68),
% 20.87/3.00    inference(avatar_split_clause,[],[f3995,f3971,f3858,f4085])).
% 20.87/3.00  fof(f3971,plain,(
% 20.87/3.00    spl2_68 <=> ! [X75,X74] : k2_xboole_0(k4_xboole_0(X75,X75),X74) = X74),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 20.87/3.00  fof(f3995,plain,(
% 20.87/3.00    ( ! [X56,X55] : (k4_xboole_0(X56,X56) = k4_xboole_0(X55,X55)) ) | (~spl2_67 | ~spl2_68)),
% 20.87/3.00    inference(superposition,[],[f3972,f3859])).
% 20.87/3.00  fof(f3972,plain,(
% 20.87/3.00    ( ! [X74,X75] : (k2_xboole_0(k4_xboole_0(X75,X75),X74) = X74) ) | ~spl2_68),
% 20.87/3.00    inference(avatar_component_clause,[],[f3971])).
% 20.87/3.00  fof(f3973,plain,(
% 20.87/3.00    spl2_68 | ~spl2_40 | ~spl2_65),
% 20.87/3.00    inference(avatar_split_clause,[],[f3783,f3692,f1499,f3971])).
% 20.87/3.00  fof(f3860,plain,(
% 20.87/3.00    spl2_67 | ~spl2_39 | ~spl2_65),
% 20.87/3.00    inference(avatar_split_clause,[],[f3784,f3692,f1460,f3858])).
% 20.87/3.00  fof(f1460,plain,(
% 20.87/3.00    spl2_39 <=> ! [X44,X43,X45] : k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45)) = X43),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 20.87/3.00  fof(f3784,plain,(
% 20.87/3.00    ( ! [X76,X77] : (k2_xboole_0(X76,k4_xboole_0(X77,X77)) = X76) ) | (~spl2_39 | ~spl2_65)),
% 20.87/3.00    inference(superposition,[],[f1461,f3693])).
% 20.87/3.00  fof(f1461,plain,(
% 20.87/3.00    ( ! [X45,X43,X44] : (k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45)) = X43) ) | ~spl2_39),
% 20.87/3.00    inference(avatar_component_clause,[],[f1460])).
% 20.87/3.00  fof(f3694,plain,(
% 20.87/3.00    spl2_65 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_26 | ~spl2_59),
% 20.87/3.00    inference(avatar_split_clause,[],[f3190,f3136,f789,f76,f47,f38,f3692])).
% 20.87/3.00  fof(f76,plain,(
% 20.87/3.00    spl2_7 <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 20.87/3.00  fof(f3136,plain,(
% 20.87/3.00    spl2_59 <=> ! [X5,X6] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 20.87/3.00  fof(f3190,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))) ) | (~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_26 | ~spl2_59)),
% 20.87/3.00    inference(backward_demodulation,[],[f804,f3187])).
% 20.87/3.00  fof(f3187,plain,(
% 20.87/3.00    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5)) ) | (~spl2_3 | ~spl2_7 | ~spl2_59)),
% 20.87/3.00    inference(backward_demodulation,[],[f88,f3186])).
% 20.87/3.00  fof(f3186,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_59)),
% 20.87/3.00    inference(forward_demodulation,[],[f3143,f3137])).
% 20.87/3.00  fof(f3137,plain,(
% 20.87/3.00    ( ! [X6,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) ) | ~spl2_59),
% 20.87/3.00    inference(avatar_component_clause,[],[f3136])).
% 20.87/3.00  fof(f3143,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_59)),
% 20.87/3.00    inference(superposition,[],[f3137,f39])).
% 20.87/3.00  fof(f88,plain,(
% 20.87/3.00    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) ) | (~spl2_3 | ~spl2_7)),
% 20.87/3.00    inference(superposition,[],[f39,f77])).
% 20.87/3.00  fof(f77,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) ) | ~spl2_7),
% 20.87/3.00    inference(avatar_component_clause,[],[f76])).
% 20.87/3.00  fof(f804,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_26)),
% 20.87/3.00    inference(forward_demodulation,[],[f793,f88])).
% 20.87/3.00  fof(f793,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))) ) | (~spl2_4 | ~spl2_26)),
% 20.87/3.00    inference(superposition,[],[f790,f48])).
% 20.87/3.00  fof(f3138,plain,(
% 20.87/3.00    spl2_59 | ~spl2_12 | ~spl2_26 | ~spl2_50 | ~spl2_52),
% 20.87/3.00    inference(avatar_split_clause,[],[f3115,f3033,f2822,f789,f150,f3136])).
% 20.87/3.00  fof(f150,plain,(
% 20.87/3.00    spl2_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 20.87/3.00  fof(f2822,plain,(
% 20.87/3.00    spl2_50 <=> ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = X11),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 20.87/3.00  fof(f3115,plain,(
% 20.87/3.00    ( ! [X6,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) ) | (~spl2_12 | ~spl2_26 | ~spl2_50 | ~spl2_52)),
% 20.87/3.00    inference(backward_demodulation,[],[f798,f3079])).
% 20.87/3.00  fof(f3079,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X2))) ) | (~spl2_50 | ~spl2_52)),
% 20.87/3.00    inference(superposition,[],[f2823,f3034])).
% 20.87/3.00  fof(f2823,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = X11) ) | ~spl2_50),
% 20.87/3.00    inference(avatar_component_clause,[],[f2822])).
% 20.87/3.00  fof(f798,plain,(
% 20.87/3.00    ( ! [X6,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X5)))) ) | (~spl2_12 | ~spl2_26)),
% 20.87/3.00    inference(superposition,[],[f151,f790])).
% 20.87/3.00  fof(f151,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_12),
% 20.87/3.00    inference(avatar_component_clause,[],[f150])).
% 20.87/3.00  fof(f3060,plain,(
% 20.87/3.00    ~spl2_58),
% 20.87/3.00    inference(avatar_split_clause,[],[f25,f3057])).
% 20.87/3.00  fof(f25,plain,(
% 20.87/3.00    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 20.87/3.00    inference(definition_unfolding,[],[f15,f17])).
% 20.87/3.00  fof(f15,plain,(
% 20.87/3.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 20.87/3.00    inference(cnf_transformation,[],[f14])).
% 20.87/3.00  fof(f14,plain,(
% 20.87/3.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 20.87/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 20.87/3.00  fof(f13,plain,(
% 20.87/3.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 20.87/3.00    introduced(choice_axiom,[])).
% 20.87/3.00  fof(f12,plain,(
% 20.87/3.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 20.87/3.00    inference(ennf_transformation,[],[f11])).
% 20.87/3.00  fof(f11,negated_conjecture,(
% 20.87/3.00    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 20.87/3.00    inference(negated_conjecture,[],[f10])).
% 20.87/3.00  fof(f10,conjecture,(
% 20.87/3.00    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 20.87/3.00  fof(f3047,plain,(
% 20.87/3.00    spl2_55 | ~spl2_4 | ~spl2_44),
% 20.87/3.00    inference(avatar_split_clause,[],[f2491,f2170,f47,f3045])).
% 20.87/3.00  fof(f2170,plain,(
% 20.87/3.00    spl2_44 <=> ! [X40,X42,X41] : k2_xboole_0(X40,X42) = k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41)))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 20.87/3.00  fof(f2491,plain,(
% 20.87/3.00    ( ! [X19,X17,X18] : (k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(X18,X17)) ) | (~spl2_4 | ~spl2_44)),
% 20.87/3.00    inference(forward_demodulation,[],[f2455,f48])).
% 20.87/3.00  fof(f2455,plain,(
% 20.87/3.00    ( ! [X19,X17,X18] : (k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X17,X19)),X17) = k4_xboole_0(k2_xboole_0(X17,X18),X17)) ) | (~spl2_4 | ~spl2_44)),
% 20.87/3.00    inference(superposition,[],[f48,f2171])).
% 20.87/3.00  fof(f2171,plain,(
% 20.87/3.00    ( ! [X41,X42,X40] : (k2_xboole_0(X40,X42) = k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41)))) ) | ~spl2_44),
% 20.87/3.00    inference(avatar_component_clause,[],[f2170])).
% 20.87/3.00  fof(f3035,plain,(
% 20.87/3.00    spl2_52 | ~spl2_4 | ~spl2_39),
% 20.87/3.00    inference(avatar_split_clause,[],[f1475,f1460,f47,f3033])).
% 20.87/3.00  fof(f1475,plain,(
% 20.87/3.00    ( ! [X12,X13,X11] : (k4_xboole_0(X11,X11) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11)) ) | (~spl2_4 | ~spl2_39)),
% 20.87/3.00    inference(superposition,[],[f48,f1461])).
% 20.87/3.00  fof(f2824,plain,(
% 20.87/3.00    spl2_50 | ~spl2_1 | ~spl2_2 | ~spl2_23 | ~spl2_42 | ~spl2_47),
% 20.87/3.00    inference(avatar_split_clause,[],[f2793,f2182,f2162,f724,f34,f30,f2822])).
% 20.87/3.00  fof(f724,plain,(
% 20.87/3.00    spl2_23 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 20.87/3.00  fof(f2162,plain,(
% 20.87/3.00    spl2_42 <=> ! [X11,X12] : k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X11))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 20.87/3.00  fof(f2182,plain,(
% 20.87/3.00    spl2_47 <=> ! [X55,X56,X57] : k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,X57)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 20.87/3.00  fof(f2793,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = X11) ) | (~spl2_1 | ~spl2_2 | ~spl2_23 | ~spl2_42 | ~spl2_47)),
% 20.87/3.00    inference(forward_demodulation,[],[f2792,f725])).
% 20.87/3.00  fof(f725,plain,(
% 20.87/3.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_23),
% 20.87/3.00    inference(avatar_component_clause,[],[f724])).
% 20.87/3.00  fof(f2792,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k2_xboole_0(X11,X11) = k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12))) ) | (~spl2_1 | ~spl2_2 | ~spl2_42 | ~spl2_47)),
% 20.87/3.00    inference(forward_demodulation,[],[f2791,f35])).
% 20.87/3.00  fof(f2791,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,X11)) = k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12))) ) | (~spl2_1 | ~spl2_42 | ~spl2_47)),
% 20.87/3.00    inference(forward_demodulation,[],[f2736,f31])).
% 20.87/3.00  fof(f2736,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,X11),X12)) = k2_xboole_0(k4_xboole_0(X11,X11),X11)) ) | (~spl2_42 | ~spl2_47)),
% 20.87/3.00    inference(superposition,[],[f2183,f2163])).
% 20.87/3.00  fof(f2163,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X11))) ) | ~spl2_42),
% 20.87/3.00    inference(avatar_component_clause,[],[f2162])).
% 20.87/3.00  fof(f2183,plain,(
% 20.87/3.00    ( ! [X57,X56,X55] : (k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,X57)) ) | ~spl2_47),
% 20.87/3.00    inference(avatar_component_clause,[],[f2182])).
% 20.87/3.00  fof(f2184,plain,(
% 20.87/3.00    spl2_47 | ~spl2_2 | ~spl2_33 | ~spl2_37),
% 20.87/3.00    inference(avatar_split_clause,[],[f2041,f1177,f1161,f34,f2182])).
% 20.87/3.00  fof(f1161,plain,(
% 20.87/3.00    spl2_33 <=> ! [X20,X19,X21] : k2_xboole_0(X19,X21) = k2_xboole_0(X19,k2_xboole_0(k4_xboole_0(X19,X20),X21))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 20.87/3.00  fof(f2041,plain,(
% 20.87/3.00    ( ! [X57,X56,X55] : (k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,X57)) ) | (~spl2_2 | ~spl2_33 | ~spl2_37)),
% 20.87/3.00    inference(forward_demodulation,[],[f1991,f1162])).
% 20.87/3.00  fof(f1162,plain,(
% 20.87/3.00    ( ! [X21,X19,X20] : (k2_xboole_0(X19,X21) = k2_xboole_0(X19,k2_xboole_0(k4_xboole_0(X19,X20),X21))) ) | ~spl2_33),
% 20.87/3.00    inference(avatar_component_clause,[],[f1161])).
% 20.87/3.00  fof(f1991,plain,(
% 20.87/3.00    ( ! [X57,X56,X55] : (k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X55,X56)),X55) = k2_xboole_0(X55,k2_xboole_0(k4_xboole_0(X55,X56),X57))) ) | (~spl2_2 | ~spl2_37)),
% 20.87/3.00    inference(superposition,[],[f1178,f35])).
% 20.87/3.00  fof(f2172,plain,(
% 20.87/3.00    spl2_44 | ~spl2_2 | ~spl2_33),
% 20.87/3.00    inference(avatar_split_clause,[],[f1432,f1161,f34,f2170])).
% 20.87/3.00  fof(f1432,plain,(
% 20.87/3.00    ( ! [X41,X42,X40] : (k2_xboole_0(X40,X42) = k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41)))) ) | (~spl2_2 | ~spl2_33)),
% 20.87/3.00    inference(forward_demodulation,[],[f1398,f1162])).
% 20.87/3.00  fof(f1398,plain,(
% 20.87/3.00    ( ! [X41,X42,X40] : (k2_xboole_0(X40,k4_xboole_0(X42,k4_xboole_0(X40,X41))) = k2_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X41),X42))) ) | (~spl2_2 | ~spl2_33)),
% 20.87/3.00    inference(superposition,[],[f1162,f35])).
% 20.87/3.00  fof(f2164,plain,(
% 20.87/3.00    spl2_42 | ~spl2_24 | ~spl2_26),
% 20.87/3.00    inference(avatar_split_clause,[],[f801,f789,f741,f2162])).
% 20.87/3.00  fof(f801,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X11))) ) | (~spl2_24 | ~spl2_26)),
% 20.87/3.00    inference(superposition,[],[f742,f790])).
% 20.87/3.00  fof(f1501,plain,(
% 20.87/3.00    spl2_40 | ~spl2_8 | ~spl2_39),
% 20.87/3.00    inference(avatar_split_clause,[],[f1477,f1460,f92,f1499])).
% 20.87/3.00  fof(f92,plain,(
% 20.87/3.00    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 20.87/3.00  fof(f1477,plain,(
% 20.87/3.00    ( ! [X21,X22,X20] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),X20) = X20) ) | (~spl2_8 | ~spl2_39)),
% 20.87/3.00    inference(superposition,[],[f93,f1461])).
% 20.87/3.00  fof(f93,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) ) | ~spl2_8),
% 20.87/3.00    inference(avatar_component_clause,[],[f92])).
% 20.87/3.00  fof(f1462,plain,(
% 20.87/3.00    spl2_39 | ~spl2_24 | ~spl2_33),
% 20.87/3.00    inference(avatar_split_clause,[],[f1433,f1161,f741,f1460])).
% 20.87/3.00  fof(f1433,plain,(
% 20.87/3.00    ( ! [X45,X43,X44] : (k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45)) = X43) ) | (~spl2_24 | ~spl2_33)),
% 20.87/3.00    inference(forward_demodulation,[],[f1399,f742])).
% 20.87/3.00  fof(f1399,plain,(
% 20.87/3.00    ( ! [X45,X43,X44] : (k2_xboole_0(X43,k4_xboole_0(X43,X44)) = k2_xboole_0(X43,k4_xboole_0(k4_xboole_0(X43,X44),X45))) ) | (~spl2_24 | ~spl2_33)),
% 20.87/3.00    inference(superposition,[],[f1162,f742])).
% 20.87/3.00  fof(f1179,plain,(
% 20.87/3.00    spl2_37 | ~spl2_24 | ~spl2_28),
% 20.87/3.00    inference(avatar_split_clause,[],[f925,f814,f741,f1177])).
% 20.87/3.00  fof(f814,plain,(
% 20.87/3.00    spl2_28 <=> ! [X9,X7,X8] : k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 20.87/3.00  fof(f925,plain,(
% 20.87/3.00    ( ! [X33,X31,X32] : (k2_xboole_0(X33,X31) = k2_xboole_0(X31,k2_xboole_0(k4_xboole_0(X31,X32),X33))) ) | (~spl2_24 | ~spl2_28)),
% 20.87/3.00    inference(superposition,[],[f815,f742])).
% 20.87/3.00  fof(f815,plain,(
% 20.87/3.00    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))) ) | ~spl2_28),
% 20.87/3.00    inference(avatar_component_clause,[],[f814])).
% 20.87/3.00  fof(f1175,plain,(
% 20.87/3.00    spl2_36),
% 20.87/3.00    inference(avatar_split_clause,[],[f24,f1173])).
% 20.87/3.00  fof(f24,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 20.87/3.00    inference(cnf_transformation,[],[f4])).
% 20.87/3.00  fof(f4,axiom,(
% 20.87/3.00    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 20.87/3.00  fof(f1163,plain,(
% 20.87/3.00    spl2_33 | ~spl2_11 | ~spl2_24),
% 20.87/3.00    inference(avatar_split_clause,[],[f756,f741,f146,f1161])).
% 20.87/3.00  fof(f146,plain,(
% 20.87/3.00    spl2_11 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 20.87/3.00  fof(f756,plain,(
% 20.87/3.00    ( ! [X21,X19,X20] : (k2_xboole_0(X19,X21) = k2_xboole_0(X19,k2_xboole_0(k4_xboole_0(X19,X20),X21))) ) | (~spl2_11 | ~spl2_24)),
% 20.87/3.00    inference(superposition,[],[f147,f742])).
% 20.87/3.00  fof(f147,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_11),
% 20.87/3.00    inference(avatar_component_clause,[],[f146])).
% 20.87/3.00  fof(f820,plain,(
% 20.87/3.00    spl2_29 | ~spl2_12 | ~spl2_13),
% 20.87/3.00    inference(avatar_split_clause,[],[f676,f154,f150,f818])).
% 20.87/3.00  fof(f676,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | (~spl2_12 | ~spl2_13)),
% 20.87/3.00    inference(superposition,[],[f155,f151])).
% 20.87/3.00  fof(f816,plain,(
% 20.87/3.00    spl2_28 | ~spl2_1 | ~spl2_11),
% 20.87/3.00    inference(avatar_split_clause,[],[f168,f146,f30,f814])).
% 20.87/3.00  fof(f168,plain,(
% 20.87/3.00    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))) ) | (~spl2_1 | ~spl2_11)),
% 20.87/3.00    inference(superposition,[],[f147,f31])).
% 20.87/3.00  fof(f812,plain,(
% 20.87/3.00    spl2_27 | ~spl2_1 | ~spl2_11),
% 20.87/3.00    inference(avatar_split_clause,[],[f157,f146,f30,f810])).
% 20.87/3.00  fof(f157,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) ) | (~spl2_1 | ~spl2_11)),
% 20.87/3.00    inference(superposition,[],[f147,f31])).
% 20.87/3.00  fof(f791,plain,(
% 20.87/3.00    spl2_26 | ~spl2_4 | ~spl2_24),
% 20.87/3.00    inference(avatar_split_clause,[],[f751,f741,f47,f789])).
% 20.87/3.00  fof(f751,plain,(
% 20.87/3.00    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,X7)) ) | (~spl2_4 | ~spl2_24)),
% 20.87/3.00    inference(superposition,[],[f48,f742])).
% 20.87/3.00  fof(f743,plain,(
% 20.87/3.00    spl2_24 | ~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_13 | ~spl2_20),
% 20.87/3.00    inference(avatar_split_clause,[],[f716,f482,f154,f150,f34,f30,f741])).
% 20.87/3.00  fof(f716,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) ) | (~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_13 | ~spl2_20)),
% 20.87/3.00    inference(backward_demodulation,[],[f672,f682])).
% 20.87/3.00  fof(f682,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) ) | (~spl2_13 | ~spl2_20)),
% 20.87/3.00    inference(superposition,[],[f155,f483])).
% 20.87/3.00  fof(f672,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X4) = k2_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_20)),
% 20.87/3.00    inference(forward_demodulation,[],[f671,f31])).
% 20.87/3.00  fof(f671,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X4) = k2_xboole_0(k4_xboole_0(X4,X5),X4)) ) | (~spl2_2 | ~spl2_12 | ~spl2_20)),
% 20.87/3.00    inference(forward_demodulation,[],[f661,f483])).
% 20.87/3.00  fof(f661,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X4) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5))) ) | (~spl2_2 | ~spl2_12)),
% 20.87/3.00    inference(superposition,[],[f35,f151])).
% 20.87/3.00  fof(f726,plain,(
% 20.87/3.00    spl2_23 | ~spl2_13 | ~spl2_16),
% 20.87/3.00    inference(avatar_split_clause,[],[f700,f251,f154,f724])).
% 20.87/3.00  fof(f251,plain,(
% 20.87/3.00    spl2_16 <=> ! [X9,X10] : k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(X10,X9)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 20.87/3.00  fof(f700,plain,(
% 20.87/3.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | (~spl2_13 | ~spl2_16)),
% 20.87/3.00    inference(forward_demodulation,[],[f699,f155])).
% 20.87/3.00  fof(f699,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X0)) ) | (~spl2_13 | ~spl2_16)),
% 20.87/3.00    inference(forward_demodulation,[],[f675,f252])).
% 20.87/3.00  fof(f252,plain,(
% 20.87/3.00    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(X10,X9)) ) | ~spl2_16),
% 20.87/3.00    inference(avatar_component_clause,[],[f251])).
% 20.87/3.00  fof(f675,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X1)),k4_xboole_0(k2_xboole_0(X0,X0),X1))) ) | (~spl2_13 | ~spl2_16)),
% 20.87/3.00    inference(superposition,[],[f155,f252])).
% 20.87/3.00  fof(f484,plain,(
% 20.87/3.00    spl2_20 | ~spl2_2 | ~spl2_7 | ~spl2_17),
% 20.87/3.00    inference(avatar_split_clause,[],[f354,f317,f76,f34,f482])).
% 20.87/3.00  fof(f317,plain,(
% 20.87/3.00    spl2_17 <=> ! [X3,X2] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 20.87/3.00  fof(f354,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5)) ) | (~spl2_2 | ~spl2_7 | ~spl2_17)),
% 20.87/3.00    inference(forward_demodulation,[],[f330,f77])).
% 20.87/3.00  fof(f330,plain,(
% 20.87/3.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,k2_xboole_0(X4,X5))) ) | (~spl2_2 | ~spl2_17)),
% 20.87/3.00    inference(superposition,[],[f318,f35])).
% 20.87/3.00  fof(f318,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) ) | ~spl2_17),
% 20.87/3.00    inference(avatar_component_clause,[],[f317])).
% 20.87/3.00  fof(f319,plain,(
% 20.87/3.00    spl2_17 | ~spl2_11 | ~spl2_15),
% 20.87/3.00    inference(avatar_split_clause,[],[f257,f247,f146,f317])).
% 20.87/3.00  fof(f247,plain,(
% 20.87/3.00    spl2_15 <=> ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X6),X5)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 20.87/3.00  fof(f257,plain,(
% 20.87/3.00    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_11 | ~spl2_15)),
% 20.87/3.00    inference(superposition,[],[f248,f147])).
% 20.87/3.00  fof(f248,plain,(
% 20.87/3.00    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X6),X5)) ) | ~spl2_15),
% 20.87/3.00    inference(avatar_component_clause,[],[f247])).
% 20.87/3.00  fof(f253,plain,(
% 20.87/3.00    spl2_16 | ~spl2_4 | ~spl2_14),
% 20.87/3.00    inference(avatar_split_clause,[],[f239,f211,f47,f251])).
% 20.87/3.00  fof(f211,plain,(
% 20.87/3.00    spl2_14 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 20.87/3.00  fof(f239,plain,(
% 20.87/3.00    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(X10,X9)) ) | (~spl2_4 | ~spl2_14)),
% 20.87/3.00    inference(forward_demodulation,[],[f224,f48])).
% 20.87/3.00  fof(f224,plain,(
% 20.87/3.00    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X10,X10),X9) = k4_xboole_0(k2_xboole_0(X9,X10),X9)) ) | (~spl2_4 | ~spl2_14)),
% 20.87/3.00    inference(superposition,[],[f48,f212])).
% 20.87/3.00  fof(f212,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1))) ) | ~spl2_14),
% 20.87/3.00    inference(avatar_component_clause,[],[f211])).
% 20.87/3.00  fof(f249,plain,(
% 20.87/3.00    spl2_15 | ~spl2_1 | ~spl2_14),
% 20.87/3.00    inference(avatar_split_clause,[],[f216,f211,f30,f247])).
% 20.87/3.00  fof(f216,plain,(
% 20.87/3.00    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X6),X5)) ) | (~spl2_1 | ~spl2_14)),
% 20.87/3.00    inference(superposition,[],[f212,f31])).
% 20.87/3.00  fof(f213,plain,(
% 20.87/3.00    spl2_14 | ~spl2_9 | ~spl2_11),
% 20.87/3.00    inference(avatar_split_clause,[],[f166,f146,f108,f211])).
% 20.87/3.00  fof(f108,plain,(
% 20.87/3.00    spl2_9 <=> ! [X11,X12] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 20.87/3.00  fof(f166,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1))) ) | (~spl2_9 | ~spl2_11)),
% 20.87/3.00    inference(superposition,[],[f147,f109])).
% 20.87/3.00  fof(f109,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)) ) | ~spl2_9),
% 20.87/3.00    inference(avatar_component_clause,[],[f108])).
% 20.87/3.00  fof(f156,plain,(
% 20.87/3.00    spl2_13),
% 20.87/3.00    inference(avatar_split_clause,[],[f27,f154])).
% 20.87/3.00  fof(f27,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 20.87/3.00    inference(definition_unfolding,[],[f21,f17])).
% 20.87/3.00  fof(f21,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 20.87/3.00    inference(cnf_transformation,[],[f8])).
% 20.87/3.00  fof(f8,axiom,(
% 20.87/3.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 20.87/3.00  fof(f152,plain,(
% 20.87/3.00    spl2_12),
% 20.87/3.00    inference(avatar_split_clause,[],[f26,f150])).
% 20.87/3.00  fof(f26,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 20.87/3.00    inference(definition_unfolding,[],[f19,f17])).
% 20.87/3.00  fof(f19,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 20.87/3.00    inference(cnf_transformation,[],[f5])).
% 20.87/3.00  fof(f5,axiom,(
% 20.87/3.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 20.87/3.00  fof(f148,plain,(
% 20.87/3.00    spl2_11),
% 20.87/3.00    inference(avatar_split_clause,[],[f22,f146])).
% 20.87/3.00  fof(f22,plain,(
% 20.87/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 20.87/3.00    inference(cnf_transformation,[],[f7])).
% 20.87/3.00  fof(f7,axiom,(
% 20.87/3.00    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 20.87/3.00  fof(f110,plain,(
% 20.87/3.00    spl2_9 | ~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_8),
% 20.87/3.00    inference(avatar_split_clause,[],[f106,f92,f76,f51,f30,f108])).
% 20.87/3.00  fof(f51,plain,(
% 20.87/3.00    spl2_5 <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))),
% 20.87/3.00    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 20.87/3.00  fof(f106,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)) ) | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_8)),
% 20.87/3.00    inference(forward_demodulation,[],[f104,f90])).
% 20.87/3.00  fof(f90,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ) | (~spl2_1 | ~spl2_5 | ~spl2_7)),
% 20.87/3.00    inference(forward_demodulation,[],[f89,f77])).
% 20.87/3.00  fof(f89,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ) | (~spl2_1 | ~spl2_5 | ~spl2_7)),
% 20.87/3.00    inference(forward_demodulation,[],[f87,f31])).
% 20.87/3.00  fof(f87,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ) | (~spl2_5 | ~spl2_7)),
% 20.87/3.00    inference(superposition,[],[f52,f77])).
% 20.87/3.00  fof(f52,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | ~spl2_5),
% 20.87/3.00    inference(avatar_component_clause,[],[f51])).
% 20.87/3.00  fof(f104,plain,(
% 20.87/3.00    ( ! [X12,X11] : (k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X12,X11))) ) | (~spl2_5 | ~spl2_8)),
% 20.87/3.00    inference(superposition,[],[f52,f93])).
% 20.87/3.00  fof(f94,plain,(
% 20.87/3.00    spl2_8 | ~spl2_1 | ~spl2_7),
% 20.87/3.00    inference(avatar_split_clause,[],[f82,f76,f30,f92])).
% 20.87/3.00  fof(f82,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) ) | (~spl2_1 | ~spl2_7)),
% 20.87/3.00    inference(superposition,[],[f77,f31])).
% 20.87/3.00  fof(f78,plain,(
% 20.87/3.00    spl2_7 | ~spl2_2 | ~spl2_4),
% 20.87/3.00    inference(avatar_split_clause,[],[f59,f47,f34,f76])).
% 20.87/3.00  fof(f59,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) ) | (~spl2_2 | ~spl2_4)),
% 20.87/3.00    inference(forward_demodulation,[],[f57,f35])).
% 20.87/3.00  fof(f57,plain,(
% 20.87/3.00    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) ) | (~spl2_2 | ~spl2_4)),
% 20.87/3.00    inference(superposition,[],[f35,f48])).
% 20.87/3.00  fof(f53,plain,(
% 20.87/3.00    spl2_5 | ~spl2_2 | ~spl2_3),
% 20.87/3.00    inference(avatar_split_clause,[],[f45,f38,f34,f51])).
% 20.87/3.00  fof(f45,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_3)),
% 20.87/3.00    inference(forward_demodulation,[],[f44,f35])).
% 20.87/3.00  fof(f44,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_3)),
% 20.87/3.00    inference(superposition,[],[f35,f39])).
% 20.87/3.00  fof(f49,plain,(
% 20.87/3.00    spl2_4 | ~spl2_1 | ~spl2_3),
% 20.87/3.00    inference(avatar_split_clause,[],[f41,f38,f30,f47])).
% 20.87/3.00  fof(f41,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | (~spl2_1 | ~spl2_3)),
% 20.87/3.00    inference(superposition,[],[f39,f31])).
% 20.87/3.00  fof(f40,plain,(
% 20.87/3.00    spl2_3),
% 20.87/3.00    inference(avatar_split_clause,[],[f20,f38])).
% 20.87/3.00  fof(f20,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 20.87/3.00    inference(cnf_transformation,[],[f3])).
% 20.87/3.00  fof(f3,axiom,(
% 20.87/3.00    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 20.87/3.00  fof(f36,plain,(
% 20.87/3.00    spl2_2),
% 20.87/3.00    inference(avatar_split_clause,[],[f18,f34])).
% 20.87/3.00  fof(f18,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 20.87/3.00    inference(cnf_transformation,[],[f2])).
% 20.87/3.00  fof(f2,axiom,(
% 20.87/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 20.87/3.00  fof(f32,plain,(
% 20.87/3.00    spl2_1),
% 20.87/3.00    inference(avatar_split_clause,[],[f16,f30])).
% 20.87/3.00  fof(f16,plain,(
% 20.87/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 20.87/3.00    inference(cnf_transformation,[],[f1])).
% 20.87/3.00  fof(f1,axiom,(
% 20.87/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 20.87/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 20.87/3.00  % SZS output end Proof for theBenchmark
% 20.87/3.00  % (7784)------------------------------
% 20.87/3.00  % (7784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.87/3.00  % (7784)Termination reason: Refutation
% 20.87/3.00  
% 20.87/3.00  % (7784)Memory used [KB]: 56928
% 20.87/3.00  % (7784)Time elapsed: 2.534 s
% 20.87/3.00  % (7784)------------------------------
% 20.87/3.00  % (7784)------------------------------
% 20.87/3.00  % (7776)Success in time 2.646 s
%------------------------------------------------------------------------------
