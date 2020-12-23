%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:21 EST 2020

% Result     : Theorem 29.38s
% Output     : Refutation 29.38s
% Verified   : 
% Statistics : Number of formulae       :  246 ( 571 expanded)
%              Number of leaves         :   57 ( 292 expanded)
%              Depth                    :    8
%              Number of atoms          :  677 (1323 expanded)
%              Number of equality atoms :  199 ( 524 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f44,f54,f64,f109,f123,f127,f143,f167,f171,f355,f404,f418,f451,f475,f479,f530,f534,f538,f729,f1084,f1096,f1100,f1775,f1779,f1795,f1819,f1823,f2564,f4001,f4025,f4495,f4511,f6014,f8999,f9035,f9039,f14813,f33294,f33302,f34082,f49876,f54464,f55352,f55835])).

fof(f55835,plain,
    ( ~ spl2_12
    | ~ spl2_33
    | spl2_34
    | ~ spl2_40
    | ~ spl2_80
    | ~ spl2_184 ),
    inference(avatar_contradiction_clause,[],[f55834])).

fof(f55834,plain,
    ( $false
    | ~ spl2_12
    | ~ spl2_33
    | spl2_34
    | ~ spl2_40
    | ~ spl2_80
    | ~ spl2_184 ),
    inference(subsumption_resolution,[],[f728,f55833])).

fof(f55833,plain,
    ( ! [X94,X93] : k5_xboole_0(X93,X94) = k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),k5_xboole_0(X93,k4_xboole_0(X93,X94)))
    | ~ spl2_12
    | ~ spl2_33
    | ~ spl2_40
    | ~ spl2_80
    | ~ spl2_184 ),
    inference(forward_demodulation,[],[f55510,f55691])).

fof(f55691,plain,
    ( ! [X33,X32] : k5_xboole_0(X32,k4_xboole_0(X32,X33)) = k4_xboole_0(X32,k5_xboole_0(X32,X33))
    | ~ spl2_12
    | ~ spl2_33
    | ~ spl2_40
    | ~ spl2_184 ),
    inference(forward_demodulation,[],[f55690,f1110])).

fof(f1110,plain,
    ( ! [X30,X31,X32] : k5_xboole_0(X30,k5_xboole_0(X32,k5_xboole_0(X31,k4_xboole_0(X31,X30)))) = k5_xboole_0(X32,k4_xboole_0(X30,X31))
    | ~ spl2_33
    | ~ spl2_40 ),
    inference(superposition,[],[f1083,f537])).

fof(f537,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl2_33
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f1083,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1082,plain,
    ( spl2_40
  <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f55690,plain,
    ( ! [X33,X32] : k4_xboole_0(X32,k5_xboole_0(X32,X33)) = k5_xboole_0(X32,k5_xboole_0(X32,k5_xboole_0(X33,k4_xboole_0(X33,X32))))
    | ~ spl2_12
    | ~ spl2_33
    | ~ spl2_184 ),
    inference(forward_demodulation,[],[f55482,f122])).

fof(f122,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f55482,plain,
    ( ! [X33,X32] : k4_xboole_0(X32,k5_xboole_0(X32,X33)) = k5_xboole_0(X32,k5_xboole_0(k5_xboole_0(X32,X33),k4_xboole_0(X33,X32)))
    | ~ spl2_33
    | ~ spl2_184 ),
    inference(superposition,[],[f537,f55351])).

fof(f55351,plain,
    ( ! [X85,X84] : k4_xboole_0(X85,X84) = k4_xboole_0(k5_xboole_0(X84,X85),X84)
    | ~ spl2_184 ),
    inference(avatar_component_clause,[],[f55350])).

fof(f55350,plain,
    ( spl2_184
  <=> ! [X84,X85] : k4_xboole_0(X85,X84) = k4_xboole_0(k5_xboole_0(X84,X85),X84) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).

fof(f55510,plain,
    ( ! [X94,X93] : k5_xboole_0(X93,X94) = k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),k4_xboole_0(X93,k5_xboole_0(X93,X94)))
    | ~ spl2_80
    | ~ spl2_184 ),
    inference(superposition,[],[f4510,f55351])).

fof(f4510,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f4509])).

fof(f4509,plain,
    ( spl2_80
  <=> ! [X9,X8] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f728,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_34 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl2_34
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f55352,plain,
    ( spl2_184
    | ~ spl2_2
    | ~ spl2_25
    | ~ spl2_29
    | ~ spl2_176 ),
    inference(avatar_split_clause,[],[f54755,f54462,f477,f402,f38,f55350])).

fof(f38,plain,
    ( spl2_2
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f402,plain,
    ( spl2_25
  <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f477,plain,
    ( spl2_29
  <=> ! [X7,X8] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f54462,plain,
    ( spl2_176
  <=> ! [X82,X83] : k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X83),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).

fof(f54755,plain,
    ( ! [X85,X84] : k4_xboole_0(X85,X84) = k4_xboole_0(k5_xboole_0(X84,X85),X84)
    | ~ spl2_2
    | ~ spl2_25
    | ~ spl2_29
    | ~ spl2_176 ),
    inference(forward_demodulation,[],[f54754,f403])).

fof(f403,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f402])).

fof(f54754,plain,
    ( ! [X85,X84] : k4_xboole_0(k5_xboole_0(X84,X85),X84) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X85,X84))
    | ~ spl2_2
    | ~ spl2_29
    | ~ spl2_176 ),
    inference(forward_demodulation,[],[f54529,f39])).

fof(f39,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f54529,plain,
    ( ! [X85,X84] : k4_xboole_0(k5_xboole_0(X84,X85),X84) = k5_xboole_0(k4_xboole_0(X85,X84),k1_xboole_0)
    | ~ spl2_29
    | ~ spl2_176 ),
    inference(superposition,[],[f54463,f478])).

fof(f478,plain,
    ( ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f477])).

fof(f54463,plain,
    ( ! [X83,X82] : k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X83),k1_xboole_0)
    | ~ spl2_176 ),
    inference(avatar_component_clause,[],[f54462])).

fof(f54464,plain,
    ( spl2_176
    | ~ spl2_25
    | ~ spl2_28
    | ~ spl2_50
    | ~ spl2_59
    | ~ spl2_67
    | ~ spl2_105
    | ~ spl2_152
    | ~ spl2_154
    | ~ spl2_167 ),
    inference(avatar_split_clause,[],[f50326,f49874,f33300,f33292,f9037,f4023,f2562,f1793,f473,f402,f54462])).

fof(f473,plain,
    ( spl2_28
  <=> ! [X5,X6] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1793,plain,
    ( spl2_50
  <=> ! [X13,X12] : k5_xboole_0(X13,k4_xboole_0(X13,X12)) = k5_xboole_0(X12,k4_xboole_0(X12,X13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f2562,plain,
    ( spl2_59
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f4023,plain,
    ( spl2_67
  <=> ! [X15,X14] : k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)) = X14 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f9037,plain,
    ( spl2_105
  <=> ! [X22,X21] : k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).

fof(f33292,plain,
    ( spl2_152
  <=> ! [X11,X10] : k4_xboole_0(k5_xboole_0(X11,X10),X10) = k5_xboole_0(X11,k4_xboole_0(X10,k5_xboole_0(X11,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_152])])).

fof(f33300,plain,
    ( spl2_154
  <=> ! [X69,X68] : k4_xboole_0(X69,k5_xboole_0(X68,X69)) = k5_xboole_0(X68,k4_xboole_0(k5_xboole_0(X68,X69),X69)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).

fof(f49874,plain,
    ( spl2_167
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).

fof(f50326,plain,
    ( ! [X83,X82] : k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X83),k1_xboole_0)
    | ~ spl2_25
    | ~ spl2_28
    | ~ spl2_50
    | ~ spl2_59
    | ~ spl2_67
    | ~ spl2_105
    | ~ spl2_152
    | ~ spl2_154
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f50325,f33293])).

fof(f33293,plain,
    ( ! [X10,X11] : k4_xboole_0(k5_xboole_0(X11,X10),X10) = k5_xboole_0(X11,k4_xboole_0(X10,k5_xboole_0(X11,X10)))
    | ~ spl2_152 ),
    inference(avatar_component_clause,[],[f33292])).

fof(f50325,plain,
    ( ! [X83,X82] : k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(X82,k4_xboole_0(X83,k5_xboole_0(X82,X83))),k1_xboole_0)
    | ~ spl2_25
    | ~ spl2_28
    | ~ spl2_50
    | ~ spl2_59
    | ~ spl2_67
    | ~ spl2_105
    | ~ spl2_154
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f50324,f50236])).

fof(f50236,plain,
    ( ! [X235,X236] : k4_xboole_0(X236,k5_xboole_0(X235,X236)) = k4_xboole_0(X235,k4_xboole_0(k5_xboole_0(X235,X236),X236))
    | ~ spl2_25
    | ~ spl2_28
    | ~ spl2_105
    | ~ spl2_154
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f50233,f403])).

fof(f50233,plain,
    ( ! [X235,X236] : k4_xboole_0(X235,k4_xboole_0(k5_xboole_0(X235,X236),X236)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X236,k5_xboole_0(X235,X236)))
    | ~ spl2_28
    | ~ spl2_105
    | ~ spl2_154
    | ~ spl2_167 ),
    inference(backward_demodulation,[],[f44768,f49980])).

fof(f49980,plain,
    ( ! [X87,X86] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X86,X87),X87),X86)
    | ~ spl2_28
    | ~ spl2_167 ),
    inference(superposition,[],[f49875,f474])).

fof(f474,plain,
    ( ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f473])).

fof(f49875,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl2_167 ),
    inference(avatar_component_clause,[],[f49874])).

fof(f44768,plain,
    ( ! [X235,X236] : k4_xboole_0(X235,k4_xboole_0(k5_xboole_0(X235,X236),X236)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X235,X236),X236),X235),k4_xboole_0(X236,k5_xboole_0(X235,X236)))
    | ~ spl2_105
    | ~ spl2_154 ),
    inference(superposition,[],[f9038,f33301])).

fof(f33301,plain,
    ( ! [X68,X69] : k4_xboole_0(X69,k5_xboole_0(X68,X69)) = k5_xboole_0(X68,k4_xboole_0(k5_xboole_0(X68,X69),X69))
    | ~ spl2_154 ),
    inference(avatar_component_clause,[],[f33300])).

fof(f9038,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22))
    | ~ spl2_105 ),
    inference(avatar_component_clause,[],[f9037])).

fof(f50324,plain,
    ( ! [X83,X82] : k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(X82,k4_xboole_0(X82,k4_xboole_0(k5_xboole_0(X82,X83),X83))),k1_xboole_0)
    | ~ spl2_50
    | ~ spl2_59
    | ~ spl2_67
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f50323,f2563])).

fof(f2563,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f2562])).

fof(f50323,plain,
    ( ! [X83,X82] : k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,k4_xboole_0(X82,k5_xboole_0(X82,X83))),X83),k1_xboole_0)
    | ~ spl2_50
    | ~ spl2_59
    | ~ spl2_67
    | ~ spl2_167 ),
    inference(forward_demodulation,[],[f50079,f4050])).

fof(f4050,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2)
    | ~ spl2_50
    | ~ spl2_59 ),
    inference(superposition,[],[f2563,f1794])).

fof(f1794,plain,
    ( ! [X12,X13] : k5_xboole_0(X13,k4_xboole_0(X13,X12)) = k5_xboole_0(X12,k4_xboole_0(X12,X13))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f1793])).

fof(f50079,plain,
    ( ! [X83,X82] : k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(X82,X83))),k1_xboole_0)
    | ~ spl2_67
    | ~ spl2_167 ),
    inference(superposition,[],[f4024,f49875])).

fof(f4024,plain,
    ( ! [X14,X15] : k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)) = X14
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f4023])).

fof(f49876,plain,
    ( spl2_167
    | ~ spl2_104
    | ~ spl2_161 ),
    inference(avatar_split_clause,[],[f49424,f34080,f9033,f49874])).

fof(f9033,plain,
    ( spl2_104
  <=> ! [X36,X37] : k5_xboole_0(X36,X37) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X37,X36)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f34080,plain,
    ( spl2_161
  <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_161])])).

fof(f49424,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl2_104
    | ~ spl2_161 ),
    inference(superposition,[],[f34081,f9034])).

fof(f9034,plain,
    ( ! [X37,X36] : k5_xboole_0(X36,X37) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X37,X36))
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f9033])).

fof(f34081,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5)))
    | ~ spl2_161 ),
    inference(avatar_component_clause,[],[f34080])).

fof(f34082,plain,
    ( spl2_161
    | ~ spl2_25
    | ~ spl2_32
    | ~ spl2_81
    | ~ spl2_108 ),
    inference(avatar_split_clause,[],[f14957,f14811,f6012,f532,f402,f34080])).

fof(f532,plain,
    ( spl2_32
  <=> ! [X5,X7,X6] : k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f6012,plain,
    ( spl2_81
  <=> ! [X9,X8,X10] : k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f14811,plain,
    ( spl2_108
  <=> ! [X22,X21,X23] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).

fof(f14957,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5)))
    | ~ spl2_25
    | ~ spl2_32
    | ~ spl2_81
    | ~ spl2_108 ),
    inference(forward_demodulation,[],[f14956,f403])).

fof(f14956,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5))))
    | ~ spl2_32
    | ~ spl2_81
    | ~ spl2_108 ),
    inference(forward_demodulation,[],[f14886,f533])).

fof(f533,plain,
    ( ! [X6,X7,X5] : k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f532])).

fof(f14886,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)))
    | ~ spl2_81
    | ~ spl2_108 ),
    inference(superposition,[],[f6013,f14812])).

fof(f14812,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23)))
    | ~ spl2_108 ),
    inference(avatar_component_clause,[],[f14811])).

fof(f6013,plain,
    ( ! [X10,X8,X9] : k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f6012])).

fof(f33302,plain,
    ( spl2_154
    | ~ spl2_28
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f7506,f4493,f473,f33300])).

fof(f4493,plain,
    ( spl2_76
  <=> ! [X22,X23] : k4_xboole_0(X23,X22) = k5_xboole_0(k5_xboole_0(X22,X23),k4_xboole_0(X22,X23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f7506,plain,
    ( ! [X68,X69] : k4_xboole_0(X69,k5_xboole_0(X68,X69)) = k5_xboole_0(X68,k4_xboole_0(k5_xboole_0(X68,X69),X69))
    | ~ spl2_28
    | ~ spl2_76 ),
    inference(superposition,[],[f4494,f474])).

fof(f4494,plain,
    ( ! [X23,X22] : k4_xboole_0(X23,X22) = k5_xboole_0(k5_xboole_0(X22,X23),k4_xboole_0(X22,X23))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f4493])).

fof(f33294,plain,
    ( spl2_152
    | ~ spl2_27
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f7481,f4493,f449,f33292])).

fof(f449,plain,
    ( spl2_27
  <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f7481,plain,
    ( ! [X10,X11] : k4_xboole_0(k5_xboole_0(X11,X10),X10) = k5_xboole_0(X11,k4_xboole_0(X10,k5_xboole_0(X11,X10)))
    | ~ spl2_27
    | ~ spl2_76 ),
    inference(superposition,[],[f4494,f450])).

fof(f450,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f449])).

fof(f14813,plain,
    ( spl2_108
    | ~ spl2_2
    | ~ spl2_26
    | ~ spl2_45
    | ~ spl2_59
    | ~ spl2_61
    | ~ spl2_81
    | ~ spl2_95 ),
    inference(avatar_split_clause,[],[f14805,f8997,f6012,f3999,f2562,f1773,f416,f38,f14811])).

fof(f416,plain,
    ( spl2_26
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1773,plain,
    ( spl2_45
  <=> ! [X7,X8] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f3999,plain,
    ( spl2_61
  <=> ! [X11,X13,X12] : k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f8997,plain,
    ( spl2_95
  <=> ! [X18,X19] : k5_xboole_0(X19,k4_xboole_0(X19,X18)) = k5_xboole_0(k4_xboole_0(X18,X19),X18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f14805,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23)))
    | ~ spl2_2
    | ~ spl2_26
    | ~ spl2_45
    | ~ spl2_59
    | ~ spl2_61
    | ~ spl2_81
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f14804,f417])).

fof(f417,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f416])).

fof(f14804,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(X21,k5_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23)))))
    | ~ spl2_2
    | ~ spl2_45
    | ~ spl2_59
    | ~ spl2_61
    | ~ spl2_81
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f14803,f2563])).

fof(f14803,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X21,X22)),X23)))
    | ~ spl2_2
    | ~ spl2_45
    | ~ spl2_61
    | ~ spl2_81
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f14802,f39])).

fof(f14802,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X21,X22)),X23),X21))
    | ~ spl2_45
    | ~ spl2_61
    | ~ spl2_81
    | ~ spl2_95 ),
    inference(backward_demodulation,[],[f8580,f14655])).

fof(f14655,plain,
    ( ! [X215,X213,X214] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X213,X214),X215),X213) = k5_xboole_0(X214,k5_xboole_0(X215,k4_xboole_0(X215,k5_xboole_0(X213,X214))))
    | ~ spl2_61
    | ~ spl2_95 ),
    inference(superposition,[],[f4000,f8998])).

fof(f8998,plain,
    ( ! [X19,X18] : k5_xboole_0(X19,k4_xboole_0(X19,X18)) = k5_xboole_0(k4_xboole_0(X18,X19),X18)
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f8997])).

fof(f4000,plain,
    ( ! [X12,X13,X11] : k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13)))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f3999])).

fof(f8580,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(X23,k4_xboole_0(X23,k5_xboole_0(X21,k4_xboole_0(X21,X22))))))
    | ~ spl2_45
    | ~ spl2_81 ),
    inference(superposition,[],[f6013,f1774])).

fof(f1774,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f9039,plain,
    ( spl2_105
    | ~ spl2_29
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f7556,f4493,f477,f9037])).

fof(f7556,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22))
    | ~ spl2_29
    | ~ spl2_76 ),
    inference(superposition,[],[f478,f4494])).

fof(f9035,plain,
    ( spl2_104
    | ~ spl2_44
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f4561,f3999,f1098,f9033])).

fof(f1098,plain,
    ( spl2_44
  <=> ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f4561,plain,
    ( ! [X37,X36] : k5_xboole_0(X36,X37) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X37,X36))
    | ~ spl2_44
    | ~ spl2_61 ),
    inference(superposition,[],[f4000,f1099])).

fof(f1099,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f8999,plain,
    ( spl2_95
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f963,f536,f477,f8997])).

fof(f963,plain,
    ( ! [X19,X18] : k5_xboole_0(X19,k4_xboole_0(X19,X18)) = k5_xboole_0(k4_xboole_0(X18,X19),X18)
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(superposition,[],[f478,f537])).

fof(f6014,plain,
    ( spl2_81
    | ~ spl2_5
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f4074,f2562,f52,f6012])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f4074,plain,
    ( ! [X10,X8,X9] : k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))
    | ~ spl2_5
    | ~ spl2_59 ),
    inference(superposition,[],[f53,f2563])).

fof(f53,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f4511,plain,
    ( spl2_80
    | ~ spl2_56
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f3794,f1821,f1817,f4509])).

fof(f1817,plain,
    ( spl2_56
  <=> ! [X3,X4] : k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f1821,plain,
    ( spl2_57
  <=> ! [X22,X21] : k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f3794,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8
    | ~ spl2_56
    | ~ spl2_57 ),
    inference(superposition,[],[f1818,f1822])).

fof(f1822,plain,
    ( ! [X21,X22] : k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(X22,X21))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f1821])).

fof(f1818,plain,
    ( ! [X4,X3] : k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3)) = X3
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f1817])).

fof(f4495,plain,
    ( spl2_76
    | ~ spl2_33
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f1995,f1777,f536,f4493])).

fof(f1777,plain,
    ( spl2_46
  <=> ! [X11,X13,X12] : k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f1995,plain,
    ( ! [X23,X22] : k4_xboole_0(X23,X22) = k5_xboole_0(k5_xboole_0(X22,X23),k4_xboole_0(X22,X23))
    | ~ spl2_33
    | ~ spl2_46 ),
    inference(superposition,[],[f1778,f537])).

fof(f1778,plain,
    ( ! [X12,X13,X11] : k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f1777])).

fof(f4025,plain,
    ( spl2_67
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f961,f536,f449,f4023])).

fof(f961,plain,
    ( ! [X14,X15] : k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)) = X14
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(superposition,[],[f450,f537])).

fof(f4001,plain,
    ( spl2_61
    | ~ spl2_12
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f460,f449,f121,f3999])).

fof(f460,plain,
    ( ! [X12,X13,X11] : k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13)))
    | ~ spl2_12
    | ~ spl2_27 ),
    inference(superposition,[],[f450,f122])).

fof(f2564,plain,
    ( spl2_59
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f441,f416,f165,f2562])).

fof(f165,plain,
    ( spl2_16
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f441,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f433,f422])).

fof(f422,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(superposition,[],[f417,f166])).

fof(f166,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f433,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f32,f422])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1823,plain,
    ( spl2_57
    | ~ spl2_26
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f1710,f1098,f416,f1821])).

fof(f1710,plain,
    ( ! [X21,X22] : k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(X22,X21))
    | ~ spl2_26
    | ~ spl2_44 ),
    inference(superposition,[],[f417,f1099])).

fof(f1819,plain,
    ( spl2_56
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f1677,f1094,f169,f52,f34,f1817])).

fof(f34,plain,
    ( spl2_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f169,plain,
    ( spl2_17
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f1094,plain,
    ( spl2_43
  <=> ! [X1,X2] : k4_xboole_0(X2,X1) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f1677,plain,
    ( ! [X4,X3] : k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3)) = X3
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f1676,f35])).

fof(f35,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f1676,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3))
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f1658,f53])).

fof(f1658,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3))
    | ~ spl2_17
    | ~ spl2_43 ),
    inference(superposition,[],[f170,f1095])).

fof(f1095,plain,
    ( ! [X2,X1] : k4_xboole_0(X2,X1) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f1094])).

fof(f170,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1795,plain,
    ( spl2_50
    | ~ spl2_26
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f960,f536,f416,f1793])).

fof(f960,plain,
    ( ! [X12,X13] : k5_xboole_0(X13,k4_xboole_0(X13,X12)) = k5_xboole_0(X12,k4_xboole_0(X12,X13))
    | ~ spl2_26
    | ~ spl2_33 ),
    inference(superposition,[],[f417,f537])).

fof(f1779,plain,
    ( spl2_46
    | ~ spl2_12
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f426,f416,f121,f1777])).

fof(f426,plain,
    ( ! [X12,X13,X11] : k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13
    | ~ spl2_12
    | ~ spl2_26 ),
    inference(superposition,[],[f417,f122])).

fof(f1775,plain,
    ( spl2_45
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f422,f416,f165,f1773])).

fof(f1100,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f990,f536,f532,f38,f1098])).

fof(f990,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f953,f39])).

fof(f953,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X6,X5),X5))
    | ~ spl2_32
    | ~ spl2_33 ),
    inference(superposition,[],[f537,f533])).

fof(f1096,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_25
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f977,f536,f477,f402,f121,f52,f38,f1094])).

fof(f977,plain,
    ( ! [X2,X1] : k4_xboole_0(X2,X1) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_25
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f976,f403])).

fof(f976,plain,
    ( ! [X2,X1] : k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f975,f39])).

fof(f975,plain,
    ( ! [X2,X1] : k5_xboole_0(k4_xboole_0(X2,X1),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f945,f519])).

fof(f519,plain,
    ( ! [X8,X7,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X9))
    | ~ spl2_12
    | ~ spl2_29 ),
    inference(superposition,[],[f122,f478])).

fof(f945,plain,
    ( ! [X2,X1] : k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k5_xboole_0(X1,k1_xboole_0))
    | ~ spl2_5
    | ~ spl2_33 ),
    inference(superposition,[],[f537,f53])).

fof(f1084,plain,
    ( spl2_40
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f551,f528,f121,f1082])).

fof(f528,plain,
    ( spl2_31
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f551,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(superposition,[],[f529,f122])).

fof(f529,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f528])).

fof(f729,plain,
    ( ~ spl2_34
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f440,f416,f165,f726])).

fof(f440,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f28,f422])).

fof(f28,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f538,plain,
    ( spl2_33
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f436,f416,f169,f165,f536])).

fof(f436,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f358,f422])).

fof(f358,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(superposition,[],[f166,f170])).

fof(f534,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f183,f121,f38,f532])).

fof(f183,plain,
    ( ! [X6,X7,X5] : k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(superposition,[],[f122,f39])).

fof(f530,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f172,f121,f38,f528])).

fof(f172,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(superposition,[],[f122,f39])).

fof(f479,plain,
    ( spl2_29
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f456,f449,f477])).

fof(f456,plain,
    ( ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7
    | ~ spl2_27 ),
    inference(superposition,[],[f450,f450])).

fof(f475,plain,
    ( spl2_28
    | ~ spl2_26
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f455,f449,f416,f473])).

fof(f455,plain,
    ( ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5
    | ~ spl2_26
    | ~ spl2_27 ),
    inference(superposition,[],[f450,f417])).

fof(f451,plain,
    ( spl2_27
    | ~ spl2_2
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f420,f416,f38,f449])).

fof(f420,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
    | ~ spl2_2
    | ~ spl2_26 ),
    inference(superposition,[],[f417,f39])).

fof(f418,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f376,f353,f165,f141,f121,f62,f34,f416])).

fof(f62,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f141,plain,
    ( spl2_15
  <=> ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f353,plain,
    ( spl2_23
  <=> ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f376,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f374,f309])).

fof(f309,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f142,f305])).

fof(f305,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f286,f63])).

fof(f63,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f286,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_1
    | ~ spl2_16 ),
    inference(superposition,[],[f166,f35])).

fof(f142,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f374,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_12
    | ~ spl2_23 ),
    inference(superposition,[],[f122,f354])).

fof(f354,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f353])).

fof(f404,plain,
    ( spl2_25
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f309,f165,f141,f62,f34,f402])).

fof(f355,plain,
    ( spl2_23
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f333,f165,f52,f34,f353])).

fof(f333,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f287,f35])).

fof(f287,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(superposition,[],[f166,f53])).

fof(f171,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f31,f169])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f167,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f27,f165])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f143,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f130,f125,f38,f141])).

fof(f125,plain,
    ( spl2_13
  <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f130,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(superposition,[],[f126,f39])).

fof(f126,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f114,f107,f38,f125])).

fof(f107,plain,
    ( spl2_11
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f114,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f108,f39])).

fof(f108,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f123,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f26,f121])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f109,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f60,f52,f42,f34,f107])).

fof(f42,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f58,f35])).

fof(f58,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f43,f53])).

fof(f43,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f64,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f57,f52,f42,f62])).

fof(f57,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f53,f43])).

fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f42])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f36,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (31391)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (31385)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (31381)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (31380)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (31378)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (31384)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (31389)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (31382)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31389)Refutation not found, incomplete strategy% (31389)------------------------------
% 0.21/0.48  % (31389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31389)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31389)Memory used [KB]: 10490
% 0.21/0.48  % (31389)Time elapsed: 0.071 s
% 0.21/0.48  % (31389)------------------------------
% 0.21/0.48  % (31389)------------------------------
% 0.21/0.48  % (31387)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (31395)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (31379)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (31383)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (31394)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (31388)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (31390)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (31393)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (31392)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (31386)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 5.24/1.04  % (31382)Time limit reached!
% 5.24/1.04  % (31382)------------------------------
% 5.24/1.04  % (31382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.04  % (31382)Termination reason: Time limit
% 5.24/1.04  % (31382)Termination phase: Saturation
% 5.24/1.04  
% 5.24/1.04  % (31382)Memory used [KB]: 21108
% 5.24/1.04  % (31382)Time elapsed: 0.600 s
% 5.24/1.04  % (31382)------------------------------
% 5.24/1.04  % (31382)------------------------------
% 12.53/1.95  % (31383)Time limit reached!
% 12.53/1.95  % (31383)------------------------------
% 12.53/1.95  % (31383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/1.95  % (31383)Termination reason: Time limit
% 12.53/1.95  % (31383)Termination phase: Saturation
% 12.53/1.95  
% 12.53/1.95  % (31383)Memory used [KB]: 42600
% 12.53/1.95  % (31383)Time elapsed: 1.500 s
% 12.53/1.95  % (31383)------------------------------
% 12.53/1.95  % (31383)------------------------------
% 12.53/1.97  % (31384)Time limit reached!
% 12.53/1.97  % (31384)------------------------------
% 12.53/1.97  % (31384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/1.97  % (31384)Termination reason: Time limit
% 12.53/1.97  % (31384)Termination phase: Saturation
% 12.53/1.97  
% 12.53/1.97  % (31384)Memory used [KB]: 43751
% 12.53/1.97  % (31384)Time elapsed: 1.500 s
% 12.53/1.97  % (31384)------------------------------
% 12.53/1.97  % (31384)------------------------------
% 14.95/2.22  % (31380)Time limit reached!
% 14.95/2.22  % (31380)------------------------------
% 14.95/2.22  % (31380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.95/2.22  % (31380)Termination reason: Time limit
% 14.95/2.22  % (31380)Termination phase: Saturation
% 14.95/2.22  
% 14.95/2.22  % (31380)Memory used [KB]: 44647
% 14.95/2.22  % (31380)Time elapsed: 1.800 s
% 14.95/2.22  % (31380)------------------------------
% 14.95/2.22  % (31380)------------------------------
% 17.86/2.66  % (31390)Time limit reached!
% 17.86/2.66  % (31390)------------------------------
% 17.86/2.66  % (31390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.86/2.66  % (31390)Termination reason: Time limit
% 17.86/2.66  % (31390)Termination phase: Saturation
% 17.86/2.66  
% 17.86/2.66  % (31390)Memory used [KB]: 63197
% 17.86/2.66  % (31390)Time elapsed: 2.200 s
% 17.86/2.66  % (31390)------------------------------
% 17.86/2.66  % (31390)------------------------------
% 29.38/4.10  % (31385)Refutation found. Thanks to Tanya!
% 29.38/4.10  % SZS status Theorem for theBenchmark
% 29.38/4.10  % SZS output start Proof for theBenchmark
% 29.38/4.10  fof(f55934,plain,(
% 29.38/4.10    $false),
% 29.38/4.10    inference(avatar_sat_refutation,[],[f36,f40,f44,f54,f64,f109,f123,f127,f143,f167,f171,f355,f404,f418,f451,f475,f479,f530,f534,f538,f729,f1084,f1096,f1100,f1775,f1779,f1795,f1819,f1823,f2564,f4001,f4025,f4495,f4511,f6014,f8999,f9035,f9039,f14813,f33294,f33302,f34082,f49876,f54464,f55352,f55835])).
% 29.38/4.10  fof(f55835,plain,(
% 29.38/4.10    ~spl2_12 | ~spl2_33 | spl2_34 | ~spl2_40 | ~spl2_80 | ~spl2_184),
% 29.38/4.10    inference(avatar_contradiction_clause,[],[f55834])).
% 29.38/4.10  fof(f55834,plain,(
% 29.38/4.10    $false | (~spl2_12 | ~spl2_33 | spl2_34 | ~spl2_40 | ~spl2_80 | ~spl2_184)),
% 29.38/4.10    inference(subsumption_resolution,[],[f728,f55833])).
% 29.38/4.10  fof(f55833,plain,(
% 29.38/4.10    ( ! [X94,X93] : (k5_xboole_0(X93,X94) = k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),k5_xboole_0(X93,k4_xboole_0(X93,X94)))) ) | (~spl2_12 | ~spl2_33 | ~spl2_40 | ~spl2_80 | ~spl2_184)),
% 29.38/4.10    inference(forward_demodulation,[],[f55510,f55691])).
% 29.38/4.10  fof(f55691,plain,(
% 29.38/4.10    ( ! [X33,X32] : (k5_xboole_0(X32,k4_xboole_0(X32,X33)) = k4_xboole_0(X32,k5_xboole_0(X32,X33))) ) | (~spl2_12 | ~spl2_33 | ~spl2_40 | ~spl2_184)),
% 29.38/4.10    inference(forward_demodulation,[],[f55690,f1110])).
% 29.38/4.10  fof(f1110,plain,(
% 29.38/4.10    ( ! [X30,X31,X32] : (k5_xboole_0(X30,k5_xboole_0(X32,k5_xboole_0(X31,k4_xboole_0(X31,X30)))) = k5_xboole_0(X32,k4_xboole_0(X30,X31))) ) | (~spl2_33 | ~spl2_40)),
% 29.38/4.10    inference(superposition,[],[f1083,f537])).
% 29.38/4.10  fof(f537,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_33),
% 29.38/4.10    inference(avatar_component_clause,[],[f536])).
% 29.38/4.10  fof(f536,plain,(
% 29.38/4.10    spl2_33 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 29.38/4.10  fof(f1083,plain,(
% 29.38/4.10    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | ~spl2_40),
% 29.38/4.10    inference(avatar_component_clause,[],[f1082])).
% 29.38/4.10  fof(f1082,plain,(
% 29.38/4.10    spl2_40 <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 29.38/4.10  fof(f55690,plain,(
% 29.38/4.10    ( ! [X33,X32] : (k4_xboole_0(X32,k5_xboole_0(X32,X33)) = k5_xboole_0(X32,k5_xboole_0(X32,k5_xboole_0(X33,k4_xboole_0(X33,X32))))) ) | (~spl2_12 | ~spl2_33 | ~spl2_184)),
% 29.38/4.10    inference(forward_demodulation,[],[f55482,f122])).
% 29.38/4.10  fof(f122,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_12),
% 29.38/4.10    inference(avatar_component_clause,[],[f121])).
% 29.38/4.10  fof(f121,plain,(
% 29.38/4.10    spl2_12 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 29.38/4.10  fof(f55482,plain,(
% 29.38/4.10    ( ! [X33,X32] : (k4_xboole_0(X32,k5_xboole_0(X32,X33)) = k5_xboole_0(X32,k5_xboole_0(k5_xboole_0(X32,X33),k4_xboole_0(X33,X32)))) ) | (~spl2_33 | ~spl2_184)),
% 29.38/4.10    inference(superposition,[],[f537,f55351])).
% 29.38/4.10  fof(f55351,plain,(
% 29.38/4.10    ( ! [X85,X84] : (k4_xboole_0(X85,X84) = k4_xboole_0(k5_xboole_0(X84,X85),X84)) ) | ~spl2_184),
% 29.38/4.10    inference(avatar_component_clause,[],[f55350])).
% 29.38/4.10  fof(f55350,plain,(
% 29.38/4.10    spl2_184 <=> ! [X84,X85] : k4_xboole_0(X85,X84) = k4_xboole_0(k5_xboole_0(X84,X85),X84)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).
% 29.38/4.10  fof(f55510,plain,(
% 29.38/4.10    ( ! [X94,X93] : (k5_xboole_0(X93,X94) = k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),k4_xboole_0(X93,k5_xboole_0(X93,X94)))) ) | (~spl2_80 | ~spl2_184)),
% 29.38/4.10    inference(superposition,[],[f4510,f55351])).
% 29.38/4.10  fof(f4510,plain,(
% 29.38/4.10    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8) ) | ~spl2_80),
% 29.38/4.10    inference(avatar_component_clause,[],[f4509])).
% 29.38/4.10  fof(f4509,plain,(
% 29.38/4.10    spl2_80 <=> ! [X9,X8] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 29.38/4.10  fof(f728,plain,(
% 29.38/4.10    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_34),
% 29.38/4.10    inference(avatar_component_clause,[],[f726])).
% 29.38/4.10  fof(f726,plain,(
% 29.38/4.10    spl2_34 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 29.38/4.10  fof(f55352,plain,(
% 29.38/4.10    spl2_184 | ~spl2_2 | ~spl2_25 | ~spl2_29 | ~spl2_176),
% 29.38/4.10    inference(avatar_split_clause,[],[f54755,f54462,f477,f402,f38,f55350])).
% 29.38/4.10  fof(f38,plain,(
% 29.38/4.10    spl2_2 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 29.38/4.10  fof(f402,plain,(
% 29.38/4.10    spl2_25 <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 29.38/4.10  fof(f477,plain,(
% 29.38/4.10    spl2_29 <=> ! [X7,X8] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 29.38/4.10  fof(f54462,plain,(
% 29.38/4.10    spl2_176 <=> ! [X82,X83] : k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X83),k1_xboole_0)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).
% 29.38/4.10  fof(f54755,plain,(
% 29.38/4.10    ( ! [X85,X84] : (k4_xboole_0(X85,X84) = k4_xboole_0(k5_xboole_0(X84,X85),X84)) ) | (~spl2_2 | ~spl2_25 | ~spl2_29 | ~spl2_176)),
% 29.38/4.10    inference(forward_demodulation,[],[f54754,f403])).
% 29.38/4.10  fof(f403,plain,(
% 29.38/4.10    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl2_25),
% 29.38/4.10    inference(avatar_component_clause,[],[f402])).
% 29.38/4.10  fof(f54754,plain,(
% 29.38/4.10    ( ! [X85,X84] : (k4_xboole_0(k5_xboole_0(X84,X85),X84) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X85,X84))) ) | (~spl2_2 | ~spl2_29 | ~spl2_176)),
% 29.38/4.10    inference(forward_demodulation,[],[f54529,f39])).
% 29.38/4.10  fof(f39,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_2),
% 29.38/4.10    inference(avatar_component_clause,[],[f38])).
% 29.38/4.10  fof(f54529,plain,(
% 29.38/4.10    ( ! [X85,X84] : (k4_xboole_0(k5_xboole_0(X84,X85),X84) = k5_xboole_0(k4_xboole_0(X85,X84),k1_xboole_0)) ) | (~spl2_29 | ~spl2_176)),
% 29.38/4.10    inference(superposition,[],[f54463,f478])).
% 29.38/4.10  fof(f478,plain,(
% 29.38/4.10    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) ) | ~spl2_29),
% 29.38/4.10    inference(avatar_component_clause,[],[f477])).
% 29.38/4.10  fof(f54463,plain,(
% 29.38/4.10    ( ! [X83,X82] : (k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X83),k1_xboole_0)) ) | ~spl2_176),
% 29.38/4.10    inference(avatar_component_clause,[],[f54462])).
% 29.38/4.10  fof(f54464,plain,(
% 29.38/4.10    spl2_176 | ~spl2_25 | ~spl2_28 | ~spl2_50 | ~spl2_59 | ~spl2_67 | ~spl2_105 | ~spl2_152 | ~spl2_154 | ~spl2_167),
% 29.38/4.10    inference(avatar_split_clause,[],[f50326,f49874,f33300,f33292,f9037,f4023,f2562,f1793,f473,f402,f54462])).
% 29.38/4.10  fof(f473,plain,(
% 29.38/4.10    spl2_28 <=> ! [X5,X6] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 29.38/4.10  fof(f1793,plain,(
% 29.38/4.10    spl2_50 <=> ! [X13,X12] : k5_xboole_0(X13,k4_xboole_0(X13,X12)) = k5_xboole_0(X12,k4_xboole_0(X12,X13))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 29.38/4.10  fof(f2562,plain,(
% 29.38/4.10    spl2_59 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 29.38/4.10  fof(f4023,plain,(
% 29.38/4.10    spl2_67 <=> ! [X15,X14] : k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)) = X14),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 29.38/4.10  fof(f9037,plain,(
% 29.38/4.10    spl2_105 <=> ! [X22,X21] : k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).
% 29.38/4.10  fof(f33292,plain,(
% 29.38/4.10    spl2_152 <=> ! [X11,X10] : k4_xboole_0(k5_xboole_0(X11,X10),X10) = k5_xboole_0(X11,k4_xboole_0(X10,k5_xboole_0(X11,X10)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_152])])).
% 29.38/4.10  fof(f33300,plain,(
% 29.38/4.10    spl2_154 <=> ! [X69,X68] : k4_xboole_0(X69,k5_xboole_0(X68,X69)) = k5_xboole_0(X68,k4_xboole_0(k5_xboole_0(X68,X69),X69))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).
% 29.38/4.10  fof(f49874,plain,(
% 29.38/4.10    spl2_167 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).
% 29.38/4.10  fof(f50326,plain,(
% 29.38/4.10    ( ! [X83,X82] : (k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X83),k1_xboole_0)) ) | (~spl2_25 | ~spl2_28 | ~spl2_50 | ~spl2_59 | ~spl2_67 | ~spl2_105 | ~spl2_152 | ~spl2_154 | ~spl2_167)),
% 29.38/4.10    inference(forward_demodulation,[],[f50325,f33293])).
% 29.38/4.10  fof(f33293,plain,(
% 29.38/4.10    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X11,X10),X10) = k5_xboole_0(X11,k4_xboole_0(X10,k5_xboole_0(X11,X10)))) ) | ~spl2_152),
% 29.38/4.10    inference(avatar_component_clause,[],[f33292])).
% 29.38/4.10  fof(f50325,plain,(
% 29.38/4.10    ( ! [X83,X82] : (k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(X82,k4_xboole_0(X83,k5_xboole_0(X82,X83))),k1_xboole_0)) ) | (~spl2_25 | ~spl2_28 | ~spl2_50 | ~spl2_59 | ~spl2_67 | ~spl2_105 | ~spl2_154 | ~spl2_167)),
% 29.38/4.10    inference(forward_demodulation,[],[f50324,f50236])).
% 29.38/4.10  fof(f50236,plain,(
% 29.38/4.10    ( ! [X235,X236] : (k4_xboole_0(X236,k5_xboole_0(X235,X236)) = k4_xboole_0(X235,k4_xboole_0(k5_xboole_0(X235,X236),X236))) ) | (~spl2_25 | ~spl2_28 | ~spl2_105 | ~spl2_154 | ~spl2_167)),
% 29.38/4.10    inference(forward_demodulation,[],[f50233,f403])).
% 29.38/4.10  fof(f50233,plain,(
% 29.38/4.10    ( ! [X235,X236] : (k4_xboole_0(X235,k4_xboole_0(k5_xboole_0(X235,X236),X236)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X236,k5_xboole_0(X235,X236)))) ) | (~spl2_28 | ~spl2_105 | ~spl2_154 | ~spl2_167)),
% 29.38/4.10    inference(backward_demodulation,[],[f44768,f49980])).
% 29.38/4.10  fof(f49980,plain,(
% 29.38/4.10    ( ! [X87,X86] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X86,X87),X87),X86)) ) | (~spl2_28 | ~spl2_167)),
% 29.38/4.10    inference(superposition,[],[f49875,f474])).
% 29.38/4.10  fof(f474,plain,(
% 29.38/4.10    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) ) | ~spl2_28),
% 29.38/4.10    inference(avatar_component_clause,[],[f473])).
% 29.38/4.10  fof(f49875,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl2_167),
% 29.38/4.10    inference(avatar_component_clause,[],[f49874])).
% 29.38/4.10  fof(f44768,plain,(
% 29.38/4.10    ( ! [X235,X236] : (k4_xboole_0(X235,k4_xboole_0(k5_xboole_0(X235,X236),X236)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X235,X236),X236),X235),k4_xboole_0(X236,k5_xboole_0(X235,X236)))) ) | (~spl2_105 | ~spl2_154)),
% 29.38/4.10    inference(superposition,[],[f9038,f33301])).
% 29.38/4.10  fof(f33301,plain,(
% 29.38/4.10    ( ! [X68,X69] : (k4_xboole_0(X69,k5_xboole_0(X68,X69)) = k5_xboole_0(X68,k4_xboole_0(k5_xboole_0(X68,X69),X69))) ) | ~spl2_154),
% 29.38/4.10    inference(avatar_component_clause,[],[f33300])).
% 29.38/4.10  fof(f9038,plain,(
% 29.38/4.10    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22))) ) | ~spl2_105),
% 29.38/4.10    inference(avatar_component_clause,[],[f9037])).
% 29.38/4.10  fof(f50324,plain,(
% 29.38/4.10    ( ! [X83,X82] : (k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(X82,k4_xboole_0(X82,k4_xboole_0(k5_xboole_0(X82,X83),X83))),k1_xboole_0)) ) | (~spl2_50 | ~spl2_59 | ~spl2_67 | ~spl2_167)),
% 29.38/4.10    inference(forward_demodulation,[],[f50323,f2563])).
% 29.38/4.10  fof(f2563,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | ~spl2_59),
% 29.38/4.10    inference(avatar_component_clause,[],[f2562])).
% 29.38/4.10  fof(f50323,plain,(
% 29.38/4.10    ( ! [X83,X82] : (k4_xboole_0(X82,X83) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,k4_xboole_0(X82,k5_xboole_0(X82,X83))),X83),k1_xboole_0)) ) | (~spl2_50 | ~spl2_59 | ~spl2_67 | ~spl2_167)),
% 29.38/4.10    inference(forward_demodulation,[],[f50079,f4050])).
% 29.38/4.10  fof(f4050,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | (~spl2_50 | ~spl2_59)),
% 29.38/4.10    inference(superposition,[],[f2563,f1794])).
% 29.38/4.10  fof(f1794,plain,(
% 29.38/4.10    ( ! [X12,X13] : (k5_xboole_0(X13,k4_xboole_0(X13,X12)) = k5_xboole_0(X12,k4_xboole_0(X12,X13))) ) | ~spl2_50),
% 29.38/4.10    inference(avatar_component_clause,[],[f1793])).
% 29.38/4.10  fof(f50079,plain,(
% 29.38/4.10    ( ! [X83,X82] : (k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(X82,X83))),k1_xboole_0)) ) | (~spl2_67 | ~spl2_167)),
% 29.38/4.10    inference(superposition,[],[f4024,f49875])).
% 29.38/4.10  fof(f4024,plain,(
% 29.38/4.10    ( ! [X14,X15] : (k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)) = X14) ) | ~spl2_67),
% 29.38/4.10    inference(avatar_component_clause,[],[f4023])).
% 29.38/4.10  fof(f49876,plain,(
% 29.38/4.10    spl2_167 | ~spl2_104 | ~spl2_161),
% 29.38/4.10    inference(avatar_split_clause,[],[f49424,f34080,f9033,f49874])).
% 29.38/4.10  fof(f9033,plain,(
% 29.38/4.10    spl2_104 <=> ! [X36,X37] : k5_xboole_0(X36,X37) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X37,X36))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 29.38/4.10  fof(f34080,plain,(
% 29.38/4.10    spl2_161 <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_161])])).
% 29.38/4.10  fof(f49424,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | (~spl2_104 | ~spl2_161)),
% 29.38/4.10    inference(superposition,[],[f34081,f9034])).
% 29.38/4.10  fof(f9034,plain,(
% 29.38/4.10    ( ! [X37,X36] : (k5_xboole_0(X36,X37) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X37,X36))) ) | ~spl2_104),
% 29.38/4.10    inference(avatar_component_clause,[],[f9033])).
% 29.38/4.10  fof(f34081,plain,(
% 29.38/4.10    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5)))) ) | ~spl2_161),
% 29.38/4.10    inference(avatar_component_clause,[],[f34080])).
% 29.38/4.10  fof(f34082,plain,(
% 29.38/4.10    spl2_161 | ~spl2_25 | ~spl2_32 | ~spl2_81 | ~spl2_108),
% 29.38/4.10    inference(avatar_split_clause,[],[f14957,f14811,f6012,f532,f402,f34080])).
% 29.38/4.10  fof(f532,plain,(
% 29.38/4.10    spl2_32 <=> ! [X5,X7,X6] : k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 29.38/4.10  fof(f6012,plain,(
% 29.38/4.10    spl2_81 <=> ! [X9,X8,X10] : k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 29.38/4.10  fof(f14811,plain,(
% 29.38/4.10    spl2_108 <=> ! [X22,X21,X23] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).
% 29.38/4.10  fof(f14957,plain,(
% 29.38/4.10    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5)))) ) | (~spl2_25 | ~spl2_32 | ~spl2_81 | ~spl2_108)),
% 29.38/4.10    inference(forward_demodulation,[],[f14956,f403])).
% 29.38/4.10  fof(f14956,plain,(
% 29.38/4.10    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5))))) ) | (~spl2_32 | ~spl2_81 | ~spl2_108)),
% 29.38/4.10    inference(forward_demodulation,[],[f14886,f533])).
% 29.38/4.10  fof(f533,plain,(
% 29.38/4.10    ( ! [X6,X7,X5] : (k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))) ) | ~spl2_32),
% 29.38/4.10    inference(avatar_component_clause,[],[f532])).
% 29.38/4.10  fof(f14886,plain,(
% 29.38/4.10    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)))) ) | (~spl2_81 | ~spl2_108)),
% 29.38/4.10    inference(superposition,[],[f6013,f14812])).
% 29.38/4.10  fof(f14812,plain,(
% 29.38/4.10    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23)))) ) | ~spl2_108),
% 29.38/4.10    inference(avatar_component_clause,[],[f14811])).
% 29.38/4.10  fof(f6013,plain,(
% 29.38/4.10    ( ! [X10,X8,X9] : (k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))) ) | ~spl2_81),
% 29.38/4.10    inference(avatar_component_clause,[],[f6012])).
% 29.38/4.10  fof(f33302,plain,(
% 29.38/4.10    spl2_154 | ~spl2_28 | ~spl2_76),
% 29.38/4.10    inference(avatar_split_clause,[],[f7506,f4493,f473,f33300])).
% 29.38/4.10  fof(f4493,plain,(
% 29.38/4.10    spl2_76 <=> ! [X22,X23] : k4_xboole_0(X23,X22) = k5_xboole_0(k5_xboole_0(X22,X23),k4_xboole_0(X22,X23))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 29.38/4.10  fof(f7506,plain,(
% 29.38/4.10    ( ! [X68,X69] : (k4_xboole_0(X69,k5_xboole_0(X68,X69)) = k5_xboole_0(X68,k4_xboole_0(k5_xboole_0(X68,X69),X69))) ) | (~spl2_28 | ~spl2_76)),
% 29.38/4.10    inference(superposition,[],[f4494,f474])).
% 29.38/4.10  fof(f4494,plain,(
% 29.38/4.10    ( ! [X23,X22] : (k4_xboole_0(X23,X22) = k5_xboole_0(k5_xboole_0(X22,X23),k4_xboole_0(X22,X23))) ) | ~spl2_76),
% 29.38/4.10    inference(avatar_component_clause,[],[f4493])).
% 29.38/4.10  fof(f33294,plain,(
% 29.38/4.10    spl2_152 | ~spl2_27 | ~spl2_76),
% 29.38/4.10    inference(avatar_split_clause,[],[f7481,f4493,f449,f33292])).
% 29.38/4.10  fof(f449,plain,(
% 29.38/4.10    spl2_27 <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 29.38/4.10  fof(f7481,plain,(
% 29.38/4.10    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X11,X10),X10) = k5_xboole_0(X11,k4_xboole_0(X10,k5_xboole_0(X11,X10)))) ) | (~spl2_27 | ~spl2_76)),
% 29.38/4.10    inference(superposition,[],[f4494,f450])).
% 29.38/4.10  fof(f450,plain,(
% 29.38/4.10    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) ) | ~spl2_27),
% 29.38/4.10    inference(avatar_component_clause,[],[f449])).
% 29.38/4.10  fof(f14813,plain,(
% 29.38/4.10    spl2_108 | ~spl2_2 | ~spl2_26 | ~spl2_45 | ~spl2_59 | ~spl2_61 | ~spl2_81 | ~spl2_95),
% 29.38/4.10    inference(avatar_split_clause,[],[f14805,f8997,f6012,f3999,f2562,f1773,f416,f38,f14811])).
% 29.38/4.10  fof(f416,plain,(
% 29.38/4.10    spl2_26 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 29.38/4.10  fof(f1773,plain,(
% 29.38/4.10    spl2_45 <=> ! [X7,X8] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 29.38/4.10  fof(f3999,plain,(
% 29.38/4.10    spl2_61 <=> ! [X11,X13,X12] : k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 29.38/4.10  fof(f8997,plain,(
% 29.38/4.10    spl2_95 <=> ! [X18,X19] : k5_xboole_0(X19,k4_xboole_0(X19,X18)) = k5_xboole_0(k4_xboole_0(X18,X19),X18)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 29.38/4.10  fof(f14805,plain,(
% 29.38/4.10    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23)))) ) | (~spl2_2 | ~spl2_26 | ~spl2_45 | ~spl2_59 | ~spl2_61 | ~spl2_81 | ~spl2_95)),
% 29.38/4.10    inference(forward_demodulation,[],[f14804,f417])).
% 29.38/4.10  fof(f417,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_26),
% 29.38/4.10    inference(avatar_component_clause,[],[f416])).
% 29.38/4.10  fof(f14804,plain,(
% 29.38/4.10    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(X21,k5_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23)))))) ) | (~spl2_2 | ~spl2_45 | ~spl2_59 | ~spl2_61 | ~spl2_81 | ~spl2_95)),
% 29.38/4.10    inference(forward_demodulation,[],[f14803,f2563])).
% 29.38/4.10  fof(f14803,plain,(
% 29.38/4.10    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X21,X22)),X23)))) ) | (~spl2_2 | ~spl2_45 | ~spl2_61 | ~spl2_81 | ~spl2_95)),
% 29.38/4.10    inference(forward_demodulation,[],[f14802,f39])).
% 29.38/4.10  fof(f14802,plain,(
% 29.38/4.10    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X21,X22)),X23),X21))) ) | (~spl2_45 | ~spl2_61 | ~spl2_81 | ~spl2_95)),
% 29.38/4.10    inference(backward_demodulation,[],[f8580,f14655])).
% 29.38/4.10  fof(f14655,plain,(
% 29.38/4.10    ( ! [X215,X213,X214] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X213,X214),X215),X213) = k5_xboole_0(X214,k5_xboole_0(X215,k4_xboole_0(X215,k5_xboole_0(X213,X214))))) ) | (~spl2_61 | ~spl2_95)),
% 29.38/4.10    inference(superposition,[],[f4000,f8998])).
% 29.38/4.10  fof(f8998,plain,(
% 29.38/4.10    ( ! [X19,X18] : (k5_xboole_0(X19,k4_xboole_0(X19,X18)) = k5_xboole_0(k4_xboole_0(X18,X19),X18)) ) | ~spl2_95),
% 29.38/4.10    inference(avatar_component_clause,[],[f8997])).
% 29.38/4.10  fof(f4000,plain,(
% 29.38/4.10    ( ! [X12,X13,X11] : (k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13)))) ) | ~spl2_61),
% 29.38/4.10    inference(avatar_component_clause,[],[f3999])).
% 29.38/4.10  fof(f8580,plain,(
% 29.38/4.10    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(k4_xboole_0(X21,X22),k5_xboole_0(X23,k4_xboole_0(X23,k5_xboole_0(X21,k4_xboole_0(X21,X22))))))) ) | (~spl2_45 | ~spl2_81)),
% 29.38/4.10    inference(superposition,[],[f6013,f1774])).
% 29.38/4.10  fof(f1774,plain,(
% 29.38/4.10    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) ) | ~spl2_45),
% 29.38/4.10    inference(avatar_component_clause,[],[f1773])).
% 29.38/4.10  fof(f9039,plain,(
% 29.38/4.10    spl2_105 | ~spl2_29 | ~spl2_76),
% 29.38/4.10    inference(avatar_split_clause,[],[f7556,f4493,f477,f9037])).
% 29.38/4.10  fof(f7556,plain,(
% 29.38/4.10    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22))) ) | (~spl2_29 | ~spl2_76)),
% 29.38/4.10    inference(superposition,[],[f478,f4494])).
% 29.38/4.10  fof(f9035,plain,(
% 29.38/4.10    spl2_104 | ~spl2_44 | ~spl2_61),
% 29.38/4.10    inference(avatar_split_clause,[],[f4561,f3999,f1098,f9033])).
% 29.38/4.10  fof(f1098,plain,(
% 29.38/4.10    spl2_44 <=> ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 29.38/4.10  fof(f4561,plain,(
% 29.38/4.10    ( ! [X37,X36] : (k5_xboole_0(X36,X37) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X37,X36))) ) | (~spl2_44 | ~spl2_61)),
% 29.38/4.10    inference(superposition,[],[f4000,f1099])).
% 29.38/4.10  fof(f1099,plain,(
% 29.38/4.10    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))) ) | ~spl2_44),
% 29.38/4.10    inference(avatar_component_clause,[],[f1098])).
% 29.38/4.10  fof(f8999,plain,(
% 29.38/4.10    spl2_95 | ~spl2_29 | ~spl2_33),
% 29.38/4.10    inference(avatar_split_clause,[],[f963,f536,f477,f8997])).
% 29.38/4.10  fof(f963,plain,(
% 29.38/4.10    ( ! [X19,X18] : (k5_xboole_0(X19,k4_xboole_0(X19,X18)) = k5_xboole_0(k4_xboole_0(X18,X19),X18)) ) | (~spl2_29 | ~spl2_33)),
% 29.38/4.10    inference(superposition,[],[f478,f537])).
% 29.38/4.10  fof(f6014,plain,(
% 29.38/4.10    spl2_81 | ~spl2_5 | ~spl2_59),
% 29.38/4.10    inference(avatar_split_clause,[],[f4074,f2562,f52,f6012])).
% 29.38/4.10  fof(f52,plain,(
% 29.38/4.10    spl2_5 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 29.38/4.10  fof(f4074,plain,(
% 29.38/4.10    ( ! [X10,X8,X9] : (k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))) ) | (~spl2_5 | ~spl2_59)),
% 29.38/4.10    inference(superposition,[],[f53,f2563])).
% 29.38/4.10  fof(f53,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl2_5),
% 29.38/4.10    inference(avatar_component_clause,[],[f52])).
% 29.38/4.10  fof(f4511,plain,(
% 29.38/4.10    spl2_80 | ~spl2_56 | ~spl2_57),
% 29.38/4.10    inference(avatar_split_clause,[],[f3794,f1821,f1817,f4509])).
% 29.38/4.10  fof(f1817,plain,(
% 29.38/4.10    spl2_56 <=> ! [X3,X4] : k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3)) = X3),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 29.38/4.10  fof(f1821,plain,(
% 29.38/4.10    spl2_57 <=> ! [X22,X21] : k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(X22,X21))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 29.38/4.10  fof(f3794,plain,(
% 29.38/4.10    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8) ) | (~spl2_56 | ~spl2_57)),
% 29.38/4.10    inference(superposition,[],[f1818,f1822])).
% 29.38/4.10  fof(f1822,plain,(
% 29.38/4.10    ( ! [X21,X22] : (k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(X22,X21))) ) | ~spl2_57),
% 29.38/4.10    inference(avatar_component_clause,[],[f1821])).
% 29.38/4.10  fof(f1818,plain,(
% 29.38/4.10    ( ! [X4,X3] : (k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3)) = X3) ) | ~spl2_56),
% 29.38/4.10    inference(avatar_component_clause,[],[f1817])).
% 29.38/4.10  fof(f4495,plain,(
% 29.38/4.10    spl2_76 | ~spl2_33 | ~spl2_46),
% 29.38/4.10    inference(avatar_split_clause,[],[f1995,f1777,f536,f4493])).
% 29.38/4.10  fof(f1777,plain,(
% 29.38/4.10    spl2_46 <=> ! [X11,X13,X12] : k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 29.38/4.10  fof(f1995,plain,(
% 29.38/4.10    ( ! [X23,X22] : (k4_xboole_0(X23,X22) = k5_xboole_0(k5_xboole_0(X22,X23),k4_xboole_0(X22,X23))) ) | (~spl2_33 | ~spl2_46)),
% 29.38/4.10    inference(superposition,[],[f1778,f537])).
% 29.38/4.10  fof(f1778,plain,(
% 29.38/4.10    ( ! [X12,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13) ) | ~spl2_46),
% 29.38/4.10    inference(avatar_component_clause,[],[f1777])).
% 29.38/4.10  fof(f4025,plain,(
% 29.38/4.10    spl2_67 | ~spl2_27 | ~spl2_33),
% 29.38/4.10    inference(avatar_split_clause,[],[f961,f536,f449,f4023])).
% 29.38/4.10  fof(f961,plain,(
% 29.38/4.10    ( ! [X14,X15] : (k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)) = X14) ) | (~spl2_27 | ~spl2_33)),
% 29.38/4.10    inference(superposition,[],[f450,f537])).
% 29.38/4.10  fof(f4001,plain,(
% 29.38/4.10    spl2_61 | ~spl2_12 | ~spl2_27),
% 29.38/4.10    inference(avatar_split_clause,[],[f460,f449,f121,f3999])).
% 29.38/4.10  fof(f460,plain,(
% 29.38/4.10    ( ! [X12,X13,X11] : (k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13)))) ) | (~spl2_12 | ~spl2_27)),
% 29.38/4.10    inference(superposition,[],[f450,f122])).
% 29.38/4.10  fof(f2564,plain,(
% 29.38/4.10    spl2_59 | ~spl2_16 | ~spl2_26),
% 29.38/4.10    inference(avatar_split_clause,[],[f441,f416,f165,f2562])).
% 29.38/4.10  fof(f165,plain,(
% 29.38/4.10    spl2_16 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 29.38/4.10  fof(f441,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | (~spl2_16 | ~spl2_26)),
% 29.38/4.10    inference(forward_demodulation,[],[f433,f422])).
% 29.38/4.10  fof(f422,plain,(
% 29.38/4.10    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) ) | (~spl2_16 | ~spl2_26)),
% 29.38/4.10    inference(superposition,[],[f417,f166])).
% 29.38/4.10  fof(f166,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_16),
% 29.38/4.10    inference(avatar_component_clause,[],[f165])).
% 29.38/4.10  fof(f433,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | (~spl2_16 | ~spl2_26)),
% 29.38/4.10    inference(backward_demodulation,[],[f32,f422])).
% 29.38/4.10  fof(f32,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 29.38/4.10    inference(definition_unfolding,[],[f25,f23,f23])).
% 29.38/4.10  fof(f23,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 29.38/4.10    inference(cnf_transformation,[],[f7])).
% 29.38/4.10  fof(f7,axiom,(
% 29.38/4.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 29.38/4.10  fof(f25,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 29.38/4.10    inference(cnf_transformation,[],[f8])).
% 29.38/4.10  fof(f8,axiom,(
% 29.38/4.10    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 29.38/4.10  fof(f1823,plain,(
% 29.38/4.10    spl2_57 | ~spl2_26 | ~spl2_44),
% 29.38/4.10    inference(avatar_split_clause,[],[f1710,f1098,f416,f1821])).
% 29.38/4.10  fof(f1710,plain,(
% 29.38/4.10    ( ! [X21,X22] : (k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(X22,X21))) ) | (~spl2_26 | ~spl2_44)),
% 29.38/4.10    inference(superposition,[],[f417,f1099])).
% 29.38/4.10  fof(f1819,plain,(
% 29.38/4.10    spl2_56 | ~spl2_1 | ~spl2_5 | ~spl2_17 | ~spl2_43),
% 29.38/4.10    inference(avatar_split_clause,[],[f1677,f1094,f169,f52,f34,f1817])).
% 29.38/4.10  fof(f34,plain,(
% 29.38/4.10    spl2_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 29.38/4.10  fof(f169,plain,(
% 29.38/4.10    spl2_17 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 29.38/4.10  fof(f1094,plain,(
% 29.38/4.10    spl2_43 <=> ! [X1,X2] : k4_xboole_0(X2,X1) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 29.38/4.10  fof(f1677,plain,(
% 29.38/4.10    ( ! [X4,X3] : (k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3)) = X3) ) | (~spl2_1 | ~spl2_5 | ~spl2_17 | ~spl2_43)),
% 29.38/4.10    inference(forward_demodulation,[],[f1676,f35])).
% 29.38/4.10  fof(f35,plain,(
% 29.38/4.10    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 29.38/4.10    inference(avatar_component_clause,[],[f34])).
% 29.38/4.10  fof(f1676,plain,(
% 29.38/4.10    ( ! [X4,X3] : (k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3))) ) | (~spl2_5 | ~spl2_17 | ~spl2_43)),
% 29.38/4.10    inference(forward_demodulation,[],[f1658,f53])).
% 29.38/4.10  fof(f1658,plain,(
% 29.38/4.10    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X4,X3))) ) | (~spl2_17 | ~spl2_43)),
% 29.38/4.10    inference(superposition,[],[f170,f1095])).
% 29.38/4.10  fof(f1095,plain,(
% 29.38/4.10    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)) ) | ~spl2_43),
% 29.38/4.10    inference(avatar_component_clause,[],[f1094])).
% 29.38/4.10  fof(f170,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_17),
% 29.38/4.10    inference(avatar_component_clause,[],[f169])).
% 29.38/4.10  fof(f1795,plain,(
% 29.38/4.10    spl2_50 | ~spl2_26 | ~spl2_33),
% 29.38/4.10    inference(avatar_split_clause,[],[f960,f536,f416,f1793])).
% 29.38/4.10  fof(f960,plain,(
% 29.38/4.10    ( ! [X12,X13] : (k5_xboole_0(X13,k4_xboole_0(X13,X12)) = k5_xboole_0(X12,k4_xboole_0(X12,X13))) ) | (~spl2_26 | ~spl2_33)),
% 29.38/4.10    inference(superposition,[],[f417,f537])).
% 29.38/4.10  fof(f1779,plain,(
% 29.38/4.10    spl2_46 | ~spl2_12 | ~spl2_26),
% 29.38/4.10    inference(avatar_split_clause,[],[f426,f416,f121,f1777])).
% 29.38/4.10  fof(f426,plain,(
% 29.38/4.10    ( ! [X12,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13) ) | (~spl2_12 | ~spl2_26)),
% 29.38/4.10    inference(superposition,[],[f417,f122])).
% 29.38/4.10  fof(f1775,plain,(
% 29.38/4.10    spl2_45 | ~spl2_16 | ~spl2_26),
% 29.38/4.10    inference(avatar_split_clause,[],[f422,f416,f165,f1773])).
% 29.38/4.10  fof(f1100,plain,(
% 29.38/4.10    spl2_44 | ~spl2_2 | ~spl2_32 | ~spl2_33),
% 29.38/4.10    inference(avatar_split_clause,[],[f990,f536,f532,f38,f1098])).
% 29.38/4.10  fof(f990,plain,(
% 29.38/4.10    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))) ) | (~spl2_2 | ~spl2_32 | ~spl2_33)),
% 29.38/4.10    inference(forward_demodulation,[],[f953,f39])).
% 29.38/4.10  fof(f953,plain,(
% 29.38/4.10    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X6,X5),X5))) ) | (~spl2_32 | ~spl2_33)),
% 29.38/4.10    inference(superposition,[],[f537,f533])).
% 29.38/4.10  fof(f1096,plain,(
% 29.38/4.10    spl2_43 | ~spl2_2 | ~spl2_5 | ~spl2_12 | ~spl2_25 | ~spl2_29 | ~spl2_33),
% 29.38/4.10    inference(avatar_split_clause,[],[f977,f536,f477,f402,f121,f52,f38,f1094])).
% 29.38/4.10  fof(f977,plain,(
% 29.38/4.10    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)) ) | (~spl2_2 | ~spl2_5 | ~spl2_12 | ~spl2_25 | ~spl2_29 | ~spl2_33)),
% 29.38/4.10    inference(forward_demodulation,[],[f976,f403])).
% 29.38/4.10  fof(f976,plain,(
% 29.38/4.10    ( ! [X2,X1] : (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))) ) | (~spl2_2 | ~spl2_5 | ~spl2_12 | ~spl2_29 | ~spl2_33)),
% 29.38/4.10    inference(forward_demodulation,[],[f975,f39])).
% 29.38/4.10  fof(f975,plain,(
% 29.38/4.10    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X2,X1),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)) ) | (~spl2_5 | ~spl2_12 | ~spl2_29 | ~spl2_33)),
% 29.38/4.10    inference(forward_demodulation,[],[f945,f519])).
% 29.38/4.10  fof(f519,plain,(
% 29.38/4.10    ( ! [X8,X7,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X9))) ) | (~spl2_12 | ~spl2_29)),
% 29.38/4.10    inference(superposition,[],[f122,f478])).
% 29.38/4.10  fof(f945,plain,(
% 29.38/4.10    ( ! [X2,X1] : (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k5_xboole_0(X1,k1_xboole_0))) ) | (~spl2_5 | ~spl2_33)),
% 29.38/4.10    inference(superposition,[],[f537,f53])).
% 29.38/4.10  fof(f1084,plain,(
% 29.38/4.10    spl2_40 | ~spl2_12 | ~spl2_31),
% 29.38/4.10    inference(avatar_split_clause,[],[f551,f528,f121,f1082])).
% 29.38/4.10  fof(f528,plain,(
% 29.38/4.10    spl2_31 <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 29.38/4.10  fof(f551,plain,(
% 29.38/4.10    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | (~spl2_12 | ~spl2_31)),
% 29.38/4.10    inference(superposition,[],[f529,f122])).
% 29.38/4.10  fof(f529,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) ) | ~spl2_31),
% 29.38/4.10    inference(avatar_component_clause,[],[f528])).
% 29.38/4.10  fof(f729,plain,(
% 29.38/4.10    ~spl2_34 | ~spl2_16 | ~spl2_26),
% 29.38/4.10    inference(avatar_split_clause,[],[f440,f416,f165,f726])).
% 29.38/4.10  fof(f440,plain,(
% 29.38/4.10    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_16 | ~spl2_26)),
% 29.38/4.10    inference(backward_demodulation,[],[f28,f422])).
% 29.38/4.10  fof(f28,plain,(
% 29.38/4.10    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 29.38/4.10    inference(definition_unfolding,[],[f16,f22,f23])).
% 29.38/4.10  fof(f22,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 29.38/4.10    inference(cnf_transformation,[],[f10])).
% 29.38/4.10  fof(f10,axiom,(
% 29.38/4.10    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 29.38/4.10  fof(f16,plain,(
% 29.38/4.10    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 29.38/4.10    inference(cnf_transformation,[],[f15])).
% 29.38/4.10  fof(f15,plain,(
% 29.38/4.10    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 29.38/4.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 29.38/4.10  fof(f14,plain,(
% 29.38/4.10    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 29.38/4.10    introduced(choice_axiom,[])).
% 29.38/4.10  fof(f13,plain,(
% 29.38/4.10    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 29.38/4.10    inference(ennf_transformation,[],[f12])).
% 29.38/4.10  fof(f12,negated_conjecture,(
% 29.38/4.10    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 29.38/4.10    inference(negated_conjecture,[],[f11])).
% 29.38/4.10  fof(f11,conjecture,(
% 29.38/4.10    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 29.38/4.10  fof(f538,plain,(
% 29.38/4.10    spl2_33 | ~spl2_16 | ~spl2_17 | ~spl2_26),
% 29.38/4.10    inference(avatar_split_clause,[],[f436,f416,f169,f165,f536])).
% 29.38/4.10  fof(f436,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_16 | ~spl2_17 | ~spl2_26)),
% 29.38/4.10    inference(backward_demodulation,[],[f358,f422])).
% 29.38/4.10  fof(f358,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_16 | ~spl2_17)),
% 29.38/4.10    inference(superposition,[],[f166,f170])).
% 29.38/4.10  fof(f534,plain,(
% 29.38/4.10    spl2_32 | ~spl2_2 | ~spl2_12),
% 29.38/4.10    inference(avatar_split_clause,[],[f183,f121,f38,f532])).
% 29.38/4.10  fof(f183,plain,(
% 29.38/4.10    ( ! [X6,X7,X5] : (k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))) ) | (~spl2_2 | ~spl2_12)),
% 29.38/4.10    inference(superposition,[],[f122,f39])).
% 29.38/4.10  fof(f530,plain,(
% 29.38/4.10    spl2_31 | ~spl2_2 | ~spl2_12),
% 29.38/4.10    inference(avatar_split_clause,[],[f172,f121,f38,f528])).
% 29.38/4.10  fof(f172,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) ) | (~spl2_2 | ~spl2_12)),
% 29.38/4.10    inference(superposition,[],[f122,f39])).
% 29.38/4.10  fof(f479,plain,(
% 29.38/4.10    spl2_29 | ~spl2_27),
% 29.38/4.10    inference(avatar_split_clause,[],[f456,f449,f477])).
% 29.38/4.10  fof(f456,plain,(
% 29.38/4.10    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) ) | ~spl2_27),
% 29.38/4.10    inference(superposition,[],[f450,f450])).
% 29.38/4.10  fof(f475,plain,(
% 29.38/4.10    spl2_28 | ~spl2_26 | ~spl2_27),
% 29.38/4.10    inference(avatar_split_clause,[],[f455,f449,f416,f473])).
% 29.38/4.10  fof(f455,plain,(
% 29.38/4.10    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) ) | (~spl2_26 | ~spl2_27)),
% 29.38/4.10    inference(superposition,[],[f450,f417])).
% 29.38/4.10  fof(f451,plain,(
% 29.38/4.10    spl2_27 | ~spl2_2 | ~spl2_26),
% 29.38/4.10    inference(avatar_split_clause,[],[f420,f416,f38,f449])).
% 29.38/4.10  fof(f420,plain,(
% 29.38/4.10    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) ) | (~spl2_2 | ~spl2_26)),
% 29.38/4.10    inference(superposition,[],[f417,f39])).
% 29.38/4.10  fof(f418,plain,(
% 29.38/4.10    spl2_26 | ~spl2_1 | ~spl2_6 | ~spl2_12 | ~spl2_15 | ~spl2_16 | ~spl2_23),
% 29.38/4.10    inference(avatar_split_clause,[],[f376,f353,f165,f141,f121,f62,f34,f416])).
% 29.38/4.10  fof(f62,plain,(
% 29.38/4.10    spl2_6 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 29.38/4.10  fof(f141,plain,(
% 29.38/4.10    spl2_15 <=> ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 29.38/4.10  fof(f353,plain,(
% 29.38/4.10    spl2_23 <=> ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 29.38/4.10  fof(f376,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_1 | ~spl2_6 | ~spl2_12 | ~spl2_15 | ~spl2_16 | ~spl2_23)),
% 29.38/4.10    inference(forward_demodulation,[],[f374,f309])).
% 29.38/4.10  fof(f309,plain,(
% 29.38/4.10    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl2_1 | ~spl2_6 | ~spl2_15 | ~spl2_16)),
% 29.38/4.10    inference(backward_demodulation,[],[f142,f305])).
% 29.38/4.10  fof(f305,plain,(
% 29.38/4.10    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_1 | ~spl2_6 | ~spl2_16)),
% 29.38/4.10    inference(forward_demodulation,[],[f286,f63])).
% 29.38/4.10  fof(f63,plain,(
% 29.38/4.10    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_6),
% 29.38/4.10    inference(avatar_component_clause,[],[f62])).
% 29.38/4.10  fof(f286,plain,(
% 29.38/4.10    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_1 | ~spl2_16)),
% 29.38/4.10    inference(superposition,[],[f166,f35])).
% 29.38/4.10  fof(f142,plain,(
% 29.38/4.10    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) ) | ~spl2_15),
% 29.38/4.10    inference(avatar_component_clause,[],[f141])).
% 29.38/4.10  fof(f374,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_12 | ~spl2_23)),
% 29.38/4.10    inference(superposition,[],[f122,f354])).
% 29.38/4.10  fof(f354,plain,(
% 29.38/4.10    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | ~spl2_23),
% 29.38/4.10    inference(avatar_component_clause,[],[f353])).
% 29.38/4.10  fof(f404,plain,(
% 29.38/4.10    spl2_25 | ~spl2_1 | ~spl2_6 | ~spl2_15 | ~spl2_16),
% 29.38/4.10    inference(avatar_split_clause,[],[f309,f165,f141,f62,f34,f402])).
% 29.38/4.10  fof(f355,plain,(
% 29.38/4.10    spl2_23 | ~spl2_1 | ~spl2_5 | ~spl2_16),
% 29.38/4.10    inference(avatar_split_clause,[],[f333,f165,f52,f34,f353])).
% 29.38/4.10  fof(f333,plain,(
% 29.38/4.10    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | (~spl2_1 | ~spl2_5 | ~spl2_16)),
% 29.38/4.10    inference(forward_demodulation,[],[f287,f35])).
% 29.38/4.10  fof(f287,plain,(
% 29.38/4.10    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl2_5 | ~spl2_16)),
% 29.38/4.10    inference(superposition,[],[f166,f53])).
% 29.38/4.10  fof(f171,plain,(
% 29.38/4.10    spl2_17),
% 29.38/4.10    inference(avatar_split_clause,[],[f31,f169])).
% 29.38/4.10  fof(f31,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 29.38/4.10    inference(definition_unfolding,[],[f20,f23,f23])).
% 29.38/4.10  fof(f20,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 29.38/4.10    inference(cnf_transformation,[],[f1])).
% 29.38/4.10  fof(f1,axiom,(
% 29.38/4.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 29.38/4.10  fof(f167,plain,(
% 29.38/4.10    spl2_16),
% 29.38/4.10    inference(avatar_split_clause,[],[f27,f165])).
% 29.38/4.10  fof(f27,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 29.38/4.10    inference(definition_unfolding,[],[f24,f23])).
% 29.38/4.10  fof(f24,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 29.38/4.10    inference(cnf_transformation,[],[f3])).
% 29.38/4.10  fof(f3,axiom,(
% 29.38/4.10    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 29.38/4.10  fof(f143,plain,(
% 29.38/4.10    spl2_15 | ~spl2_2 | ~spl2_13),
% 29.38/4.10    inference(avatar_split_clause,[],[f130,f125,f38,f141])).
% 29.38/4.10  fof(f125,plain,(
% 29.38/4.10    spl2_13 <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 29.38/4.10  fof(f130,plain,(
% 29.38/4.10    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) ) | (~spl2_2 | ~spl2_13)),
% 29.38/4.10    inference(superposition,[],[f126,f39])).
% 29.38/4.10  fof(f126,plain,(
% 29.38/4.10    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))) ) | ~spl2_13),
% 29.38/4.10    inference(avatar_component_clause,[],[f125])).
% 29.38/4.10  fof(f127,plain,(
% 29.38/4.10    spl2_13 | ~spl2_2 | ~spl2_11),
% 29.38/4.10    inference(avatar_split_clause,[],[f114,f107,f38,f125])).
% 29.38/4.10  fof(f107,plain,(
% 29.38/4.10    spl2_11 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0)),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 29.38/4.10  fof(f114,plain,(
% 29.38/4.10    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))) ) | (~spl2_2 | ~spl2_11)),
% 29.38/4.10    inference(superposition,[],[f108,f39])).
% 29.38/4.10  fof(f108,plain,(
% 29.38/4.10    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl2_11),
% 29.38/4.10    inference(avatar_component_clause,[],[f107])).
% 29.38/4.10  fof(f123,plain,(
% 29.38/4.10    spl2_12),
% 29.38/4.10    inference(avatar_split_clause,[],[f26,f121])).
% 29.38/4.10  fof(f26,plain,(
% 29.38/4.10    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 29.38/4.10    inference(cnf_transformation,[],[f9])).
% 29.38/4.10  fof(f9,axiom,(
% 29.38/4.10    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 29.38/4.10  fof(f109,plain,(
% 29.38/4.10    spl2_11 | ~spl2_1 | ~spl2_3 | ~spl2_5),
% 29.38/4.10    inference(avatar_split_clause,[],[f60,f52,f42,f34,f107])).
% 29.38/4.10  fof(f42,plain,(
% 29.38/4.10    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0),
% 29.38/4.10    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 29.38/4.10  fof(f60,plain,(
% 29.38/4.10    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl2_1 | ~spl2_3 | ~spl2_5)),
% 29.38/4.10    inference(forward_demodulation,[],[f58,f35])).
% 29.38/4.10  fof(f58,plain,(
% 29.38/4.10    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0)) ) | (~spl2_3 | ~spl2_5)),
% 29.38/4.10    inference(superposition,[],[f43,f53])).
% 29.38/4.10  fof(f43,plain,(
% 29.38/4.10    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) ) | ~spl2_3),
% 29.38/4.10    inference(avatar_component_clause,[],[f42])).
% 29.38/4.10  fof(f64,plain,(
% 29.38/4.10    spl2_6 | ~spl2_3 | ~spl2_5),
% 29.38/4.10    inference(avatar_split_clause,[],[f57,f52,f42,f62])).
% 29.38/4.10  fof(f57,plain,(
% 29.38/4.10    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_3 | ~spl2_5)),
% 29.38/4.10    inference(superposition,[],[f53,f43])).
% 29.38/4.10  fof(f54,plain,(
% 29.38/4.10    spl2_5),
% 29.38/4.10    inference(avatar_split_clause,[],[f30,f52])).
% 29.38/4.10  fof(f30,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 29.38/4.10    inference(definition_unfolding,[],[f19,f22])).
% 29.38/4.10  fof(f19,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 29.38/4.10    inference(cnf_transformation,[],[f6])).
% 29.38/4.10  fof(f6,axiom,(
% 29.38/4.10    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 29.38/4.10  fof(f44,plain,(
% 29.38/4.10    spl2_3),
% 29.38/4.10    inference(avatar_split_clause,[],[f29,f42])).
% 29.38/4.10  fof(f29,plain,(
% 29.38/4.10    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 29.38/4.10    inference(definition_unfolding,[],[f17,f22])).
% 29.38/4.10  fof(f17,plain,(
% 29.38/4.10    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 29.38/4.10    inference(cnf_transformation,[],[f4])).
% 29.38/4.10  fof(f4,axiom,(
% 29.38/4.10    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 29.38/4.10  fof(f40,plain,(
% 29.38/4.10    spl2_2),
% 29.38/4.10    inference(avatar_split_clause,[],[f21,f38])).
% 29.38/4.10  fof(f21,plain,(
% 29.38/4.10    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 29.38/4.10    inference(cnf_transformation,[],[f2])).
% 29.38/4.10  fof(f2,axiom,(
% 29.38/4.10    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 29.38/4.10  fof(f36,plain,(
% 29.38/4.10    spl2_1),
% 29.38/4.10    inference(avatar_split_clause,[],[f18,f34])).
% 29.38/4.10  fof(f18,plain,(
% 29.38/4.10    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 29.38/4.10    inference(cnf_transformation,[],[f5])).
% 29.38/4.10  fof(f5,axiom,(
% 29.38/4.10    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 29.38/4.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 29.38/4.10  % SZS output end Proof for theBenchmark
% 29.38/4.10  % (31385)------------------------------
% 29.38/4.10  % (31385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.38/4.10  % (31385)Termination reason: Refutation
% 29.38/4.10  
% 29.38/4.10  % (31385)Memory used [KB]: 104774
% 29.38/4.10  % (31385)Time elapsed: 3.690 s
% 29.38/4.10  % (31385)------------------------------
% 29.38/4.10  % (31385)------------------------------
% 29.96/4.11  % (31377)Success in time 3.753 s
%------------------------------------------------------------------------------
