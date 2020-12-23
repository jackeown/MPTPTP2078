%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:45 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 272 expanded)
%              Number of leaves         :   47 ( 142 expanded)
%              Depth                    :    6
%              Number of atoms          :  343 ( 567 expanded)
%              Number of equality atoms :  126 ( 238 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9838,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f57,f69,f75,f79,f83,f87,f91,f167,f171,f177,f181,f187,f191,f222,f246,f327,f1025,f1035,f1043,f1048,f1242,f1300,f1364,f2062,f2078,f2086,f2162,f2346,f4624,f9560,f9579,f9837])).

fof(f9837,plain,
    ( ~ spl3_46
    | spl3_165 ),
    inference(avatar_contradiction_clause,[],[f9810])).

fof(f9810,plain,
    ( $false
    | ~ spl3_46
    | spl3_165 ),
    inference(unit_resulting_resolution,[],[f1363,f9578])).

fof(f9578,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK2,sK0,sK0)
    | spl3_165 ),
    inference(avatar_component_clause,[],[f9576])).

fof(f9576,plain,
    ( spl3_165
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).

fof(f1363,plain,
    ( ! [X57,X56,X55] : k1_enumset1(X55,X57,X56) = k2_enumset1(X57,X56,X55,X55)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f1362,plain,
    ( spl3_46
  <=> ! [X55,X56,X57] : k1_enumset1(X55,X57,X56) = k2_enumset1(X57,X56,X55,X55) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f9579,plain,
    ( ~ spl3_165
    | spl3_1
    | ~ spl3_163 ),
    inference(avatar_split_clause,[],[f9567,f9558,f42,f9576])).

fof(f42,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f9558,plain,
    ( spl3_163
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X2,X1,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).

fof(f9567,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK2,sK0,sK0)
    | spl3_1
    | ~ spl3_163 ),
    inference(superposition,[],[f44,f9559])).

fof(f9559,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X2,X1,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_163 ),
    inference(avatar_component_clause,[],[f9558])).

fof(f44,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f9560,plain,
    ( spl3_163
    | ~ spl3_4
    | ~ spl3_67
    | ~ spl3_98 ),
    inference(avatar_split_clause,[],[f4637,f4622,f2344,f55,f9558])).

fof(f55,plain,
    ( spl3_4
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2344,plain,
    ( spl3_67
  <=> ! [X193,X195,X192,X194] : k3_enumset1(X192,X193,X192,X194,X195) = k2_enumset1(X192,X194,X193,X195) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f4622,plain,
    ( spl3_98
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).

fof(f4637,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X2,X1,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_4
    | ~ spl3_67
    | ~ spl3_98 ),
    inference(forward_demodulation,[],[f4625,f2345])).

fof(f2345,plain,
    ( ! [X194,X192,X195,X193] : k3_enumset1(X192,X193,X192,X194,X195) = k2_enumset1(X192,X194,X193,X195)
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f2344])).

fof(f4625,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X0,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_4
    | ~ spl3_98 ),
    inference(superposition,[],[f4623,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f4623,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))
    | ~ spl3_98 ),
    inference(avatar_component_clause,[],[f4622])).

fof(f4624,plain,
    ( spl3_98
    | ~ spl3_14
    | ~ spl3_44
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f2208,f2160,f1240,f165,f4622])).

fof(f165,plain,
    ( spl3_14
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1240,plain,
    ( spl3_44
  <=> ! [X18,X17,X19] : k2_enumset1(X17,X17,X19,X18) = k1_enumset1(X17,X18,X19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f2160,plain,
    ( spl3_57
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f2208,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))
    | ~ spl3_14
    | ~ spl3_44
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f2163,f166])).

fof(f166,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f2163,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))
    | ~ spl3_44
    | ~ spl3_57 ),
    inference(superposition,[],[f2161,f1241])).

fof(f1241,plain,
    ( ! [X19,X17,X18] : k2_enumset1(X17,X17,X19,X18) = k1_enumset1(X17,X18,X19)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f2161,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f2160])).

fof(f2346,plain,
    ( spl3_67
    | ~ spl3_12
    | ~ spl3_44
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f2139,f2084,f1298,f1240,f89,f2344])).

fof(f89,plain,
    ( spl3_12
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1298,plain,
    ( spl3_45
  <=> ! [X20,X22,X21] : k2_enumset1(X20,X22,X20,X21) = k1_enumset1(X20,X22,X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f2084,plain,
    ( spl3_54
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f2139,plain,
    ( ! [X194,X192,X195,X193] : k3_enumset1(X192,X193,X192,X194,X195) = k2_enumset1(X192,X194,X193,X195)
    | ~ spl3_12
    | ~ spl3_44
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f2127,f2131])).

fof(f2131,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))
    | ~ spl3_12
    | ~ spl3_44
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f2087,f90])).

fof(f90,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f2087,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))
    | ~ spl3_44
    | ~ spl3_54 ),
    inference(superposition,[],[f2085,f1241])).

fof(f2085,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f2084])).

fof(f2127,plain,
    ( ! [X194,X192,X195,X193] : k3_enumset1(X192,X193,X192,X194,X195) = k2_xboole_0(k1_enumset1(X192,X193,X194),k1_tarski(X195))
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(superposition,[],[f2085,f1299])).

fof(f1299,plain,
    ( ! [X21,X22,X20] : k2_enumset1(X20,X22,X20,X21) = k1_enumset1(X20,X22,X21)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f2162,plain,
    ( spl3_57
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f2081,f2076,f169,f89,f2160])).

fof(f169,plain,
    ( spl3_15
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f2076,plain,
    ( spl3_53
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f2081,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f2079,f170])).

fof(f170,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f2079,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_12
    | ~ spl3_53 ),
    inference(superposition,[],[f2077,f90])).

fof(f2077,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f2076])).

fof(f2086,plain,
    ( spl3_54
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f2064,f2060,f165,f89,f2084])).

fof(f2060,plain,
    ( spl3_51
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f2064,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f2063,f166])).

fof(f2063,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl3_12
    | ~ spl3_51 ),
    inference(superposition,[],[f2061,f90])).

fof(f2061,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f2060])).

fof(f2078,plain,
    ( spl3_53
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f1051,f1046,f175,f165,f2076])).

fof(f175,plain,
    ( spl3_16
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1046,plain,
    ( spl3_39
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f1051,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f1049,f176])).

fof(f176,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1049,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl3_14
    | ~ spl3_39 ),
    inference(superposition,[],[f1047,f166])).

fof(f1047,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f2062,plain,
    ( spl3_51
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f1027,f1023,f169,f165,f2060])).

fof(f1023,plain,
    ( spl3_35
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f1027,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f1026,f170])).

fof(f1026,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl3_14
    | ~ spl3_35 ),
    inference(superposition,[],[f1024,f166])).

fof(f1024,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f1364,plain,
    ( spl3_46
    | ~ spl3_22
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f342,f325,f244,f1362])).

fof(f244,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f325,plain,
    ( spl3_26
  <=> ! [X11,X13,X12,X14] : k2_enumset1(X14,X13,X12,X11) = k2_enumset1(X11,X13,X14,X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f342,plain,
    ( ! [X57,X56,X55] : k1_enumset1(X55,X57,X56) = k2_enumset1(X57,X56,X55,X55)
    | ~ spl3_22
    | ~ spl3_26 ),
    inference(superposition,[],[f326,f245])).

fof(f245,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f244])).

fof(f326,plain,
    ( ! [X14,X12,X13,X11] : k2_enumset1(X14,X13,X12,X11) = k2_enumset1(X11,X13,X14,X12)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f325])).

fof(f1300,plain,
    ( spl3_45
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f254,f244,f85,f1298])).

fof(f85,plain,
    ( spl3_11
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f254,plain,
    ( ! [X21,X22,X20] : k2_enumset1(X20,X22,X20,X21) = k1_enumset1(X20,X22,X21)
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(superposition,[],[f245,f86])).

fof(f86,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1242,plain,
    ( spl3_44
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f229,f220,f81,f1240])).

fof(f81,plain,
    ( spl3_10
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f220,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f229,plain,
    ( ! [X19,X17,X18] : k2_enumset1(X17,X17,X19,X18) = k1_enumset1(X17,X18,X19)
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(superposition,[],[f221,f82])).

fof(f82,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f221,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f1048,plain,
    ( spl3_39
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f1044,f1041,f1033,f1046])).

fof(f1033,plain,
    ( spl3_37
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1041,plain,
    ( spl3_38
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f1044,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f1042,f1034])).

fof(f1034,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f1042,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f1041])).

fof(f1043,plain,
    ( spl3_38
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f192,f185,f169,f1041])).

fof(f185,plain,
    ( spl3_18
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f192,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(superposition,[],[f186,f170])).

fof(f186,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f1035,plain,
    ( spl3_37
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f200,f189,f179,f175,f1033])).

fof(f179,plain,
    ( spl3_17
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f189,plain,
    ( spl3_19
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f200,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f199,f180])).

fof(f180,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f179])).

fof(f199,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(superposition,[],[f190,f176])).

fof(f190,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f1025,plain,
    ( spl3_35
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f183,f179,f175,f169,f1023])).

fof(f183,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f182,f176])).

fof(f182,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(superposition,[],[f180,f170])).

fof(f327,plain,
    ( spl3_26
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f102,f77,f73,f325])).

fof(f73,plain,
    ( spl3_8
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f77,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f102,plain,
    ( ! [X14,X12,X13,X11] : k2_enumset1(X14,X13,X12,X11) = k2_enumset1(X11,X13,X14,X12)
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f78,f74])).

fof(f74,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f78,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f246,plain,
    ( spl3_22
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f104,f77,f67,f244])).

fof(f67,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f104,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f78,f68])).

fof(f68,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f222,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f100,f77,f67,f220])).

fof(f100,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f78,f68])).

fof(f191,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f40,f189])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(f187,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f39,f185])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f181,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f38,f179])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f177,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f37,f175])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f171,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f36,f169])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f167,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f35,f165])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f91,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f34,f89])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f87,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f83,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f79,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f75,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:18:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (26208)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (26216)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (26205)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (26209)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (26218)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (26206)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (26202)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (26201)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (26215)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (26210)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (26212)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (26204)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (26213)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (26207)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (26217)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (26212)Refutation not found, incomplete strategy% (26212)------------------------------
% 0.21/0.53  % (26212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26212)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26212)Memory used [KB]: 10618
% 0.21/0.53  % (26212)Time elapsed: 0.087 s
% 0.21/0.53  % (26212)------------------------------
% 0.21/0.53  % (26212)------------------------------
% 0.21/0.54  % (26203)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.56  % (26219)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.57  % (26211)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.60/0.94  % (26206)Refutation found. Thanks to Tanya!
% 4.60/0.94  % SZS status Theorem for theBenchmark
% 4.60/0.94  % SZS output start Proof for theBenchmark
% 4.60/0.94  fof(f9838,plain,(
% 4.60/0.94    $false),
% 4.60/0.94    inference(avatar_sat_refutation,[],[f45,f57,f69,f75,f79,f83,f87,f91,f167,f171,f177,f181,f187,f191,f222,f246,f327,f1025,f1035,f1043,f1048,f1242,f1300,f1364,f2062,f2078,f2086,f2162,f2346,f4624,f9560,f9579,f9837])).
% 4.60/0.94  fof(f9837,plain,(
% 4.60/0.94    ~spl3_46 | spl3_165),
% 4.60/0.94    inference(avatar_contradiction_clause,[],[f9810])).
% 4.60/0.94  fof(f9810,plain,(
% 4.60/0.94    $false | (~spl3_46 | spl3_165)),
% 4.60/0.94    inference(unit_resulting_resolution,[],[f1363,f9578])).
% 4.60/0.94  fof(f9578,plain,(
% 4.60/0.94    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK2,sK0,sK0) | spl3_165),
% 4.60/0.94    inference(avatar_component_clause,[],[f9576])).
% 4.60/0.94  fof(f9576,plain,(
% 4.60/0.94    spl3_165 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK2,sK0,sK0)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).
% 4.60/0.94  fof(f1363,plain,(
% 4.60/0.94    ( ! [X57,X56,X55] : (k1_enumset1(X55,X57,X56) = k2_enumset1(X57,X56,X55,X55)) ) | ~spl3_46),
% 4.60/0.94    inference(avatar_component_clause,[],[f1362])).
% 4.60/0.94  fof(f1362,plain,(
% 4.60/0.94    spl3_46 <=> ! [X55,X56,X57] : k1_enumset1(X55,X57,X56) = k2_enumset1(X57,X56,X55,X55)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 4.60/0.94  fof(f9579,plain,(
% 4.60/0.94    ~spl3_165 | spl3_1 | ~spl3_163),
% 4.60/0.94    inference(avatar_split_clause,[],[f9567,f9558,f42,f9576])).
% 4.60/0.94  fof(f42,plain,(
% 4.60/0.94    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.60/0.94  fof(f9558,plain,(
% 4.60/0.94    spl3_163 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X2,X1,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).
% 4.60/0.94  fof(f9567,plain,(
% 4.60/0.94    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK2,sK0,sK0) | (spl3_1 | ~spl3_163)),
% 4.60/0.94    inference(superposition,[],[f44,f9559])).
% 4.60/0.94  fof(f9559,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X2,X1,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_163),
% 4.60/0.94    inference(avatar_component_clause,[],[f9558])).
% 4.60/0.94  fof(f44,plain,(
% 4.60/0.94    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 4.60/0.94    inference(avatar_component_clause,[],[f42])).
% 4.60/0.94  fof(f9560,plain,(
% 4.60/0.94    spl3_163 | ~spl3_4 | ~spl3_67 | ~spl3_98),
% 4.60/0.94    inference(avatar_split_clause,[],[f4637,f4622,f2344,f55,f9558])).
% 4.60/0.94  fof(f55,plain,(
% 4.60/0.94    spl3_4 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.60/0.94  fof(f2344,plain,(
% 4.60/0.94    spl3_67 <=> ! [X193,X195,X192,X194] : k3_enumset1(X192,X193,X192,X194,X195) = k2_enumset1(X192,X194,X193,X195)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 4.60/0.94  fof(f4622,plain,(
% 4.60/0.94    spl3_98 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).
% 4.60/0.94  fof(f4637,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X2,X1,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_4 | ~spl3_67 | ~spl3_98)),
% 4.60/0.94    inference(forward_demodulation,[],[f4625,f2345])).
% 4.60/0.94  fof(f2345,plain,(
% 4.60/0.94    ( ! [X194,X192,X195,X193] : (k3_enumset1(X192,X193,X192,X194,X195) = k2_enumset1(X192,X194,X193,X195)) ) | ~spl3_67),
% 4.60/0.94    inference(avatar_component_clause,[],[f2344])).
% 4.60/0.94  fof(f4625,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X0,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_4 | ~spl3_98)),
% 4.60/0.94    inference(superposition,[],[f4623,f56])).
% 4.60/0.94  fof(f56,plain,(
% 4.60/0.94    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl3_4),
% 4.60/0.94    inference(avatar_component_clause,[],[f55])).
% 4.60/0.94  fof(f4623,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) ) | ~spl3_98),
% 4.60/0.94    inference(avatar_component_clause,[],[f4622])).
% 4.60/0.94  fof(f4624,plain,(
% 4.60/0.94    spl3_98 | ~spl3_14 | ~spl3_44 | ~spl3_57),
% 4.60/0.94    inference(avatar_split_clause,[],[f2208,f2160,f1240,f165,f4622])).
% 4.60/0.94  fof(f165,plain,(
% 4.60/0.94    spl3_14 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 4.60/0.94  fof(f1240,plain,(
% 4.60/0.94    spl3_44 <=> ! [X18,X17,X19] : k2_enumset1(X17,X17,X19,X18) = k1_enumset1(X17,X18,X19)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 4.60/0.94  fof(f2160,plain,(
% 4.60/0.94    spl3_57 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 4.60/0.94  fof(f2208,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) ) | (~spl3_14 | ~spl3_44 | ~spl3_57)),
% 4.60/0.94    inference(forward_demodulation,[],[f2163,f166])).
% 4.60/0.94  fof(f166,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) ) | ~spl3_14),
% 4.60/0.94    inference(avatar_component_clause,[],[f165])).
% 4.60/0.94  fof(f2163,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) ) | (~spl3_44 | ~spl3_57)),
% 4.60/0.94    inference(superposition,[],[f2161,f1241])).
% 4.60/0.94  fof(f1241,plain,(
% 4.60/0.94    ( ! [X19,X17,X18] : (k2_enumset1(X17,X17,X19,X18) = k1_enumset1(X17,X18,X19)) ) | ~spl3_44),
% 4.60/0.94    inference(avatar_component_clause,[],[f1240])).
% 4.60/0.94  fof(f2161,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | ~spl3_57),
% 4.60/0.94    inference(avatar_component_clause,[],[f2160])).
% 4.60/0.94  fof(f2346,plain,(
% 4.60/0.94    spl3_67 | ~spl3_12 | ~spl3_44 | ~spl3_45 | ~spl3_54),
% 4.60/0.94    inference(avatar_split_clause,[],[f2139,f2084,f1298,f1240,f89,f2344])).
% 4.60/0.94  fof(f89,plain,(
% 4.60/0.94    spl3_12 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 4.60/0.94  fof(f1298,plain,(
% 4.60/0.94    spl3_45 <=> ! [X20,X22,X21] : k2_enumset1(X20,X22,X20,X21) = k1_enumset1(X20,X22,X21)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 4.60/0.94  fof(f2084,plain,(
% 4.60/0.94    spl3_54 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 4.60/0.94  fof(f2139,plain,(
% 4.60/0.94    ( ! [X194,X192,X195,X193] : (k3_enumset1(X192,X193,X192,X194,X195) = k2_enumset1(X192,X194,X193,X195)) ) | (~spl3_12 | ~spl3_44 | ~spl3_45 | ~spl3_54)),
% 4.60/0.94    inference(forward_demodulation,[],[f2127,f2131])).
% 4.60/0.94  fof(f2131,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) ) | (~spl3_12 | ~spl3_44 | ~spl3_54)),
% 4.60/0.94    inference(forward_demodulation,[],[f2087,f90])).
% 4.60/0.94  fof(f90,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl3_12),
% 4.60/0.94    inference(avatar_component_clause,[],[f89])).
% 4.60/0.94  fof(f2087,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) ) | (~spl3_44 | ~spl3_54)),
% 4.60/0.94    inference(superposition,[],[f2085,f1241])).
% 4.60/0.94  fof(f2085,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | ~spl3_54),
% 4.60/0.94    inference(avatar_component_clause,[],[f2084])).
% 4.60/0.94  fof(f2127,plain,(
% 4.60/0.94    ( ! [X194,X192,X195,X193] : (k3_enumset1(X192,X193,X192,X194,X195) = k2_xboole_0(k1_enumset1(X192,X193,X194),k1_tarski(X195))) ) | (~spl3_45 | ~spl3_54)),
% 4.60/0.94    inference(superposition,[],[f2085,f1299])).
% 4.60/0.94  fof(f1299,plain,(
% 4.60/0.94    ( ! [X21,X22,X20] : (k2_enumset1(X20,X22,X20,X21) = k1_enumset1(X20,X22,X21)) ) | ~spl3_45),
% 4.60/0.94    inference(avatar_component_clause,[],[f1298])).
% 4.60/0.94  fof(f2162,plain,(
% 4.60/0.94    spl3_57 | ~spl3_12 | ~spl3_15 | ~spl3_53),
% 4.60/0.94    inference(avatar_split_clause,[],[f2081,f2076,f169,f89,f2160])).
% 4.60/0.94  fof(f169,plain,(
% 4.60/0.94    spl3_15 <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 4.60/0.94  fof(f2076,plain,(
% 4.60/0.94    spl3_53 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 4.60/0.94  fof(f2081,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl3_12 | ~spl3_15 | ~spl3_53)),
% 4.60/0.94    inference(forward_demodulation,[],[f2079,f170])).
% 4.60/0.94  fof(f170,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) ) | ~spl3_15),
% 4.60/0.94    inference(avatar_component_clause,[],[f169])).
% 4.60/0.94  fof(f2079,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl3_12 | ~spl3_53)),
% 4.60/0.94    inference(superposition,[],[f2077,f90])).
% 4.60/0.94  fof(f2077,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | ~spl3_53),
% 4.60/0.94    inference(avatar_component_clause,[],[f2076])).
% 4.60/0.94  fof(f2086,plain,(
% 4.60/0.94    spl3_54 | ~spl3_12 | ~spl3_14 | ~spl3_51),
% 4.60/0.94    inference(avatar_split_clause,[],[f2064,f2060,f165,f89,f2084])).
% 4.60/0.94  fof(f2060,plain,(
% 4.60/0.94    spl3_51 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 4.60/0.94  fof(f2064,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | (~spl3_12 | ~spl3_14 | ~spl3_51)),
% 4.60/0.94    inference(forward_demodulation,[],[f2063,f166])).
% 4.60/0.94  fof(f2063,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | (~spl3_12 | ~spl3_51)),
% 4.60/0.94    inference(superposition,[],[f2061,f90])).
% 4.60/0.94  fof(f2061,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | ~spl3_51),
% 4.60/0.94    inference(avatar_component_clause,[],[f2060])).
% 4.60/0.94  fof(f2078,plain,(
% 4.60/0.94    spl3_53 | ~spl3_14 | ~spl3_16 | ~spl3_39),
% 4.60/0.94    inference(avatar_split_clause,[],[f1051,f1046,f175,f165,f2076])).
% 4.60/0.94  fof(f175,plain,(
% 4.60/0.94    spl3_16 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 4.60/0.94  fof(f1046,plain,(
% 4.60/0.94    spl3_39 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 4.60/0.94  fof(f1051,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | (~spl3_14 | ~spl3_16 | ~spl3_39)),
% 4.60/0.94    inference(forward_demodulation,[],[f1049,f176])).
% 4.60/0.94  fof(f176,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) | ~spl3_16),
% 4.60/0.94    inference(avatar_component_clause,[],[f175])).
% 4.60/0.94  fof(f1049,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | (~spl3_14 | ~spl3_39)),
% 4.60/0.94    inference(superposition,[],[f1047,f166])).
% 4.60/0.94  fof(f1047,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ) | ~spl3_39),
% 4.60/0.94    inference(avatar_component_clause,[],[f1046])).
% 4.60/0.94  fof(f2062,plain,(
% 4.60/0.94    spl3_51 | ~spl3_14 | ~spl3_15 | ~spl3_35),
% 4.60/0.94    inference(avatar_split_clause,[],[f1027,f1023,f169,f165,f2060])).
% 4.60/0.94  fof(f1023,plain,(
% 4.60/0.94    spl3_35 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 4.60/0.94  fof(f1027,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | (~spl3_14 | ~spl3_15 | ~spl3_35)),
% 4.60/0.94    inference(forward_demodulation,[],[f1026,f170])).
% 4.60/0.94  fof(f1026,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | (~spl3_14 | ~spl3_35)),
% 4.60/0.94    inference(superposition,[],[f1024,f166])).
% 4.60/0.94  fof(f1024,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) ) | ~spl3_35),
% 4.60/0.94    inference(avatar_component_clause,[],[f1023])).
% 4.60/0.94  fof(f1364,plain,(
% 4.60/0.94    spl3_46 | ~spl3_22 | ~spl3_26),
% 4.60/0.94    inference(avatar_split_clause,[],[f342,f325,f244,f1362])).
% 4.60/0.94  fof(f244,plain,(
% 4.60/0.94    spl3_22 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 4.60/0.94  fof(f325,plain,(
% 4.60/0.94    spl3_26 <=> ! [X11,X13,X12,X14] : k2_enumset1(X14,X13,X12,X11) = k2_enumset1(X11,X13,X14,X12)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 4.60/0.94  fof(f342,plain,(
% 4.60/0.94    ( ! [X57,X56,X55] : (k1_enumset1(X55,X57,X56) = k2_enumset1(X57,X56,X55,X55)) ) | (~spl3_22 | ~spl3_26)),
% 4.60/0.94    inference(superposition,[],[f326,f245])).
% 4.60/0.94  fof(f245,plain,(
% 4.60/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) ) | ~spl3_22),
% 4.60/0.94    inference(avatar_component_clause,[],[f244])).
% 4.60/0.94  fof(f326,plain,(
% 4.60/0.94    ( ! [X14,X12,X13,X11] : (k2_enumset1(X14,X13,X12,X11) = k2_enumset1(X11,X13,X14,X12)) ) | ~spl3_26),
% 4.60/0.94    inference(avatar_component_clause,[],[f325])).
% 4.60/0.94  fof(f1300,plain,(
% 4.60/0.94    spl3_45 | ~spl3_11 | ~spl3_22),
% 4.60/0.94    inference(avatar_split_clause,[],[f254,f244,f85,f1298])).
% 4.60/0.94  fof(f85,plain,(
% 4.60/0.94    spl3_11 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 4.60/0.94  fof(f254,plain,(
% 4.60/0.94    ( ! [X21,X22,X20] : (k2_enumset1(X20,X22,X20,X21) = k1_enumset1(X20,X22,X21)) ) | (~spl3_11 | ~spl3_22)),
% 4.60/0.94    inference(superposition,[],[f245,f86])).
% 4.60/0.94  fof(f86,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) ) | ~spl3_11),
% 4.60/0.94    inference(avatar_component_clause,[],[f85])).
% 4.60/0.94  fof(f1242,plain,(
% 4.60/0.94    spl3_44 | ~spl3_10 | ~spl3_21),
% 4.60/0.94    inference(avatar_split_clause,[],[f229,f220,f81,f1240])).
% 4.60/0.94  fof(f81,plain,(
% 4.60/0.94    spl3_10 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 4.60/0.94  fof(f220,plain,(
% 4.60/0.94    spl3_21 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 4.60/0.94  fof(f229,plain,(
% 4.60/0.94    ( ! [X19,X17,X18] : (k2_enumset1(X17,X17,X19,X18) = k1_enumset1(X17,X18,X19)) ) | (~spl3_10 | ~spl3_21)),
% 4.60/0.94    inference(superposition,[],[f221,f82])).
% 4.60/0.94  fof(f82,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) ) | ~spl3_10),
% 4.60/0.94    inference(avatar_component_clause,[],[f81])).
% 4.60/0.94  fof(f221,plain,(
% 4.60/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)) ) | ~spl3_21),
% 4.60/0.94    inference(avatar_component_clause,[],[f220])).
% 4.60/0.94  fof(f1048,plain,(
% 4.60/0.94    spl3_39 | ~spl3_37 | ~spl3_38),
% 4.60/0.94    inference(avatar_split_clause,[],[f1044,f1041,f1033,f1046])).
% 4.60/0.94  fof(f1033,plain,(
% 4.60/0.94    spl3_37 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 4.60/0.94  fof(f1041,plain,(
% 4.60/0.94    spl3_38 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 4.60/0.94  fof(f1044,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ) | (~spl3_37 | ~spl3_38)),
% 4.60/0.94    inference(forward_demodulation,[],[f1042,f1034])).
% 4.60/0.94  fof(f1034,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) ) | ~spl3_37),
% 4.60/0.94    inference(avatar_component_clause,[],[f1033])).
% 4.60/0.94  fof(f1042,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ) | ~spl3_38),
% 4.60/0.94    inference(avatar_component_clause,[],[f1041])).
% 4.60/0.94  fof(f1043,plain,(
% 4.60/0.94    spl3_38 | ~spl3_15 | ~spl3_18),
% 4.60/0.94    inference(avatar_split_clause,[],[f192,f185,f169,f1041])).
% 4.60/0.94  fof(f185,plain,(
% 4.60/0.94    spl3_18 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 4.60/0.94  fof(f192,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ) | (~spl3_15 | ~spl3_18)),
% 4.60/0.94    inference(superposition,[],[f186,f170])).
% 4.60/0.94  fof(f186,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ) | ~spl3_18),
% 4.60/0.94    inference(avatar_component_clause,[],[f185])).
% 4.60/0.94  fof(f1035,plain,(
% 4.60/0.94    spl3_37 | ~spl3_16 | ~spl3_17 | ~spl3_19),
% 4.60/0.94    inference(avatar_split_clause,[],[f200,f189,f179,f175,f1033])).
% 4.60/0.94  fof(f179,plain,(
% 4.60/0.94    spl3_17 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 4.60/0.94  fof(f189,plain,(
% 4.60/0.94    spl3_19 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 4.60/0.94  fof(f200,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) ) | (~spl3_16 | ~spl3_17 | ~spl3_19)),
% 4.60/0.94    inference(forward_demodulation,[],[f199,f180])).
% 4.60/0.94  fof(f180,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) ) | ~spl3_17),
% 4.60/0.94    inference(avatar_component_clause,[],[f179])).
% 4.60/0.94  fof(f199,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) ) | (~spl3_16 | ~spl3_19)),
% 4.60/0.94    inference(superposition,[],[f190,f176])).
% 4.60/0.94  fof(f190,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) ) | ~spl3_19),
% 4.60/0.94    inference(avatar_component_clause,[],[f189])).
% 4.60/0.94  fof(f1025,plain,(
% 4.60/0.94    spl3_35 | ~spl3_15 | ~spl3_16 | ~spl3_17),
% 4.60/0.94    inference(avatar_split_clause,[],[f183,f179,f175,f169,f1023])).
% 4.60/0.94  fof(f183,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) ) | (~spl3_15 | ~spl3_16 | ~spl3_17)),
% 4.60/0.94    inference(forward_demodulation,[],[f182,f176])).
% 4.60/0.94  fof(f182,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) ) | (~spl3_15 | ~spl3_17)),
% 4.60/0.94    inference(superposition,[],[f180,f170])).
% 4.60/0.94  fof(f327,plain,(
% 4.60/0.94    spl3_26 | ~spl3_8 | ~spl3_9),
% 4.60/0.94    inference(avatar_split_clause,[],[f102,f77,f73,f325])).
% 4.60/0.94  fof(f73,plain,(
% 4.60/0.94    spl3_8 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 4.60/0.94  fof(f77,plain,(
% 4.60/0.94    spl3_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 4.60/0.94  fof(f102,plain,(
% 4.60/0.94    ( ! [X14,X12,X13,X11] : (k2_enumset1(X14,X13,X12,X11) = k2_enumset1(X11,X13,X14,X12)) ) | (~spl3_8 | ~spl3_9)),
% 4.60/0.94    inference(superposition,[],[f78,f74])).
% 4.60/0.94  fof(f74,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) ) | ~spl3_8),
% 4.60/0.94    inference(avatar_component_clause,[],[f73])).
% 4.60/0.94  fof(f78,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) ) | ~spl3_9),
% 4.60/0.94    inference(avatar_component_clause,[],[f77])).
% 4.60/0.94  fof(f246,plain,(
% 4.60/0.94    spl3_22 | ~spl3_7 | ~spl3_9),
% 4.60/0.94    inference(avatar_split_clause,[],[f104,f77,f67,f244])).
% 4.60/0.94  fof(f67,plain,(
% 4.60/0.94    spl3_7 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.60/0.94    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 4.60/0.94  fof(f104,plain,(
% 4.60/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) ) | (~spl3_7 | ~spl3_9)),
% 4.60/0.94    inference(superposition,[],[f78,f68])).
% 4.60/0.94  fof(f68,plain,(
% 4.60/0.94    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl3_7),
% 4.60/0.94    inference(avatar_component_clause,[],[f67])).
% 4.60/0.94  fof(f222,plain,(
% 4.60/0.94    spl3_21 | ~spl3_7 | ~spl3_9),
% 4.60/0.94    inference(avatar_split_clause,[],[f100,f77,f67,f220])).
% 4.60/0.94  fof(f100,plain,(
% 4.60/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)) ) | (~spl3_7 | ~spl3_9)),
% 4.60/0.94    inference(superposition,[],[f78,f68])).
% 4.60/0.94  fof(f191,plain,(
% 4.60/0.94    spl3_19),
% 4.60/0.94    inference(avatar_split_clause,[],[f40,f189])).
% 4.60/0.94  fof(f40,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 4.60/0.94    inference(cnf_transformation,[],[f9])).
% 4.60/0.94  fof(f9,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
% 4.60/0.94  fof(f187,plain,(
% 4.60/0.94    spl3_18),
% 4.60/0.94    inference(avatar_split_clause,[],[f39,f185])).
% 4.60/0.94  fof(f39,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 4.60/0.94    inference(cnf_transformation,[],[f8])).
% 4.60/0.94  fof(f8,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 4.60/0.94  fof(f181,plain,(
% 4.60/0.94    spl3_17),
% 4.60/0.94    inference(avatar_split_clause,[],[f38,f179])).
% 4.60/0.94  fof(f38,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 4.60/0.94    inference(cnf_transformation,[],[f10])).
% 4.60/0.94  fof(f10,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 4.60/0.94  fof(f177,plain,(
% 4.60/0.94    spl3_16),
% 4.60/0.94    inference(avatar_split_clause,[],[f37,f175])).
% 4.60/0.94  fof(f37,plain,(
% 4.60/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f17])).
% 4.60/0.94  fof(f17,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 4.60/0.94  fof(f171,plain,(
% 4.60/0.94    spl3_15),
% 4.60/0.94    inference(avatar_split_clause,[],[f36,f169])).
% 4.60/0.94  fof(f36,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f16])).
% 4.60/0.94  fof(f16,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 4.60/0.94  fof(f167,plain,(
% 4.60/0.94    spl3_14),
% 4.60/0.94    inference(avatar_split_clause,[],[f35,f165])).
% 4.60/0.94  fof(f35,plain,(
% 4.60/0.94    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f15])).
% 4.60/0.94  fof(f15,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 4.60/0.94  fof(f91,plain,(
% 4.60/0.94    spl3_12),
% 4.60/0.94    inference(avatar_split_clause,[],[f34,f89])).
% 4.60/0.94  fof(f34,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f14])).
% 4.60/0.94  fof(f14,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 4.60/0.94  fof(f87,plain,(
% 4.60/0.94    spl3_11),
% 4.60/0.94    inference(avatar_split_clause,[],[f33,f85])).
% 4.60/0.94  fof(f33,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f5])).
% 4.60/0.94  fof(f5,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 4.60/0.94  fof(f83,plain,(
% 4.60/0.94    spl3_10),
% 4.60/0.94    inference(avatar_split_clause,[],[f32,f81])).
% 4.60/0.94  fof(f32,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f6])).
% 4.60/0.94  fof(f6,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 4.60/0.94  fof(f79,plain,(
% 4.60/0.94    spl3_9),
% 4.60/0.94    inference(avatar_split_clause,[],[f31,f77])).
% 4.60/0.94  fof(f31,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f4])).
% 4.60/0.94  fof(f4,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 4.60/0.94  fof(f75,plain,(
% 4.60/0.94    spl3_8),
% 4.60/0.94    inference(avatar_split_clause,[],[f30,f73])).
% 4.60/0.94  fof(f30,plain,(
% 4.60/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f7])).
% 4.60/0.94  fof(f7,axiom,(
% 4.60/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 4.60/0.94  fof(f69,plain,(
% 4.60/0.94    spl3_7),
% 4.60/0.94    inference(avatar_split_clause,[],[f29,f67])).
% 4.60/0.94  fof(f29,plain,(
% 4.60/0.94    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f13])).
% 4.60/0.94  fof(f13,axiom,(
% 4.60/0.94    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.60/0.94  fof(f57,plain,(
% 4.60/0.94    spl3_4),
% 4.60/0.94    inference(avatar_split_clause,[],[f26,f55])).
% 4.60/0.94  fof(f26,plain,(
% 4.60/0.94    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.60/0.94    inference(cnf_transformation,[],[f12])).
% 4.60/0.94  fof(f12,axiom,(
% 4.60/0.94    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.60/0.94  fof(f45,plain,(
% 4.60/0.94    ~spl3_1),
% 4.60/0.94    inference(avatar_split_clause,[],[f23,f42])).
% 4.60/0.94  fof(f23,plain,(
% 4.60/0.94    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 4.60/0.94    inference(cnf_transformation,[],[f22])).
% 4.60/0.94  fof(f22,plain,(
% 4.60/0.94    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 4.60/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 4.60/0.94  fof(f21,plain,(
% 4.60/0.94    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 4.60/0.94    introduced(choice_axiom,[])).
% 4.60/0.94  fof(f20,plain,(
% 4.60/0.94    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 4.60/0.94    inference(ennf_transformation,[],[f19])).
% 4.60/0.94  fof(f19,negated_conjecture,(
% 4.60/0.94    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 4.60/0.94    inference(negated_conjecture,[],[f18])).
% 4.60/0.94  fof(f18,conjecture,(
% 4.60/0.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 4.60/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 4.60/0.94  % SZS output end Proof for theBenchmark
% 4.60/0.94  % (26206)------------------------------
% 4.60/0.94  % (26206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/0.94  % (26206)Termination reason: Refutation
% 4.60/0.94  
% 4.60/0.94  % (26206)Memory used [KB]: 11257
% 4.60/0.94  % (26206)Time elapsed: 0.489 s
% 4.60/0.94  % (26206)------------------------------
% 4.60/0.94  % (26206)------------------------------
% 4.60/0.96  % (26199)Success in time 0.598 s
%------------------------------------------------------------------------------
