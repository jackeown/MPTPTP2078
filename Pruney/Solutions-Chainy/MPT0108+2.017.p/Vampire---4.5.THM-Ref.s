%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:20 EST 2020

% Result     : Theorem 30.43s
% Output     : Refutation 30.43s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 461 expanded)
%              Number of leaves         :   53 ( 230 expanded)
%              Depth                    :   11
%              Number of atoms          :  571 (1050 expanded)
%              Number of equality atoms :  200 ( 457 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31981,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f67,f74,f78,f91,f102,f114,f118,f122,f127,f167,f179,f183,f220,f284,f306,f312,f322,f467,f523,f783,f823,f895,f934,f1354,f2314,f3847,f4192,f4826,f6959,f8438,f9243,f9450,f12568,f28320,f31838,f31962])).

fof(f31962,plain,
    ( ~ spl2_2
    | ~ spl2_9
    | ~ spl2_21
    | ~ spl2_47
    | spl2_239 ),
    inference(avatar_contradiction_clause,[],[f31961])).

fof(f31961,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_21
    | ~ spl2_47
    | spl2_239 ),
    inference(subsumption_resolution,[],[f31960,f311])).

fof(f311,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl2_21
  <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f31960,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_47
    | spl2_239 ),
    inference(forward_demodulation,[],[f31959,f1353])).

fof(f1353,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f1352,plain,
    ( spl2_47
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f31959,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))))
    | ~ spl2_2
    | ~ spl2_9
    | spl2_239 ),
    inference(forward_demodulation,[],[f31958,f101])).

fof(f101,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f31958,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl2_2
    | ~ spl2_9
    | spl2_239 ),
    inference(forward_demodulation,[],[f31877,f51])).

fof(f51,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_2
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31877,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)))
    | ~ spl2_9
    | spl2_239 ),
    inference(superposition,[],[f31837,f101])).

fof(f31837,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,sK1))
    | spl2_239 ),
    inference(avatar_component_clause,[],[f31836])).

fof(f31836,plain,
    ( spl2_239
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_239])])).

fof(f31838,plain,
    ( ~ spl2_239
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_39
    | ~ spl2_47
    | ~ spl2_96
    | ~ spl2_183 ),
    inference(avatar_split_clause,[],[f28458,f28318,f6957,f1352,f932,f781,f100,f89,f50,f46,f31836])).

fof(f46,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f89,plain,
    ( spl2_8
  <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f781,plain,
    ( spl2_30
  <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f932,plain,
    ( spl2_39
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f6957,plain,
    ( spl2_96
  <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f28318,plain,
    ( spl2_183
  <=> ! [X73,X72] :
        ( X72 = X73
        | k1_xboole_0 != k5_xboole_0(X72,X73) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_183])])).

fof(f28458,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_39
    | ~ spl2_47
    | ~ spl2_96
    | ~ spl2_183 ),
    inference(forward_demodulation,[],[f28457,f51])).

fof(f28457,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_39
    | ~ spl2_47
    | ~ spl2_96
    | ~ spl2_183 ),
    inference(forward_demodulation,[],[f28456,f813])).

fof(f813,plain,
    ( ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6)))
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f802,f101])).

fof(f802,plain,
    ( ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6))
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(superposition,[],[f101,f782])).

fof(f782,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f781])).

fof(f28456,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_39
    | ~ spl2_47
    | ~ spl2_96
    | ~ spl2_183 ),
    inference(forward_demodulation,[],[f28455,f933])).

fof(f933,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f932])).

fof(f28455,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_47
    | ~ spl2_96
    | ~ spl2_183 ),
    inference(forward_demodulation,[],[f28364,f8390])).

fof(f8390,plain,
    ( ! [X78,X76,X77] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(X76,k5_xboole_0(k4_xboole_0(X78,X76),k4_xboole_0(X76,X77)))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_47
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f8389,f101])).

fof(f8389,plain,
    ( ! [X78,X76,X77] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_47
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f8388,f90])).

fof(f90,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f8388,plain,
    ( ! [X78,X76,X77] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k5_xboole_0(k1_xboole_0,k4_xboole_0(X76,X77)))
    | ~ spl2_2
    | ~ spl2_47
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f8272,f51])).

fof(f8272,plain,
    ( ! [X78,X76,X77] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k5_xboole_0(k4_xboole_0(X76,X77),k1_xboole_0))
    | ~ spl2_47
    | ~ spl2_96 ),
    inference(superposition,[],[f1353,f6958])).

fof(f6958,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4)))
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f6957])).

fof(f28364,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | spl2_1
    | ~ spl2_183 ),
    inference(unit_resulting_resolution,[],[f47,f28319])).

fof(f28319,plain,
    ( ! [X72,X73] :
        ( k1_xboole_0 != k5_xboole_0(X72,X73)
        | X72 = X73 )
    | ~ spl2_183 ),
    inference(avatar_component_clause,[],[f28318])).

fof(f47,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f28320,plain,
    ( spl2_183
    | ~ spl2_32
    | ~ spl2_129 ),
    inference(avatar_split_clause,[],[f13032,f12566,f821,f28318])).

fof(f821,plain,
    ( spl2_32
  <=> ! [X9,X10] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f12566,plain,
    ( spl2_129
  <=> ! [X3,X4] :
        ( k5_xboole_0(X3,X4) = X4
        | k1_xboole_0 != X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).

fof(f13032,plain,
    ( ! [X72,X73] :
        ( X72 = X73
        | k1_xboole_0 != k5_xboole_0(X72,X73) )
    | ~ spl2_32
    | ~ spl2_129 ),
    inference(superposition,[],[f12567,f822])).

fof(f822,plain,
    ( ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f821])).

fof(f12567,plain,
    ( ! [X4,X3] :
        ( k5_xboole_0(X3,X4) = X4
        | k1_xboole_0 != X3 )
    | ~ spl2_129 ),
    inference(avatar_component_clause,[],[f12566])).

fof(f12568,plain,
    ( spl2_129
    | ~ spl2_9
    | ~ spl2_29
    | ~ spl2_104 ),
    inference(avatar_split_clause,[],[f9631,f9448,f521,f100,f12566])).

fof(f521,plain,
    ( spl2_29
  <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f9448,plain,
    ( spl2_104
  <=> ! [X1] :
        ( k5_xboole_0(X1,X1) = X1
        | k1_xboole_0 != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f9631,plain,
    ( ! [X4,X3] :
        ( k5_xboole_0(X3,X4) = X4
        | k1_xboole_0 != X3 )
    | ~ spl2_9
    | ~ spl2_29
    | ~ spl2_104 ),
    inference(forward_demodulation,[],[f9529,f522])).

fof(f522,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f521])).

fof(f9529,plain,
    ( ! [X4,X3] :
        ( k5_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X3,X4))
        | k1_xboole_0 != X3 )
    | ~ spl2_9
    | ~ spl2_104 ),
    inference(superposition,[],[f101,f9449])).

fof(f9449,plain,
    ( ! [X1] :
        ( k5_xboole_0(X1,X1) = X1
        | k1_xboole_0 != X1 )
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f9448])).

fof(f9450,plain,
    ( spl2_104
    | ~ spl2_3
    | ~ spl2_102 ),
    inference(avatar_split_clause,[],[f9285,f9241,f54,f9448])).

fof(f54,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f9241,plain,
    ( spl2_102
  <=> ! [X34] :
        ( k4_xboole_0(X34,X34) = X34
        | k1_xboole_0 != X34 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).

fof(f9285,plain,
    ( ! [X1] :
        ( k5_xboole_0(X1,X1) = X1
        | k1_xboole_0 != X1 )
    | ~ spl2_3
    | ~ spl2_102 ),
    inference(superposition,[],[f55,f9242])).

fof(f9242,plain,
    ( ! [X34] :
        ( k4_xboole_0(X34,X34) = X34
        | k1_xboole_0 != X34 )
    | ~ spl2_102 ),
    inference(avatar_component_clause,[],[f9241])).

fof(f55,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f9243,plain,
    ( spl2_102
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_39
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(avatar_split_clause,[],[f9227,f8436,f2312,f932,f112,f54,f9241])).

fof(f112,plain,
    ( spl2_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f2312,plain,
    ( spl2_59
  <=> ! [X7,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f8436,plain,
    ( spl2_101
  <=> ! [X9,X7,X8] :
        ( k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) != k4_xboole_0(X9,k5_xboole_0(X7,k4_xboole_0(X7,X8)))
        | k5_xboole_0(X7,k4_xboole_0(X7,X8)) = X9 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f9227,plain,
    ( ! [X34] :
        ( k4_xboole_0(X34,X34) = X34
        | k1_xboole_0 != X34 )
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_39
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(forward_demodulation,[],[f9226,f55])).

fof(f9226,plain,
    ( ! [X34] :
        ( k1_xboole_0 != X34
        | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34)) )
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_39
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(forward_demodulation,[],[f9225,f55])).

fof(f9225,plain,
    ( ! [X34] :
        ( k1_xboole_0 != k5_xboole_0(X34,k4_xboole_0(X34,X34))
        | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34)) )
    | ~ spl2_11
    | ~ spl2_39
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(forward_demodulation,[],[f9224,f113])).

fof(f113,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f9224,plain,
    ( ! [X34] :
        ( k1_xboole_0 != k5_xboole_0(X34,k5_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,X34))))
        | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34)) )
    | ~ spl2_39
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(forward_demodulation,[],[f9043,f933])).

fof(f9043,plain,
    ( ! [X34] :
        ( k1_xboole_0 != k5_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,X34))))
        | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34)) )
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(superposition,[],[f8437,f2313])).

fof(f2313,plain,
    ( ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,k4_xboole_0(X7,X6)))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f2312])).

fof(f8437,plain,
    ( ! [X8,X7,X9] :
        ( k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) != k4_xboole_0(X9,k5_xboole_0(X7,k4_xboole_0(X7,X8)))
        | k5_xboole_0(X7,k4_xboole_0(X7,X8)) = X9 )
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f8436])).

fof(f8438,plain,
    ( spl2_101
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f382,f320,f72,f8436])).

fof(f72,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( X0 = X1
        | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f320,plain,
    ( spl2_22
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f382,plain,
    ( ! [X8,X7,X9] :
        ( k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) != k4_xboole_0(X9,k5_xboole_0(X7,k4_xboole_0(X7,X8)))
        | k5_xboole_0(X7,k4_xboole_0(X7,X8)) = X9 )
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(superposition,[],[f73,f321])).

fof(f321,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f320])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
        | X0 = X1 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f6959,plain,
    ( spl2_96
    | ~ spl2_21
    | ~ spl2_77
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f5123,f4824,f4190,f310,f6957])).

fof(f4190,plain,
    ( spl2_77
  <=> ! [X5,X7,X6] : k4_xboole_0(k4_xboole_0(X5,X6),X7) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f4824,plain,
    ( spl2_87
  <=> ! [X51,X50,X52] : k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = X50 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f5123,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4)))
    | ~ spl2_21
    | ~ spl2_77
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f5051,f311])).

fof(f5051,plain,
    ( ! [X6,X4,X5] : k5_xboole_0(X4,X4) = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4)))
    | ~ spl2_77
    | ~ spl2_87 ),
    inference(superposition,[],[f4191,f4825])).

fof(f4825,plain,
    ( ! [X52,X50,X51] : k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = X50
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f4824])).

fof(f4191,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X5,X6),X7) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7)))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f4190])).

fof(f4826,plain,
    ( spl2_87
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_24
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f4759,f3845,f465,f76,f58,f4824])).

fof(f58,plain,
    ( spl2_4
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f76,plain,
    ( spl2_7
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f465,plain,
    ( spl2_24
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f3845,plain,
    ( spl2_76
  <=> ! [X3,X2,X4] : k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f4759,plain,
    ( ! [X52,X50,X51] : k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = X50
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_24
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f4758,f77])).

fof(f77,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f4758,plain,
    ( ! [X52,X50,X51] : k5_xboole_0(X50,k1_xboole_0) = k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50))))
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f4641,f59])).

fof(f59,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f4641,plain,
    ( ! [X52,X50,X51] : k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = k5_xboole_0(X50,k4_xboole_0(X50,k5_xboole_0(X50,k4_xboole_0(X51,X50))))
    | ~ spl2_24
    | ~ spl2_76 ),
    inference(superposition,[],[f3846,f466])).

fof(f466,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f465])).

fof(f3846,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4)
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f3845])).

fof(f4192,plain,
    ( spl2_77
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f405,f320,f116,f112,f4190])).

fof(f116,plain,
    ( spl2_12
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f405,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X5,X6),X7) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7)))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f358,f158])).

fof(f158,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(superposition,[],[f113,f117])).

fof(f117,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f358,plain,
    ( ! [X6,X7,X5] : k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))),X7)
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(superposition,[],[f321,f117])).

fof(f3847,plain,
    ( spl2_76
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f404,f320,f76,f58,f3845])).

fof(f404,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4)
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f357,f77])).

fof(f357,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(k5_xboole_0(X2,k1_xboole_0),X4)
    | ~ spl2_4
    | ~ spl2_22 ),
    inference(superposition,[],[f321,f59])).

fof(f2314,plain,
    ( spl2_59
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f492,f465,f58,f50,f2312])).

fof(f492,plain,
    ( ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,k4_xboole_0(X7,X6)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f482,f51])).

fof(f482,plain,
    ( ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(k4_xboole_0(X7,X6),X6))
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(superposition,[],[f59,f466])).

fof(f1354,plain,
    ( spl2_47
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f896,f893,f125,f112,f1352])).

fof(f125,plain,
    ( spl2_14
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f893,plain,
    ( spl2_35
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f896,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f894,f211])).

fof(f211,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(superposition,[],[f113,f126])).

fof(f126,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f894,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f893])).

fof(f934,plain,
    ( spl2_39
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f211,f125,f112,f932])).

fof(f895,plain,
    ( spl2_35
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f158,f116,f112,f893])).

fof(f823,plain,
    ( spl2_32
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f789,f781,f821])).

fof(f789,plain,
    ( ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9
    | ~ spl2_30 ),
    inference(superposition,[],[f782,f782])).

fof(f783,plain,
    ( spl2_30
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f525,f521,f50,f781])).

fof(f525,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(superposition,[],[f522,f51])).

fof(f523,plain,
    ( spl2_29
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f286,f282,f181,f521])).

fof(f181,plain,
    ( spl2_17
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f282,plain,
    ( spl2_19
  <=> ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f286,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(superposition,[],[f182,f283])).

fof(f283,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f282])).

fof(f182,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = X1
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f181])).

fof(f467,plain,
    ( spl2_24
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f243,f177,f112,f465])).

fof(f177,plain,
    ( spl2_16
  <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f243,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(superposition,[],[f178,f113])).

fof(f178,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f322,plain,
    ( spl2_22
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f308,f304,f125,f112,f320])).

fof(f304,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f308,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f307,f211])).

fof(f307,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f305,f211])).

fof(f305,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f304])).

fof(f312,plain,
    ( spl2_21
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f287,f282,f165,f310])).

fof(f165,plain,
    ( spl2_15
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f287,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(superposition,[],[f166,f283])).

fof(f166,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f306,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f42,f304])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f33,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f284,plain,
    ( spl2_19
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f230,f218,f112,f76,f282])).

fof(f218,plain,
    ( spl2_18
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f230,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f226,f77])).

fof(f226,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(superposition,[],[f113,f219])).

fof(f219,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( spl2_18
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f203,f125,f58,f218])).

fof(f203,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f126,f59])).

fof(f183,plain,
    ( spl2_17
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f175,f165,f100,f89,f181])).

fof(f175,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = X1
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f172,f90])).

fof(f172,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(superposition,[],[f101,f166])).

fof(f179,plain,
    ( spl2_16
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f123,f120,f177])).

fof(f120,plain,
    ( spl2_13
  <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f123,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f121,f42])).

fof(f121,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f167,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f148,f112,f58,f165])).

fof(f148,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(superposition,[],[f113,f59])).

fof(f127,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f41,f125])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f122,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f39,f120])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f27,f30])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f118,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f38,f116])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f30,f30])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f114,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f35,f112])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f102,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f32,f100])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f91,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f79,f76,f50,f89])).

fof(f79,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(superposition,[],[f77,f51])).

fof(f78,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f68,f65,f54,f76])).

fof(f65,plain,
    ( spl2_5
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f68,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f55,f66])).

fof(f66,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f74,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f67,plain,
    ( spl2_5
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f62,f58,f54,f65])).

fof(f62,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f59,f55])).

fof(f60,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f40,f58])).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f56,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f37,f54])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f52,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f48,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f36,f46])).

fof(f36,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f27,f30])).

fof(f21,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (8765)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (8789)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (8774)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (8763)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (8791)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (8769)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (8764)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (8781)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (8773)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (8761)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (8770)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (8766)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (8762)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8762)Refutation not found, incomplete strategy% (8762)------------------------------
% 0.21/0.53  % (8762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8762)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8762)Memory used [KB]: 10618
% 0.21/0.53  % (8762)Time elapsed: 0.129 s
% 0.21/0.53  % (8762)------------------------------
% 0.21/0.53  % (8762)------------------------------
% 0.21/0.54  % (8787)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (8780)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (8790)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (8760)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (8760)Refutation not found, incomplete strategy% (8760)------------------------------
% 0.21/0.54  % (8760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8760)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8760)Memory used [KB]: 1663
% 0.21/0.54  % (8760)Time elapsed: 0.138 s
% 0.21/0.54  % (8760)------------------------------
% 0.21/0.54  % (8760)------------------------------
% 0.21/0.54  % (8783)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (8783)Refutation not found, incomplete strategy% (8783)------------------------------
% 0.21/0.54  % (8783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8783)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8783)Memory used [KB]: 1663
% 0.21/0.54  % (8783)Time elapsed: 0.140 s
% 0.21/0.54  % (8783)------------------------------
% 0.21/0.54  % (8783)------------------------------
% 0.21/0.55  % (8781)Refutation not found, incomplete strategy% (8781)------------------------------
% 0.21/0.55  % (8781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8781)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8781)Memory used [KB]: 10618
% 0.21/0.55  % (8781)Time elapsed: 0.144 s
% 0.21/0.55  % (8781)------------------------------
% 0.21/0.55  % (8781)------------------------------
% 0.21/0.55  % (8772)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (8778)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.55  % (8779)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (8786)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.55  % (8784)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.55  % (8784)Refutation not found, incomplete strategy% (8784)------------------------------
% 1.47/0.55  % (8784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (8784)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (8784)Memory used [KB]: 10618
% 1.47/0.55  % (8784)Time elapsed: 0.150 s
% 1.47/0.55  % (8784)------------------------------
% 1.47/0.55  % (8784)------------------------------
% 1.47/0.55  % (8767)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.55  % (8778)Refutation not found, incomplete strategy% (8778)------------------------------
% 1.47/0.55  % (8778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (8777)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.55  % (8778)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (8778)Memory used [KB]: 10618
% 1.47/0.55  % (8778)Time elapsed: 0.151 s
% 1.47/0.55  % (8778)------------------------------
% 1.47/0.55  % (8778)------------------------------
% 1.47/0.55  % (8771)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.56  % (8776)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.56  % (8788)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.56  % (8785)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.56  % (8785)Refutation not found, incomplete strategy% (8785)------------------------------
% 1.47/0.56  % (8785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (8785)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (8785)Memory used [KB]: 1663
% 1.47/0.56  % (8785)Time elapsed: 0.160 s
% 1.47/0.56  % (8785)------------------------------
% 1.47/0.56  % (8785)------------------------------
% 1.47/0.56  % (8768)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.57  % (8768)Refutation not found, incomplete strategy% (8768)------------------------------
% 1.65/0.57  % (8768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (8768)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (8768)Memory used [KB]: 10618
% 1.65/0.58  % (8768)Time elapsed: 0.163 s
% 1.65/0.58  % (8768)------------------------------
% 1.65/0.58  % (8768)------------------------------
% 1.99/0.65  % (8825)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.99/0.65  % (8825)Refutation not found, incomplete strategy% (8825)------------------------------
% 1.99/0.65  % (8825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.65  % (8825)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.65  
% 1.99/0.65  % (8825)Memory used [KB]: 6140
% 1.99/0.65  % (8825)Time elapsed: 0.065 s
% 1.99/0.65  % (8825)------------------------------
% 1.99/0.65  % (8825)------------------------------
% 2.22/0.67  % (8830)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.22/0.68  % (8826)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.22/0.68  % (8827)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.22/0.69  % (8828)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.22/0.71  % (8831)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.22/0.72  % (8829)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.22/0.72  % (8832)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.87/0.77  % (8838)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.87/0.82  % (8765)Time limit reached!
% 2.87/0.82  % (8765)------------------------------
% 2.87/0.82  % (8765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.87/0.82  % (8765)Termination reason: Time limit
% 2.87/0.82  % (8765)Termination phase: Saturation
% 2.87/0.82  
% 2.87/0.82  % (8765)Memory used [KB]: 10106
% 2.87/0.82  % (8765)Time elapsed: 0.400 s
% 2.87/0.82  % (8765)------------------------------
% 2.87/0.82  % (8765)------------------------------
% 3.38/0.92  % (8772)Time limit reached!
% 3.38/0.92  % (8772)------------------------------
% 3.38/0.92  % (8772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.38/0.92  % (8772)Termination reason: Time limit
% 3.38/0.92  % (8772)Termination phase: Saturation
% 3.38/0.92  
% 3.38/0.92  % (8772)Memory used [KB]: 10490
% 3.38/0.92  % (8772)Time elapsed: 0.500 s
% 3.38/0.92  % (8772)------------------------------
% 3.38/0.92  % (8772)------------------------------
% 3.77/0.93  % (8846)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.77/0.93  % (8761)Time limit reached!
% 3.77/0.93  % (8761)------------------------------
% 3.77/0.93  % (8761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.93  % (8761)Termination reason: Time limit
% 3.77/0.93  
% 3.77/0.93  % (8761)Memory used [KB]: 9083
% 3.77/0.93  % (8761)Time elapsed: 0.526 s
% 3.77/0.93  % (8761)------------------------------
% 3.77/0.93  % (8761)------------------------------
% 3.97/0.99  % (8828)Time limit reached!
% 3.97/0.99  % (8828)------------------------------
% 3.97/0.99  % (8828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.00  % (8828)Termination reason: Time limit
% 3.97/1.00  
% 3.97/1.00  % (8828)Memory used [KB]: 7931
% 3.97/1.00  % (8828)Time elapsed: 0.417 s
% 3.97/1.00  % (8828)------------------------------
% 3.97/1.00  % (8828)------------------------------
% 3.97/1.01  % (8829)Time limit reached!
% 3.97/1.01  % (8829)------------------------------
% 3.97/1.01  % (8829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.01  % (8829)Termination reason: Time limit
% 3.97/1.01  % (8829)Termination phase: Saturation
% 3.97/1.01  
% 3.97/1.01  % (8829)Memory used [KB]: 15223
% 3.97/1.01  % (8829)Time elapsed: 0.400 s
% 3.97/1.01  % (8829)------------------------------
% 3.97/1.01  % (8829)------------------------------
% 3.97/1.02  % (8790)Time limit reached!
% 3.97/1.02  % (8790)------------------------------
% 3.97/1.02  % (8790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.02  % (8790)Termination reason: Time limit
% 3.97/1.02  % (8790)Termination phase: Saturation
% 3.97/1.02  
% 3.97/1.02  % (8790)Memory used [KB]: 10874
% 3.97/1.02  % (8790)Time elapsed: 0.600 s
% 3.97/1.02  % (8790)------------------------------
% 3.97/1.02  % (8790)------------------------------
% 3.97/1.03  % (8777)Time limit reached!
% 3.97/1.03  % (8777)------------------------------
% 3.97/1.03  % (8777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.03  % (8777)Termination reason: Time limit
% 3.97/1.03  % (8777)Termination phase: Saturation
% 3.97/1.03  
% 3.97/1.03  % (8777)Memory used [KB]: 16502
% 3.97/1.03  % (8777)Time elapsed: 0.600 s
% 3.97/1.03  % (8777)------------------------------
% 3.97/1.03  % (8777)------------------------------
% 4.55/1.04  % (8883)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.55/1.04  % (8883)Refutation not found, incomplete strategy% (8883)------------------------------
% 4.55/1.04  % (8883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.04  % (8883)Termination reason: Refutation not found, incomplete strategy
% 4.55/1.04  
% 4.55/1.04  % (8883)Memory used [KB]: 6140
% 4.55/1.04  % (8883)Time elapsed: 0.101 s
% 4.55/1.04  % (8883)------------------------------
% 4.55/1.04  % (8883)------------------------------
% 4.55/1.06  % (8767)Time limit reached!
% 4.55/1.06  % (8767)------------------------------
% 4.55/1.06  % (8767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.06  % (8767)Termination reason: Time limit
% 4.55/1.06  
% 4.55/1.06  % (8767)Memory used [KB]: 12025
% 4.55/1.06  % (8767)Time elapsed: 0.625 s
% 4.55/1.06  % (8767)------------------------------
% 4.55/1.06  % (8767)------------------------------
% 4.55/1.07  % (8888)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.55/1.07  % (8888)Refutation not found, incomplete strategy% (8888)------------------------------
% 4.55/1.07  % (8888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.07  % (8888)Termination reason: Refutation not found, incomplete strategy
% 4.55/1.07  
% 4.55/1.07  % (8888)Memory used [KB]: 1663
% 4.55/1.07  % (8888)Time elapsed: 0.105 s
% 4.55/1.07  % (8888)------------------------------
% 4.55/1.07  % (8888)------------------------------
% 5.61/1.12  % (8770)Time limit reached!
% 5.61/1.12  % (8770)------------------------------
% 5.61/1.12  % (8770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.12  % (8770)Termination reason: Time limit
% 5.61/1.12  
% 5.61/1.12  % (8770)Memory used [KB]: 65244
% 5.61/1.12  % (8770)Time elapsed: 0.668 s
% 5.61/1.12  % (8770)------------------------------
% 5.61/1.12  % (8770)------------------------------
% 5.61/1.12  % (8926)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.61/1.14  % (8926)Refutation not found, incomplete strategy% (8926)------------------------------
% 5.61/1.14  % (8926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.14  % (8926)Termination reason: Refutation not found, incomplete strategy
% 5.61/1.14  
% 5.61/1.14  % (8926)Memory used [KB]: 1663
% 5.61/1.14  % (8926)Time elapsed: 0.062 s
% 5.61/1.14  % (8926)------------------------------
% 5.61/1.14  % (8926)------------------------------
% 5.61/1.14  % (8919)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.17/1.16  % (8930)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.17/1.16  % (8951)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.39/1.18  % (8959)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.39/1.19  % (8949)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.39/1.19  % (8949)Refutation not found, incomplete strategy% (8949)------------------------------
% 6.39/1.19  % (8949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.39/1.19  % (8949)Termination reason: Refutation not found, incomplete strategy
% 6.39/1.19  
% 6.39/1.19  % (8949)Memory used [KB]: 6140
% 6.39/1.19  % (8949)Time elapsed: 0.132 s
% 6.39/1.19  % (8949)------------------------------
% 6.39/1.19  % (8949)------------------------------
% 6.39/1.19  % (8970)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.39/1.23  % (8994)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.92/1.25  % (9002)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 6.92/1.31  % (9012)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.26/1.47  % (8951)Time limit reached!
% 8.26/1.47  % (8951)------------------------------
% 8.26/1.47  % (8951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.26/1.47  % (8951)Termination reason: Time limit
% 8.26/1.47  % (8951)Termination phase: Saturation
% 8.26/1.47  
% 8.26/1.47  % (8951)Memory used [KB]: 3965
% 8.26/1.47  % (8951)Time elapsed: 0.400 s
% 8.26/1.47  % (8951)------------------------------
% 8.26/1.47  % (8951)------------------------------
% 8.82/1.54  % (8994)Time limit reached!
% 8.82/1.54  % (8994)------------------------------
% 8.82/1.54  % (8994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.82/1.55  % (8919)Time limit reached!
% 8.82/1.55  % (8919)------------------------------
% 8.82/1.55  % (8919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.82/1.55  % (8919)Termination reason: Time limit
% 8.82/1.55  
% 8.82/1.55  % (8919)Memory used [KB]: 4477
% 8.82/1.55  % (8919)Time elapsed: 0.519 s
% 8.82/1.55  % (8919)------------------------------
% 8.82/1.55  % (8919)------------------------------
% 8.82/1.55  % (8994)Termination reason: Time limit
% 8.82/1.55  
% 8.82/1.55  % (8994)Memory used [KB]: 3837
% 8.82/1.55  % (8994)Time elapsed: 0.408 s
% 8.82/1.55  % (8994)------------------------------
% 8.82/1.55  % (8994)------------------------------
% 9.04/1.57  % (9086)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 10.38/1.69  % (9087)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.38/1.70  % (8786)Time limit reached!
% 10.38/1.70  % (8786)------------------------------
% 10.38/1.70  % (8786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.38/1.70  % (9088)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.38/1.71  % (8786)Termination reason: Time limit
% 10.38/1.72  
% 10.38/1.72  % (8786)Memory used [KB]: 22899
% 10.38/1.72  % (8786)Time elapsed: 1.303 s
% 10.38/1.72  % (8786)------------------------------
% 10.38/1.72  % (8786)------------------------------
% 11.19/1.80  % (8831)Time limit reached!
% 11.19/1.80  % (8831)------------------------------
% 11.19/1.80  % (8831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.51/1.82  % (8831)Termination reason: Time limit
% 11.51/1.82  
% 11.51/1.82  % (8831)Memory used [KB]: 15095
% 11.51/1.82  % (8831)Time elapsed: 1.213 s
% 11.51/1.82  % (8831)------------------------------
% 11.51/1.82  % (8831)------------------------------
% 11.66/1.85  % (9089)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.66/1.85  % (9089)Refutation not found, incomplete strategy% (9089)------------------------------
% 11.66/1.85  % (9089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/1.86  % (9089)Termination reason: Refutation not found, incomplete strategy
% 11.66/1.86  
% 11.66/1.86  % (9089)Memory used [KB]: 6140
% 11.66/1.86  % (9089)Time elapsed: 0.100 s
% 11.66/1.86  % (9089)------------------------------
% 11.66/1.86  % (9089)------------------------------
% 12.26/1.96  % (9090)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.71/1.99  % (9091)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 12.71/1.99  % (8789)Time limit reached!
% 12.71/1.99  % (8789)------------------------------
% 12.71/1.99  % (8789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.71/2.00  % (8789)Termination reason: Time limit
% 12.71/2.00  % (8789)Termination phase: Saturation
% 12.71/2.00  
% 12.71/2.00  % (8789)Memory used [KB]: 19573
% 12.71/2.00  % (8789)Time elapsed: 1.500 s
% 12.71/2.00  % (8789)------------------------------
% 12.71/2.00  % (8789)------------------------------
% 12.71/2.00  % (8771)Time limit reached!
% 12.71/2.00  % (8771)------------------------------
% 12.71/2.00  % (8771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.71/2.00  % (8771)Termination reason: Time limit
% 12.71/2.00  
% 12.71/2.00  % (8771)Memory used [KB]: 29679
% 12.71/2.00  % (8771)Time elapsed: 1.604 s
% 12.71/2.00  % (8771)------------------------------
% 12.71/2.00  % (8771)------------------------------
% 12.71/2.00  % (9091)Refutation not found, incomplete strategy% (9091)------------------------------
% 12.71/2.00  % (9091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.71/2.00  % (9091)Termination reason: Refutation not found, incomplete strategy
% 12.71/2.00  
% 12.71/2.00  % (9091)Memory used [KB]: 10618
% 12.71/2.00  % (9091)Time elapsed: 0.114 s
% 12.71/2.00  % (9091)------------------------------
% 12.71/2.00  % (9091)------------------------------
% 12.71/2.01  % (9088)Time limit reached!
% 12.71/2.01  % (9088)------------------------------
% 12.71/2.01  % (9088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.71/2.01  % (9088)Termination reason: Time limit
% 12.71/2.01  
% 12.71/2.01  % (9088)Memory used [KB]: 10746
% 12.71/2.01  % (9088)Time elapsed: 0.409 s
% 12.71/2.01  % (9088)------------------------------
% 12.71/2.01  % (9088)------------------------------
% 12.71/2.04  % (8764)Time limit reached!
% 12.71/2.04  % (8764)------------------------------
% 12.71/2.04  % (8764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.71/2.04  % (8764)Termination reason: Time limit
% 12.71/2.04  
% 12.71/2.04  % (8764)Memory used [KB]: 143281
% 12.71/2.04  % (8764)Time elapsed: 1.557 s
% 12.71/2.04  % (8764)------------------------------
% 12.71/2.04  % (8764)------------------------------
% 13.84/2.13  % (8776)Time limit reached!
% 13.84/2.13  % (8776)------------------------------
% 13.84/2.13  % (8776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.84/2.13  % (8776)Termination reason: Time limit
% 13.84/2.13  % (8776)Termination phase: Saturation
% 13.84/2.13  
% 13.84/2.13  % (8776)Memory used [KB]: 189208
% 13.84/2.13  % (8776)Time elapsed: 1.300 s
% 13.84/2.13  % (8776)------------------------------
% 13.84/2.13  % (8776)------------------------------
% 14.80/2.23  % (8788)Time limit reached!
% 14.80/2.23  % (8788)------------------------------
% 14.80/2.23  % (8788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.80/2.25  % (8788)Termination reason: Time limit
% 14.80/2.25  
% 14.80/2.25  % (8788)Memory used [KB]: 147758
% 14.80/2.25  % (8788)Time elapsed: 1.760 s
% 14.80/2.25  % (8788)------------------------------
% 14.80/2.25  % (8788)------------------------------
% 14.80/2.28  % (8827)Time limit reached!
% 14.80/2.28  % (8827)------------------------------
% 14.80/2.28  % (8827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.80/2.28  % (8827)Termination reason: Time limit
% 14.80/2.28  % (8827)Termination phase: Saturation
% 14.80/2.28  
% 14.80/2.28  % (8827)Memory used [KB]: 25202
% 14.80/2.28  % (8827)Time elapsed: 1.700 s
% 14.80/2.28  % (8827)------------------------------
% 14.80/2.28  % (8827)------------------------------
% 15.30/2.30  % (8774)Time limit reached!
% 15.30/2.30  % (8774)------------------------------
% 15.30/2.30  % (8774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.30/2.30  % (8774)Termination reason: Time limit
% 15.30/2.30  
% 15.30/2.30  % (8774)Memory used [KB]: 31598
% 15.30/2.30  % (8774)Time elapsed: 1.803 s
% 15.30/2.30  % (8774)------------------------------
% 15.30/2.30  % (8774)------------------------------
% 15.30/2.30  % (9090)Time limit reached!
% 15.30/2.30  % (9090)------------------------------
% 15.30/2.30  % (9090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.30/2.32  % (9090)Termination reason: Time limit
% 15.30/2.32  % (9090)Termination phase: Saturation
% 15.30/2.32  
% 15.30/2.32  % (9090)Memory used [KB]: 50020
% 15.30/2.32  % (9090)Time elapsed: 0.400 s
% 15.30/2.32  % (9090)------------------------------
% 15.30/2.32  % (9090)------------------------------
% 16.31/2.42  % (8970)Time limit reached!
% 16.31/2.42  % (8970)------------------------------
% 16.31/2.42  % (8970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.31/2.42  % (8970)Termination reason: Time limit
% 16.31/2.42  % (8970)Termination phase: Saturation
% 16.31/2.42  
% 16.31/2.42  % (8970)Memory used [KB]: 17910
% 16.31/2.42  % (8970)Time elapsed: 1.300 s
% 16.31/2.42  % (8970)------------------------------
% 16.31/2.42  % (8970)------------------------------
% 16.31/2.44  % (8779)Time limit reached!
% 16.31/2.44  % (8779)------------------------------
% 16.31/2.44  % (8779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.31/2.44  % (8779)Termination reason: Time limit
% 16.31/2.44  % (8779)Termination phase: Saturation
% 16.31/2.44  
% 16.31/2.44  % (8779)Memory used [KB]: 36587
% 16.31/2.44  % (8779)Time elapsed: 2.0000 s
% 16.31/2.44  % (8779)------------------------------
% 16.31/2.44  % (8779)------------------------------
% 16.55/2.45  % (8766)Time limit reached!
% 16.55/2.45  % (8766)------------------------------
% 16.55/2.45  % (8766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.55/2.46  % (8766)Termination reason: Time limit
% 16.55/2.46  % (8766)Termination phase: Saturation
% 16.55/2.46  
% 16.55/2.46  % (8766)Memory used [KB]: 28400
% 16.55/2.46  % (8766)Time elapsed: 2.0000 s
% 16.55/2.46  % (8766)------------------------------
% 16.55/2.46  % (8766)------------------------------
% 17.31/2.53  % (8838)Time limit reached!
% 17.31/2.53  % (8838)------------------------------
% 17.31/2.53  % (8838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.31/2.54  % (8838)Termination reason: Time limit
% 17.31/2.55  % (8838)Termination phase: Saturation
% 17.31/2.55  
% 17.31/2.55  % (8838)Memory used [KB]: 208269
% 17.31/2.55  % (8838)Time elapsed: 1.700 s
% 17.31/2.55  % (8838)------------------------------
% 17.31/2.55  % (8838)------------------------------
% 20.72/3.00  % (8780)Time limit reached!
% 20.72/3.00  % (8780)------------------------------
% 20.72/3.00  % (8780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.13/3.02  % (8780)Termination reason: Time limit
% 21.13/3.02  
% 21.13/3.02  % (8780)Memory used [KB]: 48741
% 21.13/3.02  % (8780)Time elapsed: 2.603 s
% 21.13/3.02  % (8780)------------------------------
% 21.13/3.02  % (8780)------------------------------
% 23.89/3.38  % (8826)Time limit reached!
% 23.89/3.38  % (8826)------------------------------
% 23.89/3.38  % (8826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.89/3.38  % (8826)Termination reason: Time limit
% 23.89/3.38  % (8826)Termination phase: Saturation
% 23.89/3.38  
% 23.89/3.38  % (8826)Memory used [KB]: 41705
% 23.89/3.38  % (8826)Time elapsed: 2.800 s
% 23.89/3.38  % (8826)------------------------------
% 23.89/3.38  % (8826)------------------------------
% 23.89/3.43  % (8773)Time limit reached!
% 23.89/3.43  % (8773)------------------------------
% 23.89/3.43  % (8773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.89/3.43  % (8773)Termination reason: Time limit
% 23.89/3.43  % (8773)Termination phase: Saturation
% 23.89/3.43  
% 23.89/3.43  % (8773)Memory used [KB]: 14967
% 23.89/3.43  % (8773)Time elapsed: 3.0000 s
% 23.89/3.43  % (8773)------------------------------
% 23.89/3.43  % (8773)------------------------------
% 30.43/4.17  % (8930)Refutation found. Thanks to Tanya!
% 30.43/4.17  % SZS status Theorem for theBenchmark
% 30.43/4.17  % SZS output start Proof for theBenchmark
% 30.43/4.17  fof(f31981,plain,(
% 30.43/4.17    $false),
% 30.43/4.17    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f67,f74,f78,f91,f102,f114,f118,f122,f127,f167,f179,f183,f220,f284,f306,f312,f322,f467,f523,f783,f823,f895,f934,f1354,f2314,f3847,f4192,f4826,f6959,f8438,f9243,f9450,f12568,f28320,f31838,f31962])).
% 30.43/4.17  fof(f31962,plain,(
% 30.43/4.17    ~spl2_2 | ~spl2_9 | ~spl2_21 | ~spl2_47 | spl2_239),
% 30.43/4.17    inference(avatar_contradiction_clause,[],[f31961])).
% 30.43/4.17  fof(f31961,plain,(
% 30.43/4.17    $false | (~spl2_2 | ~spl2_9 | ~spl2_21 | ~spl2_47 | spl2_239)),
% 30.43/4.17    inference(subsumption_resolution,[],[f31960,f311])).
% 30.43/4.17  fof(f311,plain,(
% 30.43/4.17    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | ~spl2_21),
% 30.43/4.17    inference(avatar_component_clause,[],[f310])).
% 30.43/4.17  fof(f310,plain,(
% 30.43/4.17    spl2_21 <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 30.43/4.17  fof(f31960,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | (~spl2_2 | ~spl2_9 | ~spl2_47 | spl2_239)),
% 30.43/4.17    inference(forward_demodulation,[],[f31959,f1353])).
% 30.43/4.17  fof(f1353,plain,(
% 30.43/4.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_47),
% 30.43/4.17    inference(avatar_component_clause,[],[f1352])).
% 30.43/4.17  fof(f1352,plain,(
% 30.43/4.17    spl2_47 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 30.43/4.17  fof(f31959,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) | (~spl2_2 | ~spl2_9 | spl2_239)),
% 30.43/4.17    inference(forward_demodulation,[],[f31958,f101])).
% 30.43/4.17  fof(f101,plain,(
% 30.43/4.17    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_9),
% 30.43/4.17    inference(avatar_component_clause,[],[f100])).
% 30.43/4.17  fof(f100,plain,(
% 30.43/4.17    spl2_9 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 30.43/4.17  fof(f31958,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | (~spl2_2 | ~spl2_9 | spl2_239)),
% 30.43/4.17    inference(forward_demodulation,[],[f31877,f51])).
% 30.43/4.17  fof(f51,plain,(
% 30.43/4.17    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_2),
% 30.43/4.17    inference(avatar_component_clause,[],[f50])).
% 30.43/4.17  fof(f50,plain,(
% 30.43/4.17    spl2_2 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 30.43/4.17  fof(f31877,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))) | (~spl2_9 | spl2_239)),
% 30.43/4.17    inference(superposition,[],[f31837,f101])).
% 30.43/4.17  fof(f31837,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,sK1)) | spl2_239),
% 30.43/4.17    inference(avatar_component_clause,[],[f31836])).
% 30.43/4.17  fof(f31836,plain,(
% 30.43/4.17    spl2_239 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,sK1))),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_239])])).
% 30.43/4.17  fof(f31838,plain,(
% 30.43/4.17    ~spl2_239 | spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_9 | ~spl2_30 | ~spl2_39 | ~spl2_47 | ~spl2_96 | ~spl2_183),
% 30.43/4.17    inference(avatar_split_clause,[],[f28458,f28318,f6957,f1352,f932,f781,f100,f89,f50,f46,f31836])).
% 30.43/4.17  fof(f46,plain,(
% 30.43/4.17    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 30.43/4.17  fof(f89,plain,(
% 30.43/4.17    spl2_8 <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 30.43/4.17  fof(f781,plain,(
% 30.43/4.17    spl2_30 <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 30.43/4.17  fof(f932,plain,(
% 30.43/4.17    spl2_39 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 30.43/4.17  fof(f6957,plain,(
% 30.43/4.17    spl2_96 <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4)))),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 30.43/4.17  fof(f28318,plain,(
% 30.43/4.17    spl2_183 <=> ! [X73,X72] : (X72 = X73 | k1_xboole_0 != k5_xboole_0(X72,X73))),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_183])])).
% 30.43/4.17  fof(f28458,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,sK1)) | (spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_9 | ~spl2_30 | ~spl2_39 | ~spl2_47 | ~spl2_96 | ~spl2_183)),
% 30.43/4.17    inference(forward_demodulation,[],[f28457,f51])).
% 30.43/4.17  fof(f28457,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | (spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_9 | ~spl2_30 | ~spl2_39 | ~spl2_47 | ~spl2_96 | ~spl2_183)),
% 30.43/4.17    inference(forward_demodulation,[],[f28456,f813])).
% 30.43/4.17  fof(f813,plain,(
% 30.43/4.17    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6)))) ) | (~spl2_9 | ~spl2_30)),
% 30.43/4.17    inference(forward_demodulation,[],[f802,f101])).
% 30.43/4.17  fof(f802,plain,(
% 30.43/4.17    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6))) ) | (~spl2_9 | ~spl2_30)),
% 30.43/4.17    inference(superposition,[],[f101,f782])).
% 30.43/4.17  fof(f782,plain,(
% 30.43/4.17    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) ) | ~spl2_30),
% 30.43/4.17    inference(avatar_component_clause,[],[f781])).
% 30.43/4.17  fof(f28456,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,sK1)) | (spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_9 | ~spl2_39 | ~spl2_47 | ~spl2_96 | ~spl2_183)),
% 30.43/4.17    inference(forward_demodulation,[],[f28455,f933])).
% 30.43/4.17  fof(f933,plain,(
% 30.43/4.17    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl2_39),
% 30.43/4.17    inference(avatar_component_clause,[],[f932])).
% 30.43/4.17  fof(f28455,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,sK1)) | (spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_9 | ~spl2_47 | ~spl2_96 | ~spl2_183)),
% 30.43/4.17    inference(forward_demodulation,[],[f28364,f8390])).
% 30.43/4.17  fof(f8390,plain,(
% 30.43/4.17    ( ! [X78,X76,X77] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(X76,k5_xboole_0(k4_xboole_0(X78,X76),k4_xboole_0(X76,X77)))) ) | (~spl2_2 | ~spl2_8 | ~spl2_9 | ~spl2_47 | ~spl2_96)),
% 30.43/4.17    inference(forward_demodulation,[],[f8389,f101])).
% 30.43/4.17  fof(f8389,plain,(
% 30.43/4.17    ( ! [X78,X76,X77] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77))) ) | (~spl2_2 | ~spl2_8 | ~spl2_47 | ~spl2_96)),
% 30.43/4.17    inference(forward_demodulation,[],[f8388,f90])).
% 30.43/4.17  fof(f90,plain,(
% 30.43/4.17    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl2_8),
% 30.43/4.17    inference(avatar_component_clause,[],[f89])).
% 30.43/4.17  fof(f8388,plain,(
% 30.43/4.17    ( ! [X78,X76,X77] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k5_xboole_0(k1_xboole_0,k4_xboole_0(X76,X77)))) ) | (~spl2_2 | ~spl2_47 | ~spl2_96)),
% 30.43/4.17    inference(forward_demodulation,[],[f8272,f51])).
% 30.43/4.17  fof(f8272,plain,(
% 30.43/4.17    ( ! [X78,X76,X77] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k4_xboole_0(X76,X77)) = k5_xboole_0(k5_xboole_0(X76,k4_xboole_0(X78,X76)),k5_xboole_0(k4_xboole_0(X76,X77),k1_xboole_0))) ) | (~spl2_47 | ~spl2_96)),
% 30.43/4.17    inference(superposition,[],[f1353,f6958])).
% 30.43/4.17  fof(f6958,plain,(
% 30.43/4.17    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4)))) ) | ~spl2_96),
% 30.43/4.17    inference(avatar_component_clause,[],[f6957])).
% 30.43/4.17  fof(f28364,plain,(
% 30.43/4.17    k1_xboole_0 != k5_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | (spl2_1 | ~spl2_183)),
% 30.43/4.17    inference(unit_resulting_resolution,[],[f47,f28319])).
% 30.43/4.17  fof(f28319,plain,(
% 30.43/4.17    ( ! [X72,X73] : (k1_xboole_0 != k5_xboole_0(X72,X73) | X72 = X73) ) | ~spl2_183),
% 30.43/4.17    inference(avatar_component_clause,[],[f28318])).
% 30.43/4.17  fof(f47,plain,(
% 30.43/4.17    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 30.43/4.17    inference(avatar_component_clause,[],[f46])).
% 30.43/4.17  fof(f28320,plain,(
% 30.43/4.17    spl2_183 | ~spl2_32 | ~spl2_129),
% 30.43/4.17    inference(avatar_split_clause,[],[f13032,f12566,f821,f28318])).
% 30.43/4.17  fof(f821,plain,(
% 30.43/4.17    spl2_32 <=> ! [X9,X10] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 30.43/4.17  fof(f12566,plain,(
% 30.43/4.17    spl2_129 <=> ! [X3,X4] : (k5_xboole_0(X3,X4) = X4 | k1_xboole_0 != X3)),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).
% 30.43/4.17  fof(f13032,plain,(
% 30.43/4.17    ( ! [X72,X73] : (X72 = X73 | k1_xboole_0 != k5_xboole_0(X72,X73)) ) | (~spl2_32 | ~spl2_129)),
% 30.43/4.17    inference(superposition,[],[f12567,f822])).
% 30.43/4.17  fof(f822,plain,(
% 30.43/4.17    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) ) | ~spl2_32),
% 30.43/4.17    inference(avatar_component_clause,[],[f821])).
% 30.43/4.17  fof(f12567,plain,(
% 30.43/4.17    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = X4 | k1_xboole_0 != X3) ) | ~spl2_129),
% 30.43/4.17    inference(avatar_component_clause,[],[f12566])).
% 30.43/4.17  fof(f12568,plain,(
% 30.43/4.17    spl2_129 | ~spl2_9 | ~spl2_29 | ~spl2_104),
% 30.43/4.17    inference(avatar_split_clause,[],[f9631,f9448,f521,f100,f12566])).
% 30.43/4.17  fof(f521,plain,(
% 30.43/4.17    spl2_29 <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 30.43/4.17  fof(f9448,plain,(
% 30.43/4.17    spl2_104 <=> ! [X1] : (k5_xboole_0(X1,X1) = X1 | k1_xboole_0 != X1)),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 30.43/4.17  fof(f9631,plain,(
% 30.43/4.17    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = X4 | k1_xboole_0 != X3) ) | (~spl2_9 | ~spl2_29 | ~spl2_104)),
% 30.43/4.17    inference(forward_demodulation,[],[f9529,f522])).
% 30.43/4.17  fof(f522,plain,(
% 30.43/4.17    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) ) | ~spl2_29),
% 30.43/4.17    inference(avatar_component_clause,[],[f521])).
% 30.43/4.17  fof(f9529,plain,(
% 30.43/4.17    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X3,X4)) | k1_xboole_0 != X3) ) | (~spl2_9 | ~spl2_104)),
% 30.43/4.17    inference(superposition,[],[f101,f9449])).
% 30.43/4.17  fof(f9449,plain,(
% 30.43/4.17    ( ! [X1] : (k5_xboole_0(X1,X1) = X1 | k1_xboole_0 != X1) ) | ~spl2_104),
% 30.43/4.17    inference(avatar_component_clause,[],[f9448])).
% 30.43/4.17  fof(f9450,plain,(
% 30.43/4.17    spl2_104 | ~spl2_3 | ~spl2_102),
% 30.43/4.17    inference(avatar_split_clause,[],[f9285,f9241,f54,f9448])).
% 30.43/4.17  fof(f54,plain,(
% 30.43/4.17    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 30.43/4.17  fof(f9241,plain,(
% 30.43/4.17    spl2_102 <=> ! [X34] : (k4_xboole_0(X34,X34) = X34 | k1_xboole_0 != X34)),
% 30.43/4.17    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).
% 30.43/4.18  fof(f9285,plain,(
% 30.43/4.18    ( ! [X1] : (k5_xboole_0(X1,X1) = X1 | k1_xboole_0 != X1) ) | (~spl2_3 | ~spl2_102)),
% 30.43/4.18    inference(superposition,[],[f55,f9242])).
% 30.43/4.18  fof(f9242,plain,(
% 30.43/4.18    ( ! [X34] : (k4_xboole_0(X34,X34) = X34 | k1_xboole_0 != X34) ) | ~spl2_102),
% 30.43/4.18    inference(avatar_component_clause,[],[f9241])).
% 30.43/4.18  fof(f55,plain,(
% 30.43/4.18    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_3),
% 30.43/4.18    inference(avatar_component_clause,[],[f54])).
% 30.43/4.18  fof(f9243,plain,(
% 30.43/4.18    spl2_102 | ~spl2_3 | ~spl2_11 | ~spl2_39 | ~spl2_59 | ~spl2_101),
% 30.43/4.18    inference(avatar_split_clause,[],[f9227,f8436,f2312,f932,f112,f54,f9241])).
% 30.43/4.18  fof(f112,plain,(
% 30.43/4.18    spl2_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 30.43/4.18  fof(f2312,plain,(
% 30.43/4.18    spl2_59 <=> ! [X7,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,k4_xboole_0(X7,X6)))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 30.43/4.18  fof(f8436,plain,(
% 30.43/4.18    spl2_101 <=> ! [X9,X7,X8] : (k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) != k4_xboole_0(X9,k5_xboole_0(X7,k4_xboole_0(X7,X8))) | k5_xboole_0(X7,k4_xboole_0(X7,X8)) = X9)),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 30.43/4.18  fof(f9227,plain,(
% 30.43/4.18    ( ! [X34] : (k4_xboole_0(X34,X34) = X34 | k1_xboole_0 != X34) ) | (~spl2_3 | ~spl2_11 | ~spl2_39 | ~spl2_59 | ~spl2_101)),
% 30.43/4.18    inference(forward_demodulation,[],[f9226,f55])).
% 30.43/4.18  fof(f9226,plain,(
% 30.43/4.18    ( ! [X34] : (k1_xboole_0 != X34 | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34))) ) | (~spl2_3 | ~spl2_11 | ~spl2_39 | ~spl2_59 | ~spl2_101)),
% 30.43/4.18    inference(forward_demodulation,[],[f9225,f55])).
% 30.43/4.18  fof(f9225,plain,(
% 30.43/4.18    ( ! [X34] : (k1_xboole_0 != k5_xboole_0(X34,k4_xboole_0(X34,X34)) | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34))) ) | (~spl2_11 | ~spl2_39 | ~spl2_59 | ~spl2_101)),
% 30.43/4.18    inference(forward_demodulation,[],[f9224,f113])).
% 30.43/4.18  fof(f113,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_11),
% 30.43/4.18    inference(avatar_component_clause,[],[f112])).
% 30.43/4.18  fof(f9224,plain,(
% 30.43/4.18    ( ! [X34] : (k1_xboole_0 != k5_xboole_0(X34,k5_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,X34)))) | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34))) ) | (~spl2_39 | ~spl2_59 | ~spl2_101)),
% 30.43/4.18    inference(forward_demodulation,[],[f9043,f933])).
% 30.43/4.18  fof(f9043,plain,(
% 30.43/4.18    ( ! [X34] : (k1_xboole_0 != k5_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,X34)))) | k4_xboole_0(X34,X34) = k5_xboole_0(X34,k4_xboole_0(X34,X34))) ) | (~spl2_59 | ~spl2_101)),
% 30.43/4.18    inference(superposition,[],[f8437,f2313])).
% 30.43/4.18  fof(f2313,plain,(
% 30.43/4.18    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,k4_xboole_0(X7,X6)))) ) | ~spl2_59),
% 30.43/4.18    inference(avatar_component_clause,[],[f2312])).
% 30.43/4.18  fof(f8437,plain,(
% 30.43/4.18    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) != k4_xboole_0(X9,k5_xboole_0(X7,k4_xboole_0(X7,X8))) | k5_xboole_0(X7,k4_xboole_0(X7,X8)) = X9) ) | ~spl2_101),
% 30.43/4.18    inference(avatar_component_clause,[],[f8436])).
% 30.43/4.18  fof(f8438,plain,(
% 30.43/4.18    spl2_101 | ~spl2_6 | ~spl2_22),
% 30.43/4.18    inference(avatar_split_clause,[],[f382,f320,f72,f8436])).
% 30.43/4.18  fof(f72,plain,(
% 30.43/4.18    spl2_6 <=> ! [X1,X0] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 30.43/4.18  fof(f320,plain,(
% 30.43/4.18    spl2_22 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 30.43/4.18  fof(f382,plain,(
% 30.43/4.18    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) != k4_xboole_0(X9,k5_xboole_0(X7,k4_xboole_0(X7,X8))) | k5_xboole_0(X7,k4_xboole_0(X7,X8)) = X9) ) | (~spl2_6 | ~spl2_22)),
% 30.43/4.18    inference(superposition,[],[f73,f321])).
% 30.43/4.18  fof(f321,plain,(
% 30.43/4.18    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | ~spl2_22),
% 30.43/4.18    inference(avatar_component_clause,[],[f320])).
% 30.43/4.18  fof(f73,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) ) | ~spl2_6),
% 30.43/4.18    inference(avatar_component_clause,[],[f72])).
% 30.43/4.18  fof(f6959,plain,(
% 30.43/4.18    spl2_96 | ~spl2_21 | ~spl2_77 | ~spl2_87),
% 30.43/4.18    inference(avatar_split_clause,[],[f5123,f4824,f4190,f310,f6957])).
% 30.43/4.18  fof(f4190,plain,(
% 30.43/4.18    spl2_77 <=> ! [X5,X7,X6] : k4_xboole_0(k4_xboole_0(X5,X6),X7) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7)))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 30.43/4.18  fof(f4824,plain,(
% 30.43/4.18    spl2_87 <=> ! [X51,X50,X52] : k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = X50),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 30.43/4.18  fof(f5123,plain,(
% 30.43/4.18    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4)))) ) | (~spl2_21 | ~spl2_77 | ~spl2_87)),
% 30.43/4.18    inference(forward_demodulation,[],[f5051,f311])).
% 30.43/4.18  fof(f5051,plain,(
% 30.43/4.18    ( ! [X6,X4,X5] : (k5_xboole_0(X4,X4) = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X6,X4)))) ) | (~spl2_77 | ~spl2_87)),
% 30.43/4.18    inference(superposition,[],[f4191,f4825])).
% 30.43/4.18  fof(f4825,plain,(
% 30.43/4.18    ( ! [X52,X50,X51] : (k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = X50) ) | ~spl2_87),
% 30.43/4.18    inference(avatar_component_clause,[],[f4824])).
% 30.43/4.18  fof(f4191,plain,(
% 30.43/4.18    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),X7) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7)))) ) | ~spl2_77),
% 30.43/4.18    inference(avatar_component_clause,[],[f4190])).
% 30.43/4.18  fof(f4826,plain,(
% 30.43/4.18    spl2_87 | ~spl2_4 | ~spl2_7 | ~spl2_24 | ~spl2_76),
% 30.43/4.18    inference(avatar_split_clause,[],[f4759,f3845,f465,f76,f58,f4824])).
% 30.43/4.18  fof(f58,plain,(
% 30.43/4.18    spl2_4 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 30.43/4.18  fof(f76,plain,(
% 30.43/4.18    spl2_7 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 30.43/4.18  fof(f465,plain,(
% 30.43/4.18    spl2_24 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 30.43/4.18  fof(f3845,plain,(
% 30.43/4.18    spl2_76 <=> ! [X3,X2,X4] : k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4)),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 30.43/4.18  fof(f4759,plain,(
% 30.43/4.18    ( ! [X52,X50,X51] : (k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = X50) ) | (~spl2_4 | ~spl2_7 | ~spl2_24 | ~spl2_76)),
% 30.43/4.18    inference(forward_demodulation,[],[f4758,f77])).
% 30.43/4.18  fof(f77,plain,(
% 30.43/4.18    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_7),
% 30.43/4.18    inference(avatar_component_clause,[],[f76])).
% 30.43/4.18  fof(f4758,plain,(
% 30.43/4.18    ( ! [X52,X50,X51] : (k5_xboole_0(X50,k1_xboole_0) = k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50))))) ) | (~spl2_4 | ~spl2_24 | ~spl2_76)),
% 30.43/4.18    inference(forward_demodulation,[],[f4641,f59])).
% 30.43/4.18  fof(f59,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl2_4),
% 30.43/4.18    inference(avatar_component_clause,[],[f58])).
% 30.43/4.18  fof(f4641,plain,(
% 30.43/4.18    ( ! [X52,X50,X51] : (k4_xboole_0(X50,k4_xboole_0(X52,k5_xboole_0(X50,k4_xboole_0(X51,X50)))) = k5_xboole_0(X50,k4_xboole_0(X50,k5_xboole_0(X50,k4_xboole_0(X51,X50))))) ) | (~spl2_24 | ~spl2_76)),
% 30.43/4.18    inference(superposition,[],[f3846,f466])).
% 30.43/4.18  fof(f466,plain,(
% 30.43/4.18    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | ~spl2_24),
% 30.43/4.18    inference(avatar_component_clause,[],[f465])).
% 30.43/4.18  fof(f3846,plain,(
% 30.43/4.18    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4)) ) | ~spl2_76),
% 30.43/4.18    inference(avatar_component_clause,[],[f3845])).
% 30.43/4.18  fof(f4192,plain,(
% 30.43/4.18    spl2_77 | ~spl2_11 | ~spl2_12 | ~spl2_22),
% 30.43/4.18    inference(avatar_split_clause,[],[f405,f320,f116,f112,f4190])).
% 30.43/4.18  fof(f116,plain,(
% 30.43/4.18    spl2_12 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 30.43/4.18  fof(f405,plain,(
% 30.43/4.18    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),X7) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7)))) ) | (~spl2_11 | ~spl2_12 | ~spl2_22)),
% 30.43/4.18    inference(forward_demodulation,[],[f358,f158])).
% 30.43/4.18  fof(f158,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_11 | ~spl2_12)),
% 30.43/4.18    inference(superposition,[],[f113,f117])).
% 30.43/4.18  fof(f117,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_12),
% 30.43/4.18    inference(avatar_component_clause,[],[f116])).
% 30.43/4.18  fof(f358,plain,(
% 30.43/4.18    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))),X7)) ) | (~spl2_12 | ~spl2_22)),
% 30.43/4.18    inference(superposition,[],[f321,f117])).
% 30.43/4.18  fof(f3847,plain,(
% 30.43/4.18    spl2_76 | ~spl2_4 | ~spl2_7 | ~spl2_22),
% 30.43/4.18    inference(avatar_split_clause,[],[f404,f320,f76,f58,f3845])).
% 30.43/4.18  fof(f404,plain,(
% 30.43/4.18    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4)) ) | (~spl2_4 | ~spl2_7 | ~spl2_22)),
% 30.43/4.18    inference(forward_demodulation,[],[f357,f77])).
% 30.43/4.18  fof(f357,plain,(
% 30.43/4.18    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(k5_xboole_0(X2,k1_xboole_0),X4)) ) | (~spl2_4 | ~spl2_22)),
% 30.43/4.18    inference(superposition,[],[f321,f59])).
% 30.43/4.18  fof(f2314,plain,(
% 30.43/4.18    spl2_59 | ~spl2_2 | ~spl2_4 | ~spl2_24),
% 30.43/4.18    inference(avatar_split_clause,[],[f492,f465,f58,f50,f2312])).
% 30.43/4.18  fof(f492,plain,(
% 30.43/4.18    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,k4_xboole_0(X7,X6)))) ) | (~spl2_2 | ~spl2_4 | ~spl2_24)),
% 30.43/4.18    inference(forward_demodulation,[],[f482,f51])).
% 30.43/4.18  fof(f482,plain,(
% 30.43/4.18    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(k4_xboole_0(X7,X6),X6))) ) | (~spl2_4 | ~spl2_24)),
% 30.43/4.18    inference(superposition,[],[f59,f466])).
% 30.43/4.18  fof(f1354,plain,(
% 30.43/4.18    spl2_47 | ~spl2_11 | ~spl2_14 | ~spl2_35),
% 30.43/4.18    inference(avatar_split_clause,[],[f896,f893,f125,f112,f1352])).
% 30.43/4.18  fof(f125,plain,(
% 30.43/4.18    spl2_14 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 30.43/4.18  fof(f893,plain,(
% 30.43/4.18    spl2_35 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 30.43/4.18  fof(f896,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_11 | ~spl2_14 | ~spl2_35)),
% 30.43/4.18    inference(forward_demodulation,[],[f894,f211])).
% 30.43/4.18  fof(f211,plain,(
% 30.43/4.18    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_11 | ~spl2_14)),
% 30.43/4.18    inference(superposition,[],[f113,f126])).
% 30.43/4.18  fof(f126,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_14),
% 30.43/4.18    inference(avatar_component_clause,[],[f125])).
% 30.43/4.18  fof(f894,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_35),
% 30.43/4.18    inference(avatar_component_clause,[],[f893])).
% 30.43/4.18  fof(f934,plain,(
% 30.43/4.18    spl2_39 | ~spl2_11 | ~spl2_14),
% 30.43/4.18    inference(avatar_split_clause,[],[f211,f125,f112,f932])).
% 30.43/4.18  fof(f895,plain,(
% 30.43/4.18    spl2_35 | ~spl2_11 | ~spl2_12),
% 30.43/4.18    inference(avatar_split_clause,[],[f158,f116,f112,f893])).
% 30.43/4.18  fof(f823,plain,(
% 30.43/4.18    spl2_32 | ~spl2_30),
% 30.43/4.18    inference(avatar_split_clause,[],[f789,f781,f821])).
% 30.43/4.18  fof(f789,plain,(
% 30.43/4.18    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) ) | ~spl2_30),
% 30.43/4.18    inference(superposition,[],[f782,f782])).
% 30.43/4.18  fof(f783,plain,(
% 30.43/4.18    spl2_30 | ~spl2_2 | ~spl2_29),
% 30.43/4.18    inference(avatar_split_clause,[],[f525,f521,f50,f781])).
% 30.43/4.18  fof(f525,plain,(
% 30.43/4.18    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) ) | (~spl2_2 | ~spl2_29)),
% 30.43/4.18    inference(superposition,[],[f522,f51])).
% 30.43/4.18  fof(f523,plain,(
% 30.43/4.18    spl2_29 | ~spl2_17 | ~spl2_19),
% 30.43/4.18    inference(avatar_split_clause,[],[f286,f282,f181,f521])).
% 30.43/4.18  fof(f181,plain,(
% 30.43/4.18    spl2_17 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = X1),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 30.43/4.18  fof(f282,plain,(
% 30.43/4.18    spl2_19 <=> ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 30.43/4.18  fof(f286,plain,(
% 30.43/4.18    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) ) | (~spl2_17 | ~spl2_19)),
% 30.43/4.18    inference(superposition,[],[f182,f283])).
% 30.43/4.18  fof(f283,plain,(
% 30.43/4.18    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) ) | ~spl2_19),
% 30.43/4.18    inference(avatar_component_clause,[],[f282])).
% 30.43/4.18  fof(f182,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = X1) ) | ~spl2_17),
% 30.43/4.18    inference(avatar_component_clause,[],[f181])).
% 30.43/4.18  fof(f467,plain,(
% 30.43/4.18    spl2_24 | ~spl2_11 | ~spl2_16),
% 30.43/4.18    inference(avatar_split_clause,[],[f243,f177,f112,f465])).
% 30.43/4.18  fof(f177,plain,(
% 30.43/4.18    spl2_16 <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 30.43/4.18  fof(f243,plain,(
% 30.43/4.18    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | (~spl2_11 | ~spl2_16)),
% 30.43/4.18    inference(superposition,[],[f178,f113])).
% 30.43/4.18  fof(f178,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | ~spl2_16),
% 30.43/4.18    inference(avatar_component_clause,[],[f177])).
% 30.43/4.18  fof(f322,plain,(
% 30.43/4.18    spl2_22 | ~spl2_11 | ~spl2_14 | ~spl2_20),
% 30.43/4.18    inference(avatar_split_clause,[],[f308,f304,f125,f112,f320])).
% 30.43/4.18  fof(f304,plain,(
% 30.43/4.18    spl2_20 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 30.43/4.18  fof(f308,plain,(
% 30.43/4.18    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | (~spl2_11 | ~spl2_14 | ~spl2_20)),
% 30.43/4.18    inference(forward_demodulation,[],[f307,f211])).
% 30.43/4.18  fof(f307,plain,(
% 30.43/4.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | (~spl2_11 | ~spl2_14 | ~spl2_20)),
% 30.43/4.18    inference(forward_demodulation,[],[f305,f211])).
% 30.43/4.18  fof(f305,plain,(
% 30.43/4.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl2_20),
% 30.43/4.18    inference(avatar_component_clause,[],[f304])).
% 30.43/4.18  fof(f312,plain,(
% 30.43/4.18    spl2_21 | ~spl2_15 | ~spl2_19),
% 30.43/4.18    inference(avatar_split_clause,[],[f287,f282,f165,f310])).
% 30.43/4.18  fof(f165,plain,(
% 30.43/4.18    spl2_15 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 30.43/4.18  fof(f287,plain,(
% 30.43/4.18    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | (~spl2_15 | ~spl2_19)),
% 30.43/4.18    inference(superposition,[],[f166,f283])).
% 30.43/4.18  fof(f166,plain,(
% 30.43/4.18    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | ~spl2_15),
% 30.43/4.18    inference(avatar_component_clause,[],[f165])).
% 30.43/4.18  fof(f306,plain,(
% 30.43/4.18    spl2_20),
% 30.43/4.18    inference(avatar_split_clause,[],[f42,f304])).
% 30.43/4.18  fof(f42,plain,(
% 30.43/4.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 30.43/4.18    inference(definition_unfolding,[],[f33,f30,f30])).
% 30.43/4.18  fof(f30,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 30.43/4.18    inference(cnf_transformation,[],[f10])).
% 30.43/4.18  fof(f10,axiom,(
% 30.43/4.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 30.43/4.18  fof(f33,plain,(
% 30.43/4.18    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 30.43/4.18    inference(cnf_transformation,[],[f11])).
% 30.43/4.18  fof(f11,axiom,(
% 30.43/4.18    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 30.43/4.18  fof(f284,plain,(
% 30.43/4.18    spl2_19 | ~spl2_7 | ~spl2_11 | ~spl2_18),
% 30.43/4.18    inference(avatar_split_clause,[],[f230,f218,f112,f76,f282])).
% 30.43/4.18  fof(f218,plain,(
% 30.43/4.18    spl2_18 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 30.43/4.18  fof(f230,plain,(
% 30.43/4.18    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) ) | (~spl2_7 | ~spl2_11 | ~spl2_18)),
% 30.43/4.18    inference(forward_demodulation,[],[f226,f77])).
% 30.43/4.18  fof(f226,plain,(
% 30.43/4.18    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) ) | (~spl2_11 | ~spl2_18)),
% 30.43/4.18    inference(superposition,[],[f113,f219])).
% 30.43/4.18  fof(f219,plain,(
% 30.43/4.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | ~spl2_18),
% 30.43/4.18    inference(avatar_component_clause,[],[f218])).
% 30.43/4.18  fof(f220,plain,(
% 30.43/4.18    spl2_18 | ~spl2_4 | ~spl2_14),
% 30.43/4.18    inference(avatar_split_clause,[],[f203,f125,f58,f218])).
% 30.43/4.18  fof(f203,plain,(
% 30.43/4.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl2_4 | ~spl2_14)),
% 30.43/4.18    inference(superposition,[],[f126,f59])).
% 30.43/4.18  fof(f183,plain,(
% 30.43/4.18    spl2_17 | ~spl2_8 | ~spl2_9 | ~spl2_15),
% 30.43/4.18    inference(avatar_split_clause,[],[f175,f165,f100,f89,f181])).
% 30.43/4.18  fof(f175,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = X1) ) | (~spl2_8 | ~spl2_9 | ~spl2_15)),
% 30.43/4.18    inference(forward_demodulation,[],[f172,f90])).
% 30.43/4.18  fof(f172,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) ) | (~spl2_9 | ~spl2_15)),
% 30.43/4.18    inference(superposition,[],[f101,f166])).
% 30.43/4.18  fof(f179,plain,(
% 30.43/4.18    spl2_16 | ~spl2_13),
% 30.43/4.18    inference(avatar_split_clause,[],[f123,f120,f177])).
% 30.43/4.18  fof(f120,plain,(
% 30.43/4.18    spl2_13 <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 30.43/4.18  fof(f123,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | ~spl2_13),
% 30.43/4.18    inference(forward_demodulation,[],[f121,f42])).
% 30.43/4.18  fof(f121,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) ) | ~spl2_13),
% 30.43/4.18    inference(avatar_component_clause,[],[f120])).
% 30.43/4.18  fof(f167,plain,(
% 30.43/4.18    spl2_15 | ~spl2_4 | ~spl2_11),
% 30.43/4.18    inference(avatar_split_clause,[],[f148,f112,f58,f165])).
% 30.43/4.18  fof(f148,plain,(
% 30.43/4.18    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl2_4 | ~spl2_11)),
% 30.43/4.18    inference(superposition,[],[f113,f59])).
% 30.43/4.18  fof(f127,plain,(
% 30.43/4.18    spl2_14),
% 30.43/4.18    inference(avatar_split_clause,[],[f41,f125])).
% 30.43/4.18  fof(f41,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 30.43/4.18    inference(definition_unfolding,[],[f29,f30])).
% 30.43/4.18  fof(f29,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 30.43/4.18    inference(cnf_transformation,[],[f9])).
% 30.43/4.18  fof(f9,axiom,(
% 30.43/4.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 30.43/4.18  fof(f122,plain,(
% 30.43/4.18    spl2_13),
% 30.43/4.18    inference(avatar_split_clause,[],[f39,f120])).
% 30.43/4.18  fof(f39,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 30.43/4.18    inference(definition_unfolding,[],[f25,f27,f30])).
% 30.43/4.18  fof(f27,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 30.43/4.18    inference(cnf_transformation,[],[f13])).
% 30.43/4.18  fof(f13,axiom,(
% 30.43/4.18    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 30.43/4.18  fof(f25,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 30.43/4.18    inference(cnf_transformation,[],[f6])).
% 30.43/4.18  fof(f6,axiom,(
% 30.43/4.18    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 30.43/4.18  fof(f118,plain,(
% 30.43/4.18    spl2_12),
% 30.43/4.18    inference(avatar_split_clause,[],[f38,f116])).
% 30.43/4.18  fof(f38,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 30.43/4.18    inference(definition_unfolding,[],[f24,f30,f30])).
% 30.43/4.18  fof(f24,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 30.43/4.18    inference(cnf_transformation,[],[f1])).
% 30.43/4.18  fof(f1,axiom,(
% 30.43/4.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 30.43/4.18  fof(f114,plain,(
% 30.43/4.18    spl2_11),
% 30.43/4.18    inference(avatar_split_clause,[],[f35,f112])).
% 30.43/4.18  fof(f35,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 30.43/4.18    inference(definition_unfolding,[],[f28,f30])).
% 30.43/4.18  fof(f28,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 30.43/4.18    inference(cnf_transformation,[],[f4])).
% 30.43/4.18  fof(f4,axiom,(
% 30.43/4.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 30.43/4.18  fof(f102,plain,(
% 30.43/4.18    spl2_9),
% 30.43/4.18    inference(avatar_split_clause,[],[f32,f100])).
% 30.43/4.18  fof(f32,plain,(
% 30.43/4.18    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 30.43/4.18    inference(cnf_transformation,[],[f12])).
% 30.43/4.18  fof(f12,axiom,(
% 30.43/4.18    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 30.43/4.18  fof(f91,plain,(
% 30.43/4.18    spl2_8 | ~spl2_2 | ~spl2_7),
% 30.43/4.18    inference(avatar_split_clause,[],[f79,f76,f50,f89])).
% 30.43/4.18  fof(f79,plain,(
% 30.43/4.18    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl2_2 | ~spl2_7)),
% 30.43/4.18    inference(superposition,[],[f77,f51])).
% 30.43/4.18  fof(f78,plain,(
% 30.43/4.18    spl2_7 | ~spl2_3 | ~spl2_5),
% 30.43/4.18    inference(avatar_split_clause,[],[f68,f65,f54,f76])).
% 30.43/4.18  fof(f65,plain,(
% 30.43/4.18    spl2_5 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 30.43/4.18    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 30.43/4.18  fof(f68,plain,(
% 30.43/4.18    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_3 | ~spl2_5)),
% 30.43/4.18    inference(superposition,[],[f55,f66])).
% 30.43/4.18  fof(f66,plain,(
% 30.43/4.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_5),
% 30.43/4.18    inference(avatar_component_clause,[],[f65])).
% 30.43/4.18  fof(f74,plain,(
% 30.43/4.18    spl2_6),
% 30.43/4.18    inference(avatar_split_clause,[],[f31,f72])).
% 30.43/4.18  fof(f31,plain,(
% 30.43/4.18    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 30.43/4.18    inference(cnf_transformation,[],[f18])).
% 30.43/4.18  fof(f18,plain,(
% 30.43/4.18    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 30.43/4.18    inference(ennf_transformation,[],[f7])).
% 30.43/4.18  fof(f7,axiom,(
% 30.43/4.18    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 30.43/4.18  fof(f67,plain,(
% 30.43/4.18    spl2_5 | ~spl2_3 | ~spl2_4),
% 30.43/4.18    inference(avatar_split_clause,[],[f62,f58,f54,f65])).
% 30.43/4.18  fof(f62,plain,(
% 30.43/4.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_3 | ~spl2_4)),
% 30.43/4.18    inference(superposition,[],[f59,f55])).
% 30.43/4.18  fof(f60,plain,(
% 30.43/4.18    spl2_4),
% 30.43/4.18    inference(avatar_split_clause,[],[f40,f58])).
% 30.43/4.18  fof(f40,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 30.43/4.18    inference(definition_unfolding,[],[f26,f27])).
% 30.43/4.18  fof(f26,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 30.43/4.18    inference(cnf_transformation,[],[f8])).
% 30.43/4.18  fof(f8,axiom,(
% 30.43/4.18    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 30.43/4.18  fof(f56,plain,(
% 30.43/4.18    spl2_3),
% 30.43/4.18    inference(avatar_split_clause,[],[f37,f54])).
% 30.43/4.18  fof(f37,plain,(
% 30.43/4.18    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 30.43/4.18    inference(definition_unfolding,[],[f22,f27])).
% 30.43/4.18  fof(f22,plain,(
% 30.43/4.18    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 30.43/4.18    inference(cnf_transformation,[],[f16])).
% 30.43/4.18  fof(f16,plain,(
% 30.43/4.18    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 30.43/4.18    inference(rectify,[],[f3])).
% 30.43/4.18  fof(f3,axiom,(
% 30.43/4.18    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 30.43/4.18  fof(f52,plain,(
% 30.43/4.18    spl2_2),
% 30.43/4.18    inference(avatar_split_clause,[],[f23,f50])).
% 30.43/4.18  fof(f23,plain,(
% 30.43/4.18    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 30.43/4.18    inference(cnf_transformation,[],[f2])).
% 30.43/4.18  fof(f2,axiom,(
% 30.43/4.18    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 30.43/4.18  fof(f48,plain,(
% 30.43/4.18    ~spl2_1),
% 30.43/4.18    inference(avatar_split_clause,[],[f36,f46])).
% 30.43/4.18  fof(f36,plain,(
% 30.43/4.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 30.43/4.18    inference(definition_unfolding,[],[f21,f27,f30])).
% 30.43/4.18  fof(f21,plain,(
% 30.43/4.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 30.43/4.18    inference(cnf_transformation,[],[f20])).
% 30.43/4.18  fof(f20,plain,(
% 30.43/4.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 30.43/4.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).
% 30.43/4.18  fof(f19,plain,(
% 30.43/4.18    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 30.43/4.18    introduced(choice_axiom,[])).
% 30.43/4.18  fof(f17,plain,(
% 30.43/4.18    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 30.43/4.18    inference(ennf_transformation,[],[f15])).
% 30.43/4.18  fof(f15,negated_conjecture,(
% 30.43/4.18    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 30.43/4.18    inference(negated_conjecture,[],[f14])).
% 30.43/4.18  fof(f14,conjecture,(
% 30.43/4.18    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 30.43/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 30.43/4.18  % SZS output end Proof for theBenchmark
% 30.43/4.18  % (8930)------------------------------
% 30.43/4.18  % (8930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.43/4.18  % (8930)Termination reason: Refutation
% 30.43/4.18  
% 30.43/4.18  % (8930)Memory used [KB]: 81363
% 30.43/4.18  % (8930)Time elapsed: 3.115 s
% 30.43/4.18  % (8930)------------------------------
% 30.43/4.18  % (8930)------------------------------
% 30.43/4.18  % (8754)Success in time 3.831 s
%------------------------------------------------------------------------------
