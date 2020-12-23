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
% DateTime   : Thu Dec  3 12:32:38 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 264 expanded)
%              Number of leaves         :   39 ( 127 expanded)
%              Depth                    :    8
%              Number of atoms          :  397 ( 666 expanded)
%              Number of equality atoms :   73 ( 158 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3502,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f42,f46,f50,f54,f58,f62,f66,f70,f78,f89,f113,f135,f150,f170,f184,f218,f222,f300,f482,f865,f1266,f1316,f1917,f1991,f2314,f3355,f3396,f3427,f3485])).

fof(f3485,plain,
    ( spl3_2
    | ~ spl3_94
    | ~ spl3_116 ),
    inference(avatar_contradiction_clause,[],[f3484])).

fof(f3484,plain,
    ( $false
    | spl3_2
    | ~ spl3_94
    | ~ spl3_116 ),
    inference(subsumption_resolution,[],[f37,f3444])).

fof(f3444,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_94
    | ~ spl3_116 ),
    inference(superposition,[],[f2313,f3426])).

fof(f3426,plain,
    ( sK0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl3_116 ),
    inference(avatar_component_clause,[],[f3424])).

fof(f3424,plain,
    ( spl3_116
  <=> sK0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).

fof(f2313,plain,
    ( ! [X24,X23,X22] : r1_tarski(k3_xboole_0(X24,k3_xboole_0(X22,X23)),X22)
    | ~ spl3_94 ),
    inference(avatar_component_clause,[],[f2312])).

fof(f2312,plain,
    ( spl3_94
  <=> ! [X22,X23,X24] : r1_tarski(k3_xboole_0(X24,k3_xboole_0(X22,X23)),X22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f3427,plain,
    ( spl3_116
    | ~ spl3_12
    | ~ spl3_62
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f3400,f1989,f1251,f76,f3424])).

fof(f76,plain,
    ( spl3_12
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1251,plain,
    ( spl3_62
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1989,plain,
    ( spl3_80
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f3400,plain,
    ( sK0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl3_12
    | ~ spl3_62
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f1253,f1997])).

fof(f1997,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,X2)
    | ~ spl3_12
    | ~ spl3_80 ),
    inference(superposition,[],[f77,f1990])).

fof(f1990,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f1989])).

fof(f77,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f1253,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f1251])).

fof(f3396,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_41
    | spl3_62
    | ~ spl3_63
    | ~ spl3_76
    | ~ spl3_80
    | ~ spl3_115 ),
    inference(avatar_contradiction_clause,[],[f3395])).

fof(f3395,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_41
    | spl3_62
    | ~ spl3_63
    | ~ spl3_76
    | ~ spl3_80
    | ~ spl3_115 ),
    inference(subsumption_resolution,[],[f217,f3394])).

fof(f3394,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_41
    | spl3_62
    | ~ spl3_63
    | ~ spl3_76
    | ~ spl3_80
    | ~ spl3_115 ),
    inference(forward_demodulation,[],[f3393,f1317])).

fof(f1317,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f1269,f88])).

fof(f88,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_13
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1269,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_24
    | ~ spl3_63 ),
    inference(superposition,[],[f1265,f299])).

fof(f299,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl3_24
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1265,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f1264])).

fof(f1264,plain,
    ( spl3_63
  <=> ! [X0] : k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f3393,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_41
    | spl3_62
    | ~ spl3_76
    | ~ spl3_80
    | ~ spl3_115 ),
    inference(forward_demodulation,[],[f3392,f1923])).

fof(f1923,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X1))
    | ~ spl3_41
    | ~ spl3_76 ),
    inference(unit_resulting_resolution,[],[f1916,f864])).

fof(f864,plain,
    ( ! [X6,X8,X7] :
        ( k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | ~ r1_tarski(k3_xboole_0(X6,X7),X8) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f863])).

fof(f863,plain,
    ( spl3_41
  <=> ! [X7,X8,X6] :
        ( k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | ~ r1_tarski(k3_xboole_0(X6,X7),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f1916,plain,
    ( ! [X4,X5] : r1_tarski(k3_xboole_0(X5,X4),X4)
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f1915])).

fof(f1915,plain,
    ( spl3_76
  <=> ! [X5,X4] : r1_tarski(k3_xboole_0(X5,X4),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f3392,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)))
    | ~ spl3_12
    | ~ spl3_17
    | spl3_62
    | ~ spl3_80
    | ~ spl3_115 ),
    inference(forward_demodulation,[],[f3361,f1997])).

fof(f3361,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0)))
    | ~ spl3_17
    | spl3_62
    | ~ spl3_115 ),
    inference(unit_resulting_resolution,[],[f1252,f169,f3354])).

fof(f3354,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X5,X4)
        | X4 = X5
        | ~ r1_tarski(X4,X5) )
    | ~ spl3_115 ),
    inference(avatar_component_clause,[],[f3353])).

fof(f3353,plain,
    ( spl3_115
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r1_tarski(X5,X4)
        | ~ r1_tarski(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_115])])).

fof(f169,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_17
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1252,plain,
    ( sK0 != k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))
    | spl3_62 ),
    inference(avatar_component_clause,[],[f1251])).

fof(f217,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_20
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f3355,plain,
    ( spl3_115
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f227,f220,f60,f3353])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f220,plain,
    ( spl3_21
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f227,plain,
    ( ! [X4,X5] :
        ( X4 = X5
        | ~ r1_tarski(X5,X4)
        | ~ r1_tarski(X4,X5) )
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(superposition,[],[f221,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f221,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f2314,plain,
    ( spl3_94
    | ~ spl3_17
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f540,f480,f168,f2312])).

fof(f480,plain,
    ( spl3_34
  <=> ! [X9,X11,X10] : k3_xboole_0(X9,k3_xboole_0(X10,X11)) = k3_xboole_0(X11,k3_xboole_0(X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f540,plain,
    ( ! [X24,X23,X22] : r1_tarski(k3_xboole_0(X24,k3_xboole_0(X22,X23)),X22)
    | ~ spl3_17
    | ~ spl3_34 ),
    inference(superposition,[],[f169,f481])).

fof(f481,plain,
    ( ! [X10,X11,X9] : k3_xboole_0(X9,k3_xboole_0(X10,X11)) = k3_xboole_0(X11,k3_xboole_0(X9,X10))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f480])).

fof(f1991,plain,
    ( spl3_80
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f302,f298,f182,f1989])).

fof(f182,plain,
    ( spl3_18
  <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f302,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(superposition,[],[f299,f183])).

fof(f183,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1917,plain,
    ( spl3_76
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f174,f168,f56,f1915])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f174,plain,
    ( ! [X4,X5] : r1_tarski(k3_xboole_0(X5,X4),X4)
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(superposition,[],[f169,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f1316,plain,
    ( ~ spl3_7
    | spl3_15
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_63 ),
    inference(avatar_contradiction_clause,[],[f1315])).

fof(f1315,plain,
    ( $false
    | ~ spl3_7
    | spl3_15
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_63 ),
    inference(subsumption_resolution,[],[f134,f1314])).

fof(f1314,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f1313,f153])).

fof(f153,plain,
    ( ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(superposition,[],[f149,f57])).

fof(f149,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_16
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1313,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_7
    | ~ spl3_18
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f1268,f57])).

fof(f1268,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_18
    | ~ spl3_63 ),
    inference(superposition,[],[f1265,f183])).

fof(f134,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_15
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1266,plain,
    ( spl3_63
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f145,f111,f86,f1264])).

fof(f111,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f145,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(superposition,[],[f112,f88])).

fof(f112,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f865,plain,
    ( spl3_41
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f120,f111,f60,f863])).

fof(f120,plain,
    ( ! [X6,X8,X7] :
        ( k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | ~ r1_tarski(k3_xboole_0(X6,X7),X8) )
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(superposition,[],[f112,f61])).

fof(f482,plain,
    ( spl3_34
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f121,f111,f56,f480])).

fof(f121,plain,
    ( ! [X10,X11,X9] : k3_xboole_0(X9,k3_xboole_0(X10,X11)) = k3_xboole_0(X11,k3_xboole_0(X9,X10))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f112,f57])).

fof(f300,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f80,f60,f52,f298])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f80,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f53,f61])).

fof(f53,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f222,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f60,f56,f220])).

fof(f81,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f61,f57])).

fof(f218,plain,
    ( spl3_20
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f178,f168,f86,f215])).

fof(f178,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(superposition,[],[f169,f88])).

fof(f184,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f91,f64,f48,f182])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f91,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f49,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f49,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f170,plain,
    ( spl3_17
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f108,f76,f52,f168])).

fof(f108,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f53,f77])).

fof(f150,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f90,f64,f44,f148])).

fof(f44,plain,
    ( spl3_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f90,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f45,f65])).

fof(f45,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f135,plain,
    ( ~ spl3_15
    | spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f98,f68,f39,f132])).

fof(f39,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f98,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f41,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f41,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f113,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f28,f111])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f89,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f79,f60,f30,f86])).

fof(f30,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f32,f61])).

fof(f32,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f78,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f24,f76])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f70,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f42,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f39,f35])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f33,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (9223)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (9216)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (9220)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (9221)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (9224)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (9230)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (9219)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (9222)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (9229)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (9225)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (9228)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (9217)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (9226)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (9218)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (9227)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (9232)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (9233)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (9231)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.21/0.65  % (9221)Refutation found. Thanks to Tanya!
% 2.21/0.65  % SZS status Theorem for theBenchmark
% 2.21/0.65  % SZS output start Proof for theBenchmark
% 2.21/0.65  fof(f3502,plain,(
% 2.21/0.65    $false),
% 2.21/0.65    inference(avatar_sat_refutation,[],[f33,f42,f46,f50,f54,f58,f62,f66,f70,f78,f89,f113,f135,f150,f170,f184,f218,f222,f300,f482,f865,f1266,f1316,f1917,f1991,f2314,f3355,f3396,f3427,f3485])).
% 2.21/0.65  fof(f3485,plain,(
% 2.21/0.65    spl3_2 | ~spl3_94 | ~spl3_116),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f3484])).
% 2.21/0.65  fof(f3484,plain,(
% 2.21/0.65    $false | (spl3_2 | ~spl3_94 | ~spl3_116)),
% 2.21/0.65    inference(subsumption_resolution,[],[f37,f3444])).
% 2.21/0.65  fof(f3444,plain,(
% 2.21/0.65    r1_tarski(sK0,sK1) | (~spl3_94 | ~spl3_116)),
% 2.21/0.65    inference(superposition,[],[f2313,f3426])).
% 2.21/0.65  fof(f3426,plain,(
% 2.21/0.65    sK0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) | ~spl3_116),
% 2.21/0.65    inference(avatar_component_clause,[],[f3424])).
% 2.21/0.65  fof(f3424,plain,(
% 2.21/0.65    spl3_116 <=> sK0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).
% 2.21/0.65  fof(f2313,plain,(
% 2.21/0.65    ( ! [X24,X23,X22] : (r1_tarski(k3_xboole_0(X24,k3_xboole_0(X22,X23)),X22)) ) | ~spl3_94),
% 2.21/0.65    inference(avatar_component_clause,[],[f2312])).
% 2.21/0.65  fof(f2312,plain,(
% 2.21/0.65    spl3_94 <=> ! [X22,X23,X24] : r1_tarski(k3_xboole_0(X24,k3_xboole_0(X22,X23)),X22)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 2.21/0.65  fof(f37,plain,(
% 2.21/0.65    ~r1_tarski(sK0,sK1) | spl3_2),
% 2.21/0.65    inference(avatar_component_clause,[],[f35])).
% 2.21/0.65  fof(f35,plain,(
% 2.21/0.65    spl3_2 <=> r1_tarski(sK0,sK1)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.21/0.65  fof(f3427,plain,(
% 2.21/0.65    spl3_116 | ~spl3_12 | ~spl3_62 | ~spl3_80),
% 2.21/0.65    inference(avatar_split_clause,[],[f3400,f1989,f1251,f76,f3424])).
% 2.21/0.65  fof(f76,plain,(
% 2.21/0.65    spl3_12 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.21/0.65  fof(f1251,plain,(
% 2.21/0.65    spl3_62 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 2.21/0.65  fof(f1989,plain,(
% 2.21/0.65    spl3_80 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 2.21/0.65  fof(f3400,plain,(
% 2.21/0.65    sK0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) | (~spl3_12 | ~spl3_62 | ~spl3_80)),
% 2.21/0.65    inference(forward_demodulation,[],[f1253,f1997])).
% 2.21/0.65  fof(f1997,plain,(
% 2.21/0.65    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,X2)) ) | (~spl3_12 | ~spl3_80)),
% 2.21/0.65    inference(superposition,[],[f77,f1990])).
% 2.21/0.65  fof(f1990,plain,(
% 2.21/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_80),
% 2.21/0.65    inference(avatar_component_clause,[],[f1989])).
% 2.21/0.65  fof(f77,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_12),
% 2.21/0.65    inference(avatar_component_clause,[],[f76])).
% 2.21/0.65  fof(f1253,plain,(
% 2.21/0.65    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0)) | ~spl3_62),
% 2.21/0.65    inference(avatar_component_clause,[],[f1251])).
% 2.21/0.65  fof(f3396,plain,(
% 2.21/0.65    ~spl3_12 | ~spl3_13 | ~spl3_17 | ~spl3_20 | ~spl3_24 | ~spl3_41 | spl3_62 | ~spl3_63 | ~spl3_76 | ~spl3_80 | ~spl3_115),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f3395])).
% 2.21/0.65  fof(f3395,plain,(
% 2.21/0.65    $false | (~spl3_12 | ~spl3_13 | ~spl3_17 | ~spl3_20 | ~spl3_24 | ~spl3_41 | spl3_62 | ~spl3_63 | ~spl3_76 | ~spl3_80 | ~spl3_115)),
% 2.21/0.65    inference(subsumption_resolution,[],[f217,f3394])).
% 2.21/0.65  fof(f3394,plain,(
% 2.21/0.65    ~r1_tarski(sK0,sK0) | (~spl3_12 | ~spl3_13 | ~spl3_17 | ~spl3_24 | ~spl3_41 | spl3_62 | ~spl3_63 | ~spl3_76 | ~spl3_80 | ~spl3_115)),
% 2.21/0.65    inference(forward_demodulation,[],[f3393,f1317])).
% 2.21/0.65  fof(f1317,plain,(
% 2.21/0.65    sK0 = k3_xboole_0(sK0,sK1) | (~spl3_13 | ~spl3_24 | ~spl3_63)),
% 2.21/0.65    inference(forward_demodulation,[],[f1269,f88])).
% 2.21/0.65  fof(f88,plain,(
% 2.21/0.65    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_13),
% 2.21/0.65    inference(avatar_component_clause,[],[f86])).
% 2.21/0.65  fof(f86,plain,(
% 2.21/0.65    spl3_13 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.21/0.65  fof(f1269,plain,(
% 2.21/0.65    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1) | (~spl3_24 | ~spl3_63)),
% 2.21/0.65    inference(superposition,[],[f1265,f299])).
% 2.21/0.65  fof(f299,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_24),
% 2.21/0.65    inference(avatar_component_clause,[],[f298])).
% 2.21/0.65  fof(f298,plain,(
% 2.21/0.65    spl3_24 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.21/0.65  fof(f1265,plain,(
% 2.21/0.65    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK0,X0)) ) | ~spl3_63),
% 2.21/0.65    inference(avatar_component_clause,[],[f1264])).
% 2.21/0.65  fof(f1264,plain,(
% 2.21/0.65    spl3_63 <=> ! [X0] : k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK0,X0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 2.21/0.65  fof(f3393,plain,(
% 2.21/0.65    ~r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_12 | ~spl3_17 | ~spl3_41 | spl3_62 | ~spl3_76 | ~spl3_80 | ~spl3_115)),
% 2.21/0.65    inference(forward_demodulation,[],[f3392,f1923])).
% 2.21/0.65  fof(f1923,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X1))) ) | (~spl3_41 | ~spl3_76)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f1916,f864])).
% 2.21/0.65  fof(f864,plain,(
% 2.21/0.65    ( ! [X6,X8,X7] : (k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X7,X8)) | ~r1_tarski(k3_xboole_0(X6,X7),X8)) ) | ~spl3_41),
% 2.21/0.65    inference(avatar_component_clause,[],[f863])).
% 2.21/0.65  fof(f863,plain,(
% 2.21/0.65    spl3_41 <=> ! [X7,X8,X6] : (k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X7,X8)) | ~r1_tarski(k3_xboole_0(X6,X7),X8))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 2.21/0.65  fof(f1916,plain,(
% 2.21/0.65    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X5,X4),X4)) ) | ~spl3_76),
% 2.21/0.65    inference(avatar_component_clause,[],[f1915])).
% 2.21/0.65  fof(f1915,plain,(
% 2.21/0.65    spl3_76 <=> ! [X5,X4] : r1_tarski(k3_xboole_0(X5,X4),X4)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 2.21/0.65  fof(f3392,plain,(
% 2.21/0.65    ~r1_tarski(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))) | (~spl3_12 | ~spl3_17 | spl3_62 | ~spl3_80 | ~spl3_115)),
% 2.21/0.65    inference(forward_demodulation,[],[f3361,f1997])).
% 2.21/0.65  fof(f3361,plain,(
% 2.21/0.65    ~r1_tarski(sK0,k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))) | (~spl3_17 | spl3_62 | ~spl3_115)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f1252,f169,f3354])).
% 2.21/0.65  fof(f3354,plain,(
% 2.21/0.65    ( ! [X4,X5] : (~r1_tarski(X5,X4) | X4 = X5 | ~r1_tarski(X4,X5)) ) | ~spl3_115),
% 2.21/0.65    inference(avatar_component_clause,[],[f3353])).
% 2.21/0.65  fof(f3353,plain,(
% 2.21/0.65    spl3_115 <=> ! [X5,X4] : (X4 = X5 | ~r1_tarski(X5,X4) | ~r1_tarski(X4,X5))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_115])])).
% 2.21/0.65  fof(f169,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_17),
% 2.21/0.65    inference(avatar_component_clause,[],[f168])).
% 2.21/0.65  fof(f168,plain,(
% 2.21/0.65    spl3_17 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.21/0.65  fof(f1252,plain,(
% 2.21/0.65    sK0 != k3_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0)) | spl3_62),
% 2.21/0.65    inference(avatar_component_clause,[],[f1251])).
% 2.21/0.65  fof(f217,plain,(
% 2.21/0.65    r1_tarski(sK0,sK0) | ~spl3_20),
% 2.21/0.65    inference(avatar_component_clause,[],[f215])).
% 2.21/0.65  fof(f215,plain,(
% 2.21/0.65    spl3_20 <=> r1_tarski(sK0,sK0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.21/0.65  fof(f3355,plain,(
% 2.21/0.65    spl3_115 | ~spl3_8 | ~spl3_21),
% 2.21/0.65    inference(avatar_split_clause,[],[f227,f220,f60,f3353])).
% 2.21/0.65  fof(f60,plain,(
% 2.21/0.65    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.21/0.65  fof(f220,plain,(
% 2.21/0.65    spl3_21 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.21/0.65  fof(f227,plain,(
% 2.21/0.65    ( ! [X4,X5] : (X4 = X5 | ~r1_tarski(X5,X4) | ~r1_tarski(X4,X5)) ) | (~spl3_8 | ~spl3_21)),
% 2.21/0.65    inference(superposition,[],[f221,f61])).
% 2.21/0.65  fof(f61,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 2.21/0.65    inference(avatar_component_clause,[],[f60])).
% 2.21/0.65  fof(f221,plain,(
% 2.21/0.65    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl3_21),
% 2.21/0.65    inference(avatar_component_clause,[],[f220])).
% 2.21/0.65  fof(f2314,plain,(
% 2.21/0.65    spl3_94 | ~spl3_17 | ~spl3_34),
% 2.21/0.65    inference(avatar_split_clause,[],[f540,f480,f168,f2312])).
% 2.21/0.65  fof(f480,plain,(
% 2.21/0.65    spl3_34 <=> ! [X9,X11,X10] : k3_xboole_0(X9,k3_xboole_0(X10,X11)) = k3_xboole_0(X11,k3_xboole_0(X9,X10))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.21/0.65  fof(f540,plain,(
% 2.21/0.65    ( ! [X24,X23,X22] : (r1_tarski(k3_xboole_0(X24,k3_xboole_0(X22,X23)),X22)) ) | (~spl3_17 | ~spl3_34)),
% 2.21/0.65    inference(superposition,[],[f169,f481])).
% 2.21/0.65  fof(f481,plain,(
% 2.21/0.65    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k3_xboole_0(X10,X11)) = k3_xboole_0(X11,k3_xboole_0(X9,X10))) ) | ~spl3_34),
% 2.21/0.65    inference(avatar_component_clause,[],[f480])).
% 2.21/0.65  fof(f1991,plain,(
% 2.21/0.65    spl3_80 | ~spl3_18 | ~spl3_24),
% 2.21/0.65    inference(avatar_split_clause,[],[f302,f298,f182,f1989])).
% 2.21/0.65  fof(f182,plain,(
% 2.21/0.65    spl3_18 <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.21/0.65  fof(f302,plain,(
% 2.21/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_18 | ~spl3_24)),
% 2.21/0.65    inference(superposition,[],[f299,f183])).
% 2.21/0.65  fof(f183,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_18),
% 2.21/0.65    inference(avatar_component_clause,[],[f182])).
% 2.21/0.65  fof(f1917,plain,(
% 2.21/0.65    spl3_76 | ~spl3_7 | ~spl3_17),
% 2.21/0.65    inference(avatar_split_clause,[],[f174,f168,f56,f1915])).
% 2.21/0.65  fof(f56,plain,(
% 2.21/0.65    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.21/0.65  fof(f174,plain,(
% 2.21/0.65    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X5,X4),X4)) ) | (~spl3_7 | ~spl3_17)),
% 2.21/0.65    inference(superposition,[],[f169,f57])).
% 2.21/0.65  fof(f57,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_7),
% 2.21/0.65    inference(avatar_component_clause,[],[f56])).
% 2.21/0.65  fof(f1316,plain,(
% 2.21/0.65    ~spl3_7 | spl3_15 | ~spl3_16 | ~spl3_18 | ~spl3_63),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f1315])).
% 2.21/0.65  fof(f1315,plain,(
% 2.21/0.65    $false | (~spl3_7 | spl3_15 | ~spl3_16 | ~spl3_18 | ~spl3_63)),
% 2.21/0.65    inference(subsumption_resolution,[],[f134,f1314])).
% 2.21/0.65  fof(f1314,plain,(
% 2.21/0.65    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_7 | ~spl3_16 | ~spl3_18 | ~spl3_63)),
% 2.21/0.65    inference(forward_demodulation,[],[f1313,f153])).
% 2.21/0.65  fof(f153,plain,(
% 2.21/0.65    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) ) | (~spl3_7 | ~spl3_16)),
% 2.21/0.65    inference(superposition,[],[f149,f57])).
% 2.21/0.65  fof(f149,plain,(
% 2.21/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_16),
% 2.21/0.65    inference(avatar_component_clause,[],[f148])).
% 2.21/0.65  fof(f148,plain,(
% 2.21/0.65    spl3_16 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.21/0.65  fof(f1313,plain,(
% 2.21/0.65    k3_xboole_0(sK0,sK2) = k3_xboole_0(k1_xboole_0,sK0) | (~spl3_7 | ~spl3_18 | ~spl3_63)),
% 2.21/0.65    inference(forward_demodulation,[],[f1268,f57])).
% 2.21/0.65  fof(f1268,plain,(
% 2.21/0.65    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_xboole_0) | (~spl3_18 | ~spl3_63)),
% 2.21/0.65    inference(superposition,[],[f1265,f183])).
% 2.21/0.65  fof(f134,plain,(
% 2.21/0.65    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_15),
% 2.21/0.65    inference(avatar_component_clause,[],[f132])).
% 2.21/0.65  fof(f132,plain,(
% 2.21/0.65    spl3_15 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.21/0.65  fof(f1266,plain,(
% 2.21/0.65    spl3_63 | ~spl3_13 | ~spl3_14),
% 2.21/0.65    inference(avatar_split_clause,[],[f145,f111,f86,f1264])).
% 2.21/0.65  fof(f111,plain,(
% 2.21/0.65    spl3_14 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.21/0.65  fof(f145,plain,(
% 2.21/0.65    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK0,X0)) ) | (~spl3_13 | ~spl3_14)),
% 2.21/0.65    inference(superposition,[],[f112,f88])).
% 2.21/0.65  fof(f112,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl3_14),
% 2.21/0.65    inference(avatar_component_clause,[],[f111])).
% 2.21/0.65  fof(f865,plain,(
% 2.21/0.65    spl3_41 | ~spl3_8 | ~spl3_14),
% 2.21/0.65    inference(avatar_split_clause,[],[f120,f111,f60,f863])).
% 2.21/0.65  fof(f120,plain,(
% 2.21/0.65    ( ! [X6,X8,X7] : (k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X7,X8)) | ~r1_tarski(k3_xboole_0(X6,X7),X8)) ) | (~spl3_8 | ~spl3_14)),
% 2.21/0.65    inference(superposition,[],[f112,f61])).
% 2.21/0.65  fof(f482,plain,(
% 2.21/0.65    spl3_34 | ~spl3_7 | ~spl3_14),
% 2.21/0.65    inference(avatar_split_clause,[],[f121,f111,f56,f480])).
% 2.21/0.65  fof(f121,plain,(
% 2.21/0.65    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k3_xboole_0(X10,X11)) = k3_xboole_0(X11,k3_xboole_0(X9,X10))) ) | (~spl3_7 | ~spl3_14)),
% 2.21/0.65    inference(superposition,[],[f112,f57])).
% 2.21/0.65  fof(f300,plain,(
% 2.21/0.65    spl3_24 | ~spl3_6 | ~spl3_8),
% 2.21/0.65    inference(avatar_split_clause,[],[f80,f60,f52,f298])).
% 2.21/0.65  fof(f52,plain,(
% 2.21/0.65    spl3_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.21/0.65  fof(f80,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_6 | ~spl3_8)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f53,f61])).
% 2.21/0.65  fof(f53,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 2.21/0.65    inference(avatar_component_clause,[],[f52])).
% 2.21/0.65  fof(f222,plain,(
% 2.21/0.65    spl3_21 | ~spl3_7 | ~spl3_8),
% 2.21/0.65    inference(avatar_split_clause,[],[f81,f60,f56,f220])).
% 2.21/0.65  fof(f81,plain,(
% 2.21/0.65    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl3_7 | ~spl3_8)),
% 2.21/0.65    inference(superposition,[],[f61,f57])).
% 2.21/0.65  fof(f218,plain,(
% 2.21/0.65    spl3_20 | ~spl3_13 | ~spl3_17),
% 2.21/0.65    inference(avatar_split_clause,[],[f178,f168,f86,f215])).
% 2.21/0.65  fof(f178,plain,(
% 2.21/0.65    r1_tarski(sK0,sK0) | (~spl3_13 | ~spl3_17)),
% 2.21/0.65    inference(superposition,[],[f169,f88])).
% 2.21/0.65  fof(f184,plain,(
% 2.21/0.65    spl3_18 | ~spl3_5 | ~spl3_9),
% 2.21/0.65    inference(avatar_split_clause,[],[f91,f64,f48,f182])).
% 2.21/0.65  fof(f48,plain,(
% 2.21/0.65    spl3_5 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.21/0.65  fof(f64,plain,(
% 2.21/0.65    spl3_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.21/0.65  fof(f91,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) ) | (~spl3_5 | ~spl3_9)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f49,f65])).
% 2.21/0.65  fof(f65,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 2.21/0.65    inference(avatar_component_clause,[],[f64])).
% 2.21/0.65  fof(f49,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_5),
% 2.21/0.65    inference(avatar_component_clause,[],[f48])).
% 2.21/0.65  fof(f170,plain,(
% 2.21/0.65    spl3_17 | ~spl3_6 | ~spl3_12),
% 2.21/0.65    inference(avatar_split_clause,[],[f108,f76,f52,f168])).
% 2.21/0.65  fof(f108,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | (~spl3_6 | ~spl3_12)),
% 2.21/0.65    inference(superposition,[],[f53,f77])).
% 2.21/0.65  fof(f150,plain,(
% 2.21/0.65    spl3_16 | ~spl3_4 | ~spl3_9),
% 2.21/0.65    inference(avatar_split_clause,[],[f90,f64,f44,f148])).
% 2.21/0.65  fof(f44,plain,(
% 2.21/0.65    spl3_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.21/0.65  fof(f90,plain,(
% 2.21/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_9)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f45,f65])).
% 2.21/0.65  fof(f45,plain,(
% 2.21/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 2.21/0.65    inference(avatar_component_clause,[],[f44])).
% 2.21/0.65  fof(f135,plain,(
% 2.21/0.65    ~spl3_15 | spl3_3 | ~spl3_10),
% 2.21/0.65    inference(avatar_split_clause,[],[f98,f68,f39,f132])).
% 2.21/0.65  fof(f39,plain,(
% 2.21/0.65    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.21/0.65  fof(f68,plain,(
% 2.21/0.65    spl3_10 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.21/0.65  fof(f98,plain,(
% 2.21/0.65    k1_xboole_0 != k3_xboole_0(sK0,sK2) | (spl3_3 | ~spl3_10)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f41,f69])).
% 2.21/0.65  fof(f69,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_10),
% 2.21/0.65    inference(avatar_component_clause,[],[f68])).
% 2.21/0.65  fof(f41,plain,(
% 2.21/0.65    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 2.21/0.65    inference(avatar_component_clause,[],[f39])).
% 2.21/0.65  fof(f113,plain,(
% 2.21/0.65    spl3_14),
% 2.21/0.65    inference(avatar_split_clause,[],[f28,f111])).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f4])).
% 2.21/0.65  fof(f4,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.21/0.65  fof(f89,plain,(
% 2.21/0.65    spl3_13 | ~spl3_1 | ~spl3_8),
% 2.21/0.65    inference(avatar_split_clause,[],[f79,f60,f30,f86])).
% 2.21/0.65  fof(f30,plain,(
% 2.21/0.65    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.21/0.65  fof(f79,plain,(
% 2.21/0.65    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_8)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f32,f61])).
% 2.21/0.65  fof(f32,plain,(
% 2.21/0.65    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.21/0.65    inference(avatar_component_clause,[],[f30])).
% 2.21/0.65  fof(f78,plain,(
% 2.21/0.65    spl3_12),
% 2.21/0.65    inference(avatar_split_clause,[],[f24,f76])).
% 2.21/0.65  fof(f24,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f7])).
% 2.21/0.65  fof(f7,axiom,(
% 2.21/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.21/0.65  fof(f70,plain,(
% 2.21/0.65    spl3_10),
% 2.21/0.65    inference(avatar_split_clause,[],[f27,f68])).
% 2.21/0.65  fof(f27,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.21/0.65    inference(cnf_transformation,[],[f16])).
% 2.21/0.65  fof(f16,plain,(
% 2.21/0.65    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.21/0.65    inference(nnf_transformation,[],[f2])).
% 2.21/0.65  fof(f2,axiom,(
% 2.21/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.21/0.65  fof(f66,plain,(
% 2.21/0.65    spl3_9),
% 2.21/0.65    inference(avatar_split_clause,[],[f26,f64])).
% 2.21/0.65  fof(f26,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f16])).
% 2.21/0.65  fof(f62,plain,(
% 2.21/0.65    spl3_8),
% 2.21/0.65    inference(avatar_split_clause,[],[f25,f60])).
% 2.21/0.65  fof(f25,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f13])).
% 2.21/0.65  fof(f13,plain,(
% 2.21/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f5])).
% 2.21/0.65  fof(f5,axiom,(
% 2.21/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.21/0.65  fof(f58,plain,(
% 2.21/0.65    spl3_7),
% 2.21/0.65    inference(avatar_split_clause,[],[f22,f56])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f1])).
% 2.21/0.65  fof(f1,axiom,(
% 2.21/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.21/0.65  fof(f54,plain,(
% 2.21/0.65    spl3_6),
% 2.21/0.65    inference(avatar_split_clause,[],[f21,f52])).
% 2.21/0.65  fof(f21,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f6])).
% 2.21/0.65  fof(f6,axiom,(
% 2.21/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.21/0.65  fof(f50,plain,(
% 2.21/0.65    spl3_5),
% 2.21/0.65    inference(avatar_split_clause,[],[f20,f48])).
% 2.21/0.65  fof(f20,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f9])).
% 2.21/0.65  fof(f9,axiom,(
% 2.21/0.65    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.21/0.65  fof(f46,plain,(
% 2.21/0.65    spl3_4),
% 2.21/0.65    inference(avatar_split_clause,[],[f19,f44])).
% 2.21/0.65  fof(f19,plain,(
% 2.21/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f8])).
% 2.21/0.65  fof(f8,axiom,(
% 2.21/0.65    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.21/0.65  fof(f42,plain,(
% 2.21/0.65    ~spl3_2 | ~spl3_3),
% 2.21/0.65    inference(avatar_split_clause,[],[f18,f39,f35])).
% 2.21/0.65  fof(f18,plain,(
% 2.21/0.65    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 2.21/0.65    inference(cnf_transformation,[],[f15])).
% 2.21/0.65  fof(f15,plain,(
% 2.21/0.65    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 2.21/0.65  fof(f14,plain,(
% 2.21/0.65    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f12,plain,(
% 2.21/0.65    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.21/0.65    inference(ennf_transformation,[],[f11])).
% 2.21/0.65  fof(f11,negated_conjecture,(
% 2.21/0.65    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.21/0.65    inference(negated_conjecture,[],[f10])).
% 2.21/0.65  fof(f10,conjecture,(
% 2.21/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.21/0.65  fof(f33,plain,(
% 2.21/0.65    spl3_1),
% 2.21/0.65    inference(avatar_split_clause,[],[f17,f30])).
% 2.21/0.65  fof(f17,plain,(
% 2.21/0.65    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.21/0.65    inference(cnf_transformation,[],[f15])).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (9221)------------------------------
% 2.21/0.65  % (9221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (9221)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (9221)Memory used [KB]: 8699
% 2.21/0.65  % (9221)Time elapsed: 0.236 s
% 2.21/0.65  % (9221)------------------------------
% 2.21/0.65  % (9221)------------------------------
% 2.21/0.65  % (9215)Success in time 0.294 s
%------------------------------------------------------------------------------
