%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:46 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 545 expanded)
%              Number of leaves         :   64 ( 267 expanded)
%              Depth                    :    9
%              Number of atoms          :  766 (1429 expanded)
%              Number of equality atoms :  161 ( 384 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12932,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f69,f73,f77,f81,f86,f90,f94,f101,f109,f118,f126,f130,f134,f138,f143,f214,f218,f249,f307,f332,f338,f372,f505,f543,f548,f701,f801,f895,f970,f1045,f1197,f1202,f1551,f1766,f1771,f1848,f1990,f2126,f2127,f2388,f2400,f2683,f3838,f8757,f9858,f12580,f12607,f12866,f12920,f12931])).

fof(f12931,plain,
    ( ~ spl3_12
    | ~ spl3_46
    | spl3_277 ),
    inference(avatar_contradiction_clause,[],[f12926])).

fof(f12926,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_46
    | spl3_277 ),
    inference(unit_resulting_resolution,[],[f547,f12919,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f12919,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_277 ),
    inference(avatar_component_clause,[],[f12917])).

fof(f12917,plain,
    ( spl3_277
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_277])])).

fof(f547,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl3_46
  <=> ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f12920,plain,
    ( ~ spl3_277
    | ~ spl3_94
    | spl3_113
    | ~ spl3_114
    | ~ spl3_124 ),
    inference(avatar_split_clause,[],[f12779,f2681,f2397,f2385,f1769,f12917])).

fof(f1769,plain,
    ( spl3_94
  <=> ! [X5,X4] : k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f2385,plain,
    ( spl3_113
  <=> r1_tarski(sK0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).

fof(f2397,plain,
    ( spl3_114
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f2681,plain,
    ( spl3_124
  <=> ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).

fof(f12779,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_94
    | spl3_113
    | ~ spl3_114
    | ~ spl3_124 ),
    inference(forward_demodulation,[],[f2387,f2731])).

fof(f2731,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_94
    | ~ spl3_114
    | ~ spl3_124 ),
    inference(forward_demodulation,[],[f2694,f2399])).

fof(f2399,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_114 ),
    inference(avatar_component_clause,[],[f2397])).

fof(f2694,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_94
    | ~ spl3_124 ),
    inference(superposition,[],[f2682,f1770])).

fof(f1770,plain,
    ( ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))
    | ~ spl3_94 ),
    inference(avatar_component_clause,[],[f1769])).

fof(f2682,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_124 ),
    inference(avatar_component_clause,[],[f2681])).

fof(f2387,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_113 ),
    inference(avatar_component_clause,[],[f2385])).

fof(f12866,plain,
    ( spl3_1
    | ~ spl3_12
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f315,f304,f107,f51])).

fof(f51,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f304,plain,
    ( spl3_28
  <=> k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f315,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_12
    | ~ spl3_28 ),
    inference(trivial_inequality_removal,[],[f310])).

fof(f310,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_12
    | ~ spl3_28 ),
    inference(superposition,[],[f108,f306])).

fof(f306,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f304])).

fof(f12607,plain,
    ( ~ spl3_2
    | ~ spl3_59
    | ~ spl3_94
    | spl3_114
    | ~ spl3_124 ),
    inference(avatar_contradiction_clause,[],[f12606])).

fof(f12606,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_59
    | ~ spl3_94
    | spl3_114
    | ~ spl3_124 ),
    inference(subsumption_resolution,[],[f12605,f2398])).

fof(f2398,plain,
    ( sK0 != k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | spl3_114 ),
    inference(avatar_component_clause,[],[f2397])).

fof(f12605,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_59
    | ~ spl3_94
    | ~ spl3_124 ),
    inference(forward_demodulation,[],[f2694,f2111])).

fof(f2111,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_59 ),
    inference(unit_resulting_resolution,[],[f57,f800])).

fof(f800,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f799])).

fof(f799,plain,
    ( spl3_59
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f57,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f12580,plain,
    ( spl3_28
    | ~ spl3_114
    | ~ spl3_234
    | ~ spl3_248 ),
    inference(avatar_contradiction_clause,[],[f12579])).

fof(f12579,plain,
    ( $false
    | spl3_28
    | ~ spl3_114
    | ~ spl3_234
    | ~ spl3_248 ),
    inference(subsumption_resolution,[],[f9971,f305])).

fof(f305,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f304])).

fof(f9971,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_114
    | ~ spl3_234
    | ~ spl3_248 ),
    inference(forward_demodulation,[],[f9889,f8756])).

fof(f8756,plain,
    ( ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5)
    | ~ spl3_234 ),
    inference(avatar_component_clause,[],[f8755])).

fof(f8755,plain,
    ( spl3_234
  <=> ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_234])])).

fof(f9889,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)
    | ~ spl3_114
    | ~ spl3_248 ),
    inference(superposition,[],[f9857,f2399])).

fof(f9857,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7)
    | ~ spl3_248 ),
    inference(avatar_component_clause,[],[f9856])).

fof(f9856,plain,
    ( spl3_248
  <=> ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_248])])).

fof(f9858,plain,
    ( spl3_248
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_22
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f1230,f1200,f212,f132,f128,f9856])).

fof(f128,plain,
    ( spl3_16
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f132,plain,
    ( spl3_17
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f212,plain,
    ( spl3_22
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1200,plain,
    ( spl3_72
  <=> ! [X3,X2] : k5_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f1230,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7)
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_22
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f1207,f231])).

fof(f231,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X2))
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f220,f129])).

fof(f129,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f220,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X2))
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(superposition,[],[f213,f133])).

fof(f133,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f213,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f1207,plain,
    ( ! [X8,X7] : k5_xboole_0(k3_xboole_0(X7,X8),X7) = k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k3_xboole_0(X7,X8),X7))
    | ~ spl3_17
    | ~ spl3_72 ),
    inference(superposition,[],[f1201,f133])).

fof(f1201,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f8757,plain,
    ( spl3_234
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_32
    | ~ spl3_46
    | ~ spl3_65
    | ~ spl3_84
    | ~ spl3_159 ),
    inference(avatar_split_clause,[],[f3839,f3836,f1549,f968,f546,f370,f136,f71,f8755])).

fof(f71,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f136,plain,
    ( spl3_18
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f370,plain,
    ( spl3_32
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f968,plain,
    ( spl3_65
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1549,plain,
    ( spl3_84
  <=> ! [X1,X0] : k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f3836,plain,
    ( spl3_159
  <=> ! [X5] : k5_xboole_0(X5,X5) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_159])])).

fof(f3839,plain,
    ( ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5)
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_32
    | ~ spl3_46
    | ~ spl3_65
    | ~ spl3_84
    | ~ spl3_159 ),
    inference(forward_demodulation,[],[f3837,f1602])).

fof(f1602,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_32
    | ~ spl3_46
    | ~ spl3_65
    | ~ spl3_84 ),
    inference(forward_demodulation,[],[f1601,f563])).

fof(f563,plain,
    ( ! [X4] : k3_xboole_0(X4,X4) = X4
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f554,f72])).

fof(f72,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f554,plain,
    ( ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k3_xboole_0(X4,X4)
    | ~ spl3_18
    | ~ spl3_46 ),
    inference(superposition,[],[f137,f547])).

fof(f137,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1601,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = k2_xboole_0(X0,k3_xboole_0(X0,X0))
    | ~ spl3_4
    | ~ spl3_32
    | ~ spl3_46
    | ~ spl3_65
    | ~ spl3_84 ),
    inference(forward_demodulation,[],[f1562,f1015])).

fof(f1015,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4
    | ~ spl3_32
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f971,f72])).

fof(f971,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)
    | ~ spl3_32
    | ~ spl3_65 ),
    inference(unit_resulting_resolution,[],[f371,f969])).

fof(f969,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f968])).

fof(f371,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1562,plain,
    ( ! [X0] : k2_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)
    | ~ spl3_46
    | ~ spl3_84 ),
    inference(superposition,[],[f1550,f547])).

fof(f1550,plain,
    ( ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_84 ),
    inference(avatar_component_clause,[],[f1549])).

fof(f3837,plain,
    ( ! [X5] : k5_xboole_0(X5,X5) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_159 ),
    inference(avatar_component_clause,[],[f3836])).

fof(f3838,plain,
    ( spl3_159
    | ~ spl3_22
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f555,f546,f212,f3836])).

fof(f555,plain,
    ( ! [X5] : k5_xboole_0(X5,X5) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_22
    | ~ spl3_46 ),
    inference(superposition,[],[f213,f547])).

fof(f2683,plain,
    ( spl3_124
    | ~ spl3_3
    | ~ spl3_99 ),
    inference(avatar_split_clause,[],[f2000,f1988,f63,f2681])).

fof(f63,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1988,plain,
    ( spl3_99
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f2000,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3
    | ~ spl3_99 ),
    inference(unit_resulting_resolution,[],[f65,f1989])).

fof(f1989,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f1988])).

fof(f65,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f2400,plain,
    ( spl3_114
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f317,f304,f136,f71,f2397])).

fof(f317,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f312,f72])).

fof(f312,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_18
    | ~ spl3_28 ),
    inference(superposition,[],[f137,f306])).

fof(f2388,plain,
    ( ~ spl3_113
    | spl3_26
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f1046,f1043,f290,f2385])).

fof(f290,plain,
    ( spl3_26
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1043,plain,
    ( spl3_66
  <=> ! [X3,X2] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | ~ r1_tarski(X2,k3_xboole_0(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f1046,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_26
    | ~ spl3_66 ),
    inference(unit_resulting_resolution,[],[f291,f1044])).

fof(f1044,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,k3_xboole_0(X2,X3))
        | k1_xboole_0 = k4_xboole_0(X2,X3) )
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f291,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f290])).

fof(f2127,plain,
    ( ~ spl3_26
    | spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f294,f107,f55,f290])).

fof(f294,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f56,f108])).

fof(f56,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f2126,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f31,f63,f55,f51])).

fof(f31,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f1990,plain,
    ( spl3_99
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_32
    | ~ spl3_42
    | ~ spl3_46
    | ~ spl3_55
    | ~ spl3_62
    | ~ spl3_71
    | ~ spl3_72
    | ~ spl3_96 ),
    inference(avatar_split_clause,[],[f1849,f1846,f1200,f1195,f893,f699,f546,f503,f370,f212,f136,f128,f99,f1988])).

fof(f99,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f503,plain,
    ( spl3_42
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f699,plain,
    ( spl3_55
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f893,plain,
    ( spl3_62
  <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1195,plain,
    ( spl3_71
  <=> ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) = k2_xboole_0(k1_xboole_0,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f1846,plain,
    ( spl3_96
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f1849,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_32
    | ~ spl3_42
    | ~ spl3_46
    | ~ spl3_55
    | ~ spl3_62
    | ~ spl3_71
    | ~ spl3_72
    | ~ spl3_96 ),
    inference(forward_demodulation,[],[f1847,f1247])).

fof(f1247,plain,
    ( ! [X12,X11] : k3_xboole_0(X11,X12) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X11,X12))
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_32
    | ~ spl3_42
    | ~ spl3_46
    | ~ spl3_55
    | ~ spl3_62
    | ~ spl3_71
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f1246,f926])).

fof(f926,plain,
    ( ! [X10,X11] : k3_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X10,X11))
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f910,f137])).

fof(f910,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k5_xboole_0(X10,k4_xboole_0(X10,X11))
    | ~ spl3_16
    | ~ spl3_62 ),
    inference(superposition,[],[f129,f894])).

fof(f894,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f893])).

fof(f1246,plain,
    ( ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X11,X12))
    | ~ spl3_10
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_32
    | ~ spl3_42
    | ~ spl3_46
    | ~ spl3_55
    | ~ spl3_62
    | ~ spl3_71
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f1245,f1198])).

fof(f1198,plain,
    ( ! [X6] : k2_xboole_0(k1_xboole_0,X6) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X6)
    | ~ spl3_10
    | ~ spl3_32
    | ~ spl3_42
    | ~ spl3_55
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f1196,f716])).

fof(f716,plain,
    ( ! [X3] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl3_10
    | ~ spl3_32
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f709,f374])).

fof(f374,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f371,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f709,plain,
    ( ! [X3] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(superposition,[],[f700,f504])).

fof(f504,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f503])).

fof(f700,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f699])).

fof(f1196,plain,
    ( ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) = k2_xboole_0(k1_xboole_0,X6)
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f1195])).

fof(f1245,plain,
    ( ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X11,X12))
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_46
    | ~ spl3_55
    | ~ spl3_62
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f1218,f932])).

fof(f932,plain,
    ( ! [X37,X36] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X36,X37),X36)
    | ~ spl3_22
    | ~ spl3_46
    | ~ spl3_55
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f921,f555])).

fof(f921,plain,
    ( ! [X37,X36] : k4_xboole_0(k4_xboole_0(X36,X37),X36) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,X37))
    | ~ spl3_55
    | ~ spl3_62 ),
    inference(superposition,[],[f700,f894])).

fof(f1218,plain,
    ( ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X11),k3_xboole_0(X11,X12))
    | ~ spl3_18
    | ~ spl3_72 ),
    inference(superposition,[],[f1201,f137])).

fof(f1847,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f1846])).

fof(f1848,plain,
    ( spl3_96
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f260,f247,f99,f84,f1846])).

fof(f84,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f247,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f260,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f253,f85])).

fof(f85,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f248,f100])).

fof(f248,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f247])).

fof(f1771,plain,
    ( spl3_94
    | ~ spl3_4
    | ~ spl3_32
    | ~ spl3_65
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1767,f1764,f968,f370,f71,f1769])).

fof(f1764,plain,
    ( spl3_93
  <=> ! [X5,X4] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f1767,plain,
    ( ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))
    | ~ spl3_4
    | ~ spl3_32
    | ~ spl3_65
    | ~ spl3_93 ),
    inference(forward_demodulation,[],[f1765,f1015])).

fof(f1765,plain,
    ( ! [X4,X5] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f1764])).

fof(f1766,plain,
    ( spl3_93
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f243,f216,f99,f92,f88,f1764])).

fof(f88,plain,
    ( spl3_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f92,plain,
    ( spl3_9
  <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f216,plain,
    ( spl3_23
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f243,plain,
    ( ! [X4,X5] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f242,f145])).

fof(f145,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f93,f100])).

fof(f93,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f242,plain,
    ( ! [X4,X5] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5)))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f236,f89])).

fof(f89,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f236,plain,
    ( ! [X4,X5] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)))
    | ~ spl3_23 ),
    inference(superposition,[],[f217,f217])).

fof(f217,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1551,plain,
    ( spl3_84
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f182,f132,f124,f84,f1549])).

fof(f124,plain,
    ( spl3_15
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f182,plain,
    ( ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f177,f85])).

fof(f177,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(superposition,[],[f125,f133])).

fof(f125,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1202,plain,
    ( spl3_72
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f227,f212,f84,f1200])).

fof(f227,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3))
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(superposition,[],[f213,f85])).

fof(f1197,plain,
    ( spl3_71
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f233,f212,f124,f71,f1195])).

fof(f233,plain,
    ( ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) = k2_xboole_0(k1_xboole_0,X6)
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f226,f166])).

fof(f166,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(superposition,[],[f125,f72])).

fof(f226,plain,
    ( ! [X6] : k5_xboole_0(k1_xboole_0,X6) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6)
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(superposition,[],[f213,f72])).

fof(f1045,plain,
    ( spl3_66
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f176,f132,f116,f1043])).

fof(f116,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f176,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | ~ r1_tarski(X2,k3_xboole_0(X2,X3)) )
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(superposition,[],[f133,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f970,plain,
    ( spl3_65
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f169,f128,f99,f968])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(superposition,[],[f129,f100])).

fof(f895,plain,
    ( spl3_62
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f203,f136,f132,f893])).

fof(f203,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f194,f133])).

fof(f194,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl3_18 ),
    inference(superposition,[],[f137,f137])).

fof(f801,plain,
    ( spl3_59
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f201,f136,f116,f71,f799])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f192,f72])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(superposition,[],[f137,f117])).

fof(f701,plain,
    ( spl3_55
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f170,f128,f88,f699])).

fof(f170,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(superposition,[],[f129,f89])).

fof(f548,plain,
    ( spl3_46
    | ~ spl3_10
    | ~ spl3_32
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f544,f541,f370,f99,f546])).

fof(f541,plain,
    ( spl3_45
  <=> ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f544,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6)
    | ~ spl3_10
    | ~ spl3_32
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f542,f374])).

fof(f542,plain,
    ( ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,X6)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f541])).

fof(f543,plain,
    ( spl3_45
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f195,f136,f71,f541])).

fof(f195,plain,
    ( ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,X6)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(superposition,[],[f137,f72])).

fof(f505,plain,
    ( spl3_42
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f166,f124,f71,f503])).

fof(f372,plain,
    ( spl3_32
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f82,f75,f71,f370])).

fof(f75,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f76,f72])).

fof(f76,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f338,plain,
    ( ~ spl3_6
    | ~ spl3_9
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_9
    | spl3_30 ),
    inference(unit_resulting_resolution,[],[f93,f331,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f331,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl3_30
  <=> r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f332,plain,
    ( ~ spl3_30
    | ~ spl3_1
    | spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f208,f141,f63,f51,f329])).

fof(f141,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f208,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl3_1
    | spl3_3
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f64,f53,f142])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f141])).

fof(f53,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f64,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f307,plain,
    ( spl3_28
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f161,f116,f51,f304])).

fof(f161,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f53,f117])).

fof(f249,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f48,f247])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f218,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f42,f216])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f214,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f41,f212])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f143,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f49,f141])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f138,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f40,f136])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f134,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f39,f132])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f130,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f38,f128])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f126,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f37,f124])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f118,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f47,f116])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f109,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f46,f107])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f44,f99])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f94,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f36,f92])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f90,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f86,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f81,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f77,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f73,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f69,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f67,f63,f51])).

fof(f67,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f30,f64])).

fof(f30,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f29,f55,f51])).

fof(f29,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (21337)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (21341)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.44  % (21349)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (21335)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (21334)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (21338)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (21342)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (21336)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (21332)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (21333)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (21348)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (21340)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (21344)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (21339)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (21345)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (21343)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (21346)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (21347)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.21/0.63  % (21337)Refutation found. Thanks to Tanya!
% 2.21/0.63  % SZS status Theorem for theBenchmark
% 2.21/0.63  % SZS output start Proof for theBenchmark
% 2.21/0.63  fof(f12932,plain,(
% 2.21/0.63    $false),
% 2.21/0.63    inference(avatar_sat_refutation,[],[f58,f69,f73,f77,f81,f86,f90,f94,f101,f109,f118,f126,f130,f134,f138,f143,f214,f218,f249,f307,f332,f338,f372,f505,f543,f548,f701,f801,f895,f970,f1045,f1197,f1202,f1551,f1766,f1771,f1848,f1990,f2126,f2127,f2388,f2400,f2683,f3838,f8757,f9858,f12580,f12607,f12866,f12920,f12931])).
% 2.21/0.63  fof(f12931,plain,(
% 2.21/0.63    ~spl3_12 | ~spl3_46 | spl3_277),
% 2.21/0.63    inference(avatar_contradiction_clause,[],[f12926])).
% 2.21/0.63  fof(f12926,plain,(
% 2.21/0.63    $false | (~spl3_12 | ~spl3_46 | spl3_277)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f547,f12919,f108])).
% 2.21/0.63  fof(f108,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_12),
% 2.21/0.63    inference(avatar_component_clause,[],[f107])).
% 2.21/0.63  fof(f107,plain,(
% 2.21/0.63    spl3_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.21/0.63  fof(f12919,plain,(
% 2.21/0.63    ~r1_tarski(sK0,sK0) | spl3_277),
% 2.21/0.63    inference(avatar_component_clause,[],[f12917])).
% 2.21/0.63  fof(f12917,plain,(
% 2.21/0.63    spl3_277 <=> r1_tarski(sK0,sK0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_277])])).
% 2.21/0.63  fof(f547,plain,(
% 2.21/0.63    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) ) | ~spl3_46),
% 2.21/0.63    inference(avatar_component_clause,[],[f546])).
% 2.21/0.63  fof(f546,plain,(
% 2.21/0.63    spl3_46 <=> ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 2.21/0.63  fof(f12920,plain,(
% 2.21/0.63    ~spl3_277 | ~spl3_94 | spl3_113 | ~spl3_114 | ~spl3_124),
% 2.21/0.63    inference(avatar_split_clause,[],[f12779,f2681,f2397,f2385,f1769,f12917])).
% 2.21/0.63  fof(f1769,plain,(
% 2.21/0.63    spl3_94 <=> ! [X5,X4] : k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 2.21/0.63  fof(f2385,plain,(
% 2.21/0.63    spl3_113 <=> r1_tarski(sK0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).
% 2.21/0.63  fof(f2397,plain,(
% 2.21/0.63    spl3_114 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 2.21/0.63  fof(f2681,plain,(
% 2.21/0.63    spl3_124 <=> ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).
% 2.21/0.63  fof(f12779,plain,(
% 2.21/0.63    ~r1_tarski(sK0,sK0) | (~spl3_94 | spl3_113 | ~spl3_114 | ~spl3_124)),
% 2.21/0.63    inference(forward_demodulation,[],[f2387,f2731])).
% 2.21/0.63  fof(f2731,plain,(
% 2.21/0.63    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_94 | ~spl3_114 | ~spl3_124)),
% 2.21/0.63    inference(forward_demodulation,[],[f2694,f2399])).
% 2.21/0.63  fof(f2399,plain,(
% 2.21/0.63    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_114),
% 2.21/0.63    inference(avatar_component_clause,[],[f2397])).
% 2.21/0.63  fof(f2694,plain,(
% 2.21/0.63    k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_94 | ~spl3_124)),
% 2.21/0.63    inference(superposition,[],[f2682,f1770])).
% 2.21/0.63  fof(f1770,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))) ) | ~spl3_94),
% 2.21/0.63    inference(avatar_component_clause,[],[f1769])).
% 2.21/0.63  fof(f2682,plain,(
% 2.21/0.63    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))) ) | ~spl3_124),
% 2.21/0.63    inference(avatar_component_clause,[],[f2681])).
% 2.21/0.63  fof(f2387,plain,(
% 2.21/0.63    ~r1_tarski(sK0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl3_113),
% 2.21/0.63    inference(avatar_component_clause,[],[f2385])).
% 2.21/0.63  fof(f12866,plain,(
% 2.21/0.63    spl3_1 | ~spl3_12 | ~spl3_28),
% 2.21/0.63    inference(avatar_split_clause,[],[f315,f304,f107,f51])).
% 2.21/0.63  fof(f51,plain,(
% 2.21/0.63    spl3_1 <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.21/0.63  fof(f304,plain,(
% 2.21/0.63    spl3_28 <=> k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.21/0.63  fof(f315,plain,(
% 2.21/0.63    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_12 | ~spl3_28)),
% 2.21/0.63    inference(trivial_inequality_removal,[],[f310])).
% 2.21/0.63  fof(f310,plain,(
% 2.21/0.63    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_12 | ~spl3_28)),
% 2.21/0.63    inference(superposition,[],[f108,f306])).
% 2.21/0.63  fof(f306,plain,(
% 2.21/0.63    k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_28),
% 2.21/0.63    inference(avatar_component_clause,[],[f304])).
% 2.21/0.63  fof(f12607,plain,(
% 2.21/0.63    ~spl3_2 | ~spl3_59 | ~spl3_94 | spl3_114 | ~spl3_124),
% 2.21/0.63    inference(avatar_contradiction_clause,[],[f12606])).
% 2.21/0.63  fof(f12606,plain,(
% 2.21/0.63    $false | (~spl3_2 | ~spl3_59 | ~spl3_94 | spl3_114 | ~spl3_124)),
% 2.21/0.63    inference(subsumption_resolution,[],[f12605,f2398])).
% 2.21/0.63  fof(f2398,plain,(
% 2.21/0.63    sK0 != k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | spl3_114),
% 2.21/0.63    inference(avatar_component_clause,[],[f2397])).
% 2.21/0.63  fof(f12605,plain,(
% 2.21/0.63    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_59 | ~spl3_94 | ~spl3_124)),
% 2.21/0.63    inference(forward_demodulation,[],[f2694,f2111])).
% 2.21/0.63  fof(f2111,plain,(
% 2.21/0.63    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_59)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f57,f800])).
% 2.21/0.63  fof(f800,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_59),
% 2.21/0.63    inference(avatar_component_clause,[],[f799])).
% 2.21/0.63  fof(f799,plain,(
% 2.21/0.63    spl3_59 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 2.21/0.63  fof(f57,plain,(
% 2.21/0.63    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 2.21/0.63    inference(avatar_component_clause,[],[f55])).
% 2.21/0.63  fof(f55,plain,(
% 2.21/0.63    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.21/0.63  fof(f12580,plain,(
% 2.21/0.63    spl3_28 | ~spl3_114 | ~spl3_234 | ~spl3_248),
% 2.21/0.63    inference(avatar_contradiction_clause,[],[f12579])).
% 2.21/0.63  fof(f12579,plain,(
% 2.21/0.63    $false | (spl3_28 | ~spl3_114 | ~spl3_234 | ~spl3_248)),
% 2.21/0.63    inference(subsumption_resolution,[],[f9971,f305])).
% 2.21/0.63  fof(f305,plain,(
% 2.21/0.63    k1_xboole_0 != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | spl3_28),
% 2.21/0.63    inference(avatar_component_clause,[],[f304])).
% 2.21/0.63  fof(f9971,plain,(
% 2.21/0.63    k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_114 | ~spl3_234 | ~spl3_248)),
% 2.21/0.63    inference(forward_demodulation,[],[f9889,f8756])).
% 2.21/0.63  fof(f8756,plain,(
% 2.21/0.63    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) ) | ~spl3_234),
% 2.21/0.63    inference(avatar_component_clause,[],[f8755])).
% 2.21/0.63  fof(f8755,plain,(
% 2.21/0.63    spl3_234 <=> ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_234])])).
% 2.21/0.63  fof(f9889,plain,(
% 2.21/0.63    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) | (~spl3_114 | ~spl3_248)),
% 2.21/0.63    inference(superposition,[],[f9857,f2399])).
% 2.21/0.63  fof(f9857,plain,(
% 2.21/0.63    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7)) ) | ~spl3_248),
% 2.21/0.63    inference(avatar_component_clause,[],[f9856])).
% 2.21/0.63  fof(f9856,plain,(
% 2.21/0.63    spl3_248 <=> ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_248])])).
% 2.21/0.63  fof(f9858,plain,(
% 2.21/0.63    spl3_248 | ~spl3_16 | ~spl3_17 | ~spl3_22 | ~spl3_72),
% 2.21/0.63    inference(avatar_split_clause,[],[f1230,f1200,f212,f132,f128,f9856])).
% 2.21/0.63  fof(f128,plain,(
% 2.21/0.63    spl3_16 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.21/0.63  fof(f132,plain,(
% 2.21/0.63    spl3_17 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.21/0.63  fof(f212,plain,(
% 2.21/0.63    spl3_22 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.21/0.63  fof(f1200,plain,(
% 2.21/0.63    spl3_72 <=> ! [X3,X2] : k5_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 2.21/0.63  fof(f1230,plain,(
% 2.21/0.63    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7)) ) | (~spl3_16 | ~spl3_17 | ~spl3_22 | ~spl3_72)),
% 2.21/0.63    inference(forward_demodulation,[],[f1207,f231])).
% 2.21/0.63  fof(f231,plain,(
% 2.21/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X2))) ) | (~spl3_16 | ~spl3_17 | ~spl3_22)),
% 2.21/0.63    inference(forward_demodulation,[],[f220,f129])).
% 2.21/0.63  fof(f129,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_16),
% 2.21/0.63    inference(avatar_component_clause,[],[f128])).
% 2.21/0.63  fof(f220,plain,(
% 2.21/0.63    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X2))) ) | (~spl3_17 | ~spl3_22)),
% 2.21/0.63    inference(superposition,[],[f213,f133])).
% 2.21/0.63  fof(f133,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_17),
% 2.21/0.63    inference(avatar_component_clause,[],[f132])).
% 2.21/0.63  fof(f213,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ) | ~spl3_22),
% 2.21/0.63    inference(avatar_component_clause,[],[f212])).
% 2.21/0.63  fof(f1207,plain,(
% 2.21/0.63    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X7,X8),X7) = k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k3_xboole_0(X7,X8),X7))) ) | (~spl3_17 | ~spl3_72)),
% 2.21/0.63    inference(superposition,[],[f1201,f133])).
% 2.21/0.63  fof(f1201,plain,(
% 2.21/0.63    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3))) ) | ~spl3_72),
% 2.21/0.63    inference(avatar_component_clause,[],[f1200])).
% 2.21/0.63  fof(f8757,plain,(
% 2.21/0.63    spl3_234 | ~spl3_4 | ~spl3_18 | ~spl3_32 | ~spl3_46 | ~spl3_65 | ~spl3_84 | ~spl3_159),
% 2.21/0.63    inference(avatar_split_clause,[],[f3839,f3836,f1549,f968,f546,f370,f136,f71,f8755])).
% 2.21/0.63  fof(f71,plain,(
% 2.21/0.63    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.21/0.63  fof(f136,plain,(
% 2.21/0.63    spl3_18 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.21/0.63  fof(f370,plain,(
% 2.21/0.63    spl3_32 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.21/0.63  fof(f968,plain,(
% 2.21/0.63    spl3_65 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 2.21/0.63  fof(f1549,plain,(
% 2.21/0.63    spl3_84 <=> ! [X1,X0] : k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 2.21/0.63  fof(f3836,plain,(
% 2.21/0.63    spl3_159 <=> ! [X5] : k5_xboole_0(X5,X5) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_159])])).
% 2.21/0.63  fof(f3839,plain,(
% 2.21/0.63    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) ) | (~spl3_4 | ~spl3_18 | ~spl3_32 | ~spl3_46 | ~spl3_65 | ~spl3_84 | ~spl3_159)),
% 2.21/0.63    inference(forward_demodulation,[],[f3837,f1602])).
% 2.21/0.63  fof(f1602,plain,(
% 2.21/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | (~spl3_4 | ~spl3_18 | ~spl3_32 | ~spl3_46 | ~spl3_65 | ~spl3_84)),
% 2.21/0.63    inference(forward_demodulation,[],[f1601,f563])).
% 2.21/0.63  fof(f563,plain,(
% 2.21/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = X4) ) | (~spl3_4 | ~spl3_18 | ~spl3_46)),
% 2.21/0.63    inference(forward_demodulation,[],[f554,f72])).
% 2.21/0.63  fof(f72,plain,(
% 2.21/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 2.21/0.63    inference(avatar_component_clause,[],[f71])).
% 2.21/0.63  fof(f554,plain,(
% 2.21/0.63    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k3_xboole_0(X4,X4)) ) | (~spl3_18 | ~spl3_46)),
% 2.21/0.63    inference(superposition,[],[f137,f547])).
% 2.21/0.63  fof(f137,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_18),
% 2.21/0.63    inference(avatar_component_clause,[],[f136])).
% 2.21/0.63  fof(f1601,plain,(
% 2.21/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = k2_xboole_0(X0,k3_xboole_0(X0,X0))) ) | (~spl3_4 | ~spl3_32 | ~spl3_46 | ~spl3_65 | ~spl3_84)),
% 2.21/0.63    inference(forward_demodulation,[],[f1562,f1015])).
% 2.21/0.63  fof(f1015,plain,(
% 2.21/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl3_4 | ~spl3_32 | ~spl3_65)),
% 2.21/0.63    inference(forward_demodulation,[],[f971,f72])).
% 2.21/0.63  fof(f971,plain,(
% 2.21/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) ) | (~spl3_32 | ~spl3_65)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f371,f969])).
% 2.21/0.63  fof(f969,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | ~spl3_65),
% 2.21/0.63    inference(avatar_component_clause,[],[f968])).
% 2.21/0.63  fof(f371,plain,(
% 2.21/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_32),
% 2.21/0.63    inference(avatar_component_clause,[],[f370])).
% 2.21/0.63  fof(f1562,plain,(
% 2.21/0.63    ( ! [X0] : (k2_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) ) | (~spl3_46 | ~spl3_84)),
% 2.21/0.63    inference(superposition,[],[f1550,f547])).
% 2.21/0.63  fof(f1550,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_84),
% 2.21/0.63    inference(avatar_component_clause,[],[f1549])).
% 2.21/0.63  fof(f3837,plain,(
% 2.21/0.63    ( ! [X5] : (k5_xboole_0(X5,X5) = k2_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl3_159),
% 2.21/0.63    inference(avatar_component_clause,[],[f3836])).
% 2.21/0.63  fof(f3838,plain,(
% 2.21/0.63    spl3_159 | ~spl3_22 | ~spl3_46),
% 2.21/0.63    inference(avatar_split_clause,[],[f555,f546,f212,f3836])).
% 2.21/0.63  fof(f555,plain,(
% 2.21/0.63    ( ! [X5] : (k5_xboole_0(X5,X5) = k2_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl3_22 | ~spl3_46)),
% 2.21/0.63    inference(superposition,[],[f213,f547])).
% 2.21/0.63  fof(f2683,plain,(
% 2.21/0.63    spl3_124 | ~spl3_3 | ~spl3_99),
% 2.21/0.63    inference(avatar_split_clause,[],[f2000,f1988,f63,f2681])).
% 2.21/0.63  fof(f63,plain,(
% 2.21/0.63    spl3_3 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.21/0.63  fof(f1988,plain,(
% 2.21/0.63    spl3_99 <=> ! [X1,X0,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 2.21/0.63  fof(f2000,plain,(
% 2.21/0.63    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))) ) | (~spl3_3 | ~spl3_99)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f65,f1989])).
% 2.21/0.63  fof(f1989,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_99),
% 2.21/0.63    inference(avatar_component_clause,[],[f1988])).
% 2.21/0.63  fof(f65,plain,(
% 2.21/0.63    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_3),
% 2.21/0.63    inference(avatar_component_clause,[],[f63])).
% 2.21/0.63  fof(f2400,plain,(
% 2.21/0.63    spl3_114 | ~spl3_4 | ~spl3_18 | ~spl3_28),
% 2.21/0.63    inference(avatar_split_clause,[],[f317,f304,f136,f71,f2397])).
% 2.21/0.63  fof(f317,plain,(
% 2.21/0.63    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_4 | ~spl3_18 | ~spl3_28)),
% 2.21/0.63    inference(forward_demodulation,[],[f312,f72])).
% 2.21/0.63  fof(f312,plain,(
% 2.21/0.63    k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_18 | ~spl3_28)),
% 2.21/0.63    inference(superposition,[],[f137,f306])).
% 2.21/0.63  fof(f2388,plain,(
% 2.21/0.63    ~spl3_113 | spl3_26 | ~spl3_66),
% 2.21/0.63    inference(avatar_split_clause,[],[f1046,f1043,f290,f2385])).
% 2.21/0.63  fof(f290,plain,(
% 2.21/0.63    spl3_26 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.21/0.63  fof(f1043,plain,(
% 2.21/0.63    spl3_66 <=> ! [X3,X2] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,k3_xboole_0(X2,X3)))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 2.21/0.63  fof(f1046,plain,(
% 2.21/0.63    ~r1_tarski(sK0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | (spl3_26 | ~spl3_66)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f291,f1044])).
% 2.21/0.63  fof(f1044,plain,(
% 2.21/0.63    ( ! [X2,X3] : (~r1_tarski(X2,k3_xboole_0(X2,X3)) | k1_xboole_0 = k4_xboole_0(X2,X3)) ) | ~spl3_66),
% 2.21/0.63    inference(avatar_component_clause,[],[f1043])).
% 2.21/0.63  fof(f291,plain,(
% 2.21/0.63    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_26),
% 2.21/0.63    inference(avatar_component_clause,[],[f290])).
% 2.21/0.63  fof(f2127,plain,(
% 2.21/0.63    ~spl3_26 | spl3_2 | ~spl3_12),
% 2.21/0.63    inference(avatar_split_clause,[],[f294,f107,f55,f290])).
% 2.21/0.63  fof(f294,plain,(
% 2.21/0.63    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (spl3_2 | ~spl3_12)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f56,f108])).
% 2.21/0.63  fof(f56,plain,(
% 2.21/0.63    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 2.21/0.63    inference(avatar_component_clause,[],[f55])).
% 2.21/0.63  fof(f2126,plain,(
% 2.21/0.63    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 2.21/0.63    inference(avatar_split_clause,[],[f31,f63,f55,f51])).
% 2.21/0.63  fof(f31,plain,(
% 2.21/0.63    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.21/0.63    inference(cnf_transformation,[],[f26])).
% 2.21/0.63  fof(f26,plain,(
% 2.21/0.63    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 2.21/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).
% 2.21/0.63  fof(f25,plain,(
% 2.21/0.63    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 2.21/0.63    introduced(choice_axiom,[])).
% 2.21/0.63  fof(f24,plain,(
% 2.21/0.63    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.21/0.63    inference(flattening,[],[f23])).
% 2.21/0.63  fof(f23,plain,(
% 2.21/0.63    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.21/0.63    inference(nnf_transformation,[],[f19])).
% 2.21/0.63  fof(f19,plain,(
% 2.21/0.63    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.21/0.63    inference(ennf_transformation,[],[f18])).
% 2.21/0.63  fof(f18,negated_conjecture,(
% 2.21/0.63    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.21/0.63    inference(negated_conjecture,[],[f17])).
% 2.21/0.63  fof(f17,conjecture,(
% 2.21/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 2.21/0.63  fof(f1990,plain,(
% 2.21/0.63    spl3_99 | ~spl3_10 | ~spl3_16 | ~spl3_18 | ~spl3_22 | ~spl3_32 | ~spl3_42 | ~spl3_46 | ~spl3_55 | ~spl3_62 | ~spl3_71 | ~spl3_72 | ~spl3_96),
% 2.21/0.63    inference(avatar_split_clause,[],[f1849,f1846,f1200,f1195,f893,f699,f546,f503,f370,f212,f136,f128,f99,f1988])).
% 2.21/0.63  fof(f99,plain,(
% 2.21/0.63    spl3_10 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.21/0.63  fof(f503,plain,(
% 2.21/0.63    spl3_42 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 2.21/0.63  fof(f699,plain,(
% 2.21/0.63    spl3_55 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 2.21/0.63  fof(f893,plain,(
% 2.21/0.63    spl3_62 <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 2.21/0.63  fof(f1195,plain,(
% 2.21/0.63    spl3_71 <=> ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) = k2_xboole_0(k1_xboole_0,X6)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 2.21/0.63  fof(f1846,plain,(
% 2.21/0.63    spl3_96 <=> ! [X1,X0,X2] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 2.21/0.63  fof(f1849,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | (~spl3_10 | ~spl3_16 | ~spl3_18 | ~spl3_22 | ~spl3_32 | ~spl3_42 | ~spl3_46 | ~spl3_55 | ~spl3_62 | ~spl3_71 | ~spl3_72 | ~spl3_96)),
% 2.21/0.63    inference(forward_demodulation,[],[f1847,f1247])).
% 2.21/0.63  fof(f1247,plain,(
% 2.21/0.63    ( ! [X12,X11] : (k3_xboole_0(X11,X12) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X11,X12))) ) | (~spl3_10 | ~spl3_16 | ~spl3_18 | ~spl3_22 | ~spl3_32 | ~spl3_42 | ~spl3_46 | ~spl3_55 | ~spl3_62 | ~spl3_71 | ~spl3_72)),
% 2.21/0.63    inference(forward_demodulation,[],[f1246,f926])).
% 2.21/0.63  fof(f926,plain,(
% 2.21/0.63    ( ! [X10,X11] : (k3_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X10,X11))) ) | (~spl3_16 | ~spl3_18 | ~spl3_62)),
% 2.21/0.63    inference(forward_demodulation,[],[f910,f137])).
% 2.21/0.63  fof(f910,plain,(
% 2.21/0.63    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k5_xboole_0(X10,k4_xboole_0(X10,X11))) ) | (~spl3_16 | ~spl3_62)),
% 2.21/0.63    inference(superposition,[],[f129,f894])).
% 2.21/0.63  fof(f894,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl3_62),
% 2.21/0.63    inference(avatar_component_clause,[],[f893])).
% 2.21/0.63  fof(f1246,plain,(
% 2.21/0.63    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X11,X12))) ) | (~spl3_10 | ~spl3_18 | ~spl3_22 | ~spl3_32 | ~spl3_42 | ~spl3_46 | ~spl3_55 | ~spl3_62 | ~spl3_71 | ~spl3_72)),
% 2.21/0.63    inference(forward_demodulation,[],[f1245,f1198])).
% 2.21/0.63  fof(f1198,plain,(
% 2.21/0.63    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X6)) ) | (~spl3_10 | ~spl3_32 | ~spl3_42 | ~spl3_55 | ~spl3_71)),
% 2.21/0.63    inference(forward_demodulation,[],[f1196,f716])).
% 2.21/0.63  fof(f716,plain,(
% 2.21/0.63    ( ! [X3] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl3_10 | ~spl3_32 | ~spl3_42 | ~spl3_55)),
% 2.21/0.63    inference(forward_demodulation,[],[f709,f374])).
% 2.21/0.63  fof(f374,plain,(
% 2.21/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_10 | ~spl3_32)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f371,f100])).
% 2.21/0.63  fof(f100,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_10),
% 2.21/0.63    inference(avatar_component_clause,[],[f99])).
% 2.21/0.63  fof(f709,plain,(
% 2.21/0.63    ( ! [X3] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl3_42 | ~spl3_55)),
% 2.21/0.63    inference(superposition,[],[f700,f504])).
% 2.21/0.63  fof(f504,plain,(
% 2.21/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) ) | ~spl3_42),
% 2.21/0.63    inference(avatar_component_clause,[],[f503])).
% 2.21/0.63  fof(f700,plain,(
% 2.21/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | ~spl3_55),
% 2.21/0.63    inference(avatar_component_clause,[],[f699])).
% 2.21/0.63  fof(f1196,plain,(
% 2.21/0.63    ( ! [X6] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) = k2_xboole_0(k1_xboole_0,X6)) ) | ~spl3_71),
% 2.21/0.63    inference(avatar_component_clause,[],[f1195])).
% 2.21/0.63  fof(f1245,plain,(
% 2.21/0.63    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X11,X12))) ) | (~spl3_18 | ~spl3_22 | ~spl3_46 | ~spl3_55 | ~spl3_62 | ~spl3_72)),
% 2.21/0.63    inference(forward_demodulation,[],[f1218,f932])).
% 2.21/0.63  fof(f932,plain,(
% 2.21/0.63    ( ! [X37,X36] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X36,X37),X36)) ) | (~spl3_22 | ~spl3_46 | ~spl3_55 | ~spl3_62)),
% 2.21/0.63    inference(forward_demodulation,[],[f921,f555])).
% 2.21/0.63  fof(f921,plain,(
% 2.21/0.63    ( ! [X37,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),X36) = k5_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,X37))) ) | (~spl3_55 | ~spl3_62)),
% 2.21/0.63    inference(superposition,[],[f700,f894])).
% 2.21/0.63  fof(f1218,plain,(
% 2.21/0.63    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,X12),X11),k3_xboole_0(X11,X12))) ) | (~spl3_18 | ~spl3_72)),
% 2.21/0.63    inference(superposition,[],[f1201,f137])).
% 2.21/0.63  fof(f1847,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_96),
% 2.21/0.63    inference(avatar_component_clause,[],[f1846])).
% 2.21/0.63  fof(f1848,plain,(
% 2.21/0.63    spl3_96 | ~spl3_7 | ~spl3_10 | ~spl3_24),
% 2.21/0.63    inference(avatar_split_clause,[],[f260,f247,f99,f84,f1846])).
% 2.21/0.63  fof(f84,plain,(
% 2.21/0.63    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.21/0.63  fof(f247,plain,(
% 2.21/0.63    spl3_24 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.21/0.63  fof(f260,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | (~spl3_7 | ~spl3_10 | ~spl3_24)),
% 2.21/0.63    inference(forward_demodulation,[],[f253,f85])).
% 2.21/0.63  fof(f85,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_7),
% 2.21/0.63    inference(avatar_component_clause,[],[f84])).
% 2.21/0.63  fof(f253,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | (~spl3_10 | ~spl3_24)),
% 2.21/0.63    inference(superposition,[],[f248,f100])).
% 2.21/0.63  fof(f248,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_24),
% 2.21/0.63    inference(avatar_component_clause,[],[f247])).
% 2.21/0.63  fof(f1771,plain,(
% 2.21/0.63    spl3_94 | ~spl3_4 | ~spl3_32 | ~spl3_65 | ~spl3_93),
% 2.21/0.63    inference(avatar_split_clause,[],[f1767,f1764,f968,f370,f71,f1769])).
% 2.21/0.63  fof(f1764,plain,(
% 2.21/0.63    spl3_93 <=> ! [X5,X4] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 2.21/0.63  fof(f1767,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))) ) | (~spl3_4 | ~spl3_32 | ~spl3_65 | ~spl3_93)),
% 2.21/0.63    inference(forward_demodulation,[],[f1765,f1015])).
% 2.21/0.63  fof(f1765,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)) ) | ~spl3_93),
% 2.21/0.63    inference(avatar_component_clause,[],[f1764])).
% 2.21/0.63  fof(f1766,plain,(
% 2.21/0.63    spl3_93 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_23),
% 2.21/0.63    inference(avatar_split_clause,[],[f243,f216,f99,f92,f88,f1764])).
% 2.21/0.63  fof(f88,plain,(
% 2.21/0.63    spl3_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.21/0.63  fof(f92,plain,(
% 2.21/0.63    spl3_9 <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.21/0.63  fof(f216,plain,(
% 2.21/0.63    spl3_23 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.21/0.63  fof(f243,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)) ) | (~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_23)),
% 2.21/0.63    inference(forward_demodulation,[],[f242,f145])).
% 2.21/0.63  fof(f145,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | (~spl3_9 | ~spl3_10)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f93,f100])).
% 2.21/0.63  fof(f93,plain,(
% 2.21/0.63    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl3_9),
% 2.21/0.63    inference(avatar_component_clause,[],[f92])).
% 2.21/0.63  fof(f242,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5)))) ) | (~spl3_8 | ~spl3_23)),
% 2.21/0.63    inference(forward_demodulation,[],[f236,f89])).
% 2.21/0.63  fof(f89,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_8),
% 2.21/0.63    inference(avatar_component_clause,[],[f88])).
% 2.21/0.63  fof(f236,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)))) ) | ~spl3_23),
% 2.21/0.63    inference(superposition,[],[f217,f217])).
% 2.21/0.63  fof(f217,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl3_23),
% 2.21/0.63    inference(avatar_component_clause,[],[f216])).
% 2.21/0.63  fof(f1551,plain,(
% 2.21/0.63    spl3_84 | ~spl3_7 | ~spl3_15 | ~spl3_17),
% 2.21/0.63    inference(avatar_split_clause,[],[f182,f132,f124,f84,f1549])).
% 2.21/0.63  fof(f124,plain,(
% 2.21/0.63    spl3_15 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.21/0.63  fof(f182,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl3_7 | ~spl3_15 | ~spl3_17)),
% 2.21/0.63    inference(forward_demodulation,[],[f177,f85])).
% 2.21/0.63  fof(f177,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl3_15 | ~spl3_17)),
% 2.21/0.63    inference(superposition,[],[f125,f133])).
% 2.21/0.63  fof(f125,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_15),
% 2.21/0.63    inference(avatar_component_clause,[],[f124])).
% 2.21/0.63  fof(f1202,plain,(
% 2.21/0.63    spl3_72 | ~spl3_7 | ~spl3_22),
% 2.21/0.63    inference(avatar_split_clause,[],[f227,f212,f84,f1200])).
% 2.21/0.63  fof(f227,plain,(
% 2.21/0.63    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3))) ) | (~spl3_7 | ~spl3_22)),
% 2.21/0.63    inference(superposition,[],[f213,f85])).
% 2.21/0.63  fof(f1197,plain,(
% 2.21/0.63    spl3_71 | ~spl3_4 | ~spl3_15 | ~spl3_22),
% 2.21/0.63    inference(avatar_split_clause,[],[f233,f212,f124,f71,f1195])).
% 2.21/0.63  fof(f233,plain,(
% 2.21/0.63    ( ! [X6] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) = k2_xboole_0(k1_xboole_0,X6)) ) | (~spl3_4 | ~spl3_15 | ~spl3_22)),
% 2.21/0.63    inference(forward_demodulation,[],[f226,f166])).
% 2.21/0.63  fof(f166,plain,(
% 2.21/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl3_4 | ~spl3_15)),
% 2.21/0.63    inference(superposition,[],[f125,f72])).
% 2.21/0.63  fof(f226,plain,(
% 2.21/0.63    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6)) ) | (~spl3_4 | ~spl3_22)),
% 2.21/0.63    inference(superposition,[],[f213,f72])).
% 2.21/0.63  fof(f1045,plain,(
% 2.21/0.63    spl3_66 | ~spl3_14 | ~spl3_17),
% 2.21/0.63    inference(avatar_split_clause,[],[f176,f132,f116,f1043])).
% 2.21/0.63  fof(f116,plain,(
% 2.21/0.63    spl3_14 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.21/0.63  fof(f176,plain,(
% 2.21/0.63    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,k3_xboole_0(X2,X3))) ) | (~spl3_14 | ~spl3_17)),
% 2.21/0.63    inference(superposition,[],[f133,f117])).
% 2.21/0.63  fof(f117,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 2.21/0.63    inference(avatar_component_clause,[],[f116])).
% 2.21/0.63  fof(f970,plain,(
% 2.21/0.63    spl3_65 | ~spl3_10 | ~spl3_16),
% 2.21/0.63    inference(avatar_split_clause,[],[f169,f128,f99,f968])).
% 2.21/0.63  fof(f169,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | (~spl3_10 | ~spl3_16)),
% 2.21/0.63    inference(superposition,[],[f129,f100])).
% 2.21/0.63  fof(f895,plain,(
% 2.21/0.63    spl3_62 | ~spl3_17 | ~spl3_18),
% 2.21/0.63    inference(avatar_split_clause,[],[f203,f136,f132,f893])).
% 2.21/0.63  fof(f203,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl3_17 | ~spl3_18)),
% 2.21/0.63    inference(forward_demodulation,[],[f194,f133])).
% 2.21/0.63  fof(f194,plain,(
% 2.21/0.63    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl3_18),
% 2.21/0.63    inference(superposition,[],[f137,f137])).
% 2.21/0.63  fof(f801,plain,(
% 2.21/0.63    spl3_59 | ~spl3_4 | ~spl3_14 | ~spl3_18),
% 2.21/0.63    inference(avatar_split_clause,[],[f201,f136,f116,f71,f799])).
% 2.21/0.63  fof(f201,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | (~spl3_4 | ~spl3_14 | ~spl3_18)),
% 2.21/0.63    inference(forward_demodulation,[],[f192,f72])).
% 2.21/0.63  fof(f192,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X0,X1)) ) | (~spl3_14 | ~spl3_18)),
% 2.21/0.63    inference(superposition,[],[f137,f117])).
% 2.21/0.63  fof(f701,plain,(
% 2.21/0.63    spl3_55 | ~spl3_8 | ~spl3_16),
% 2.21/0.63    inference(avatar_split_clause,[],[f170,f128,f88,f699])).
% 2.21/0.63  fof(f170,plain,(
% 2.21/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | (~spl3_8 | ~spl3_16)),
% 2.21/0.63    inference(superposition,[],[f129,f89])).
% 2.21/0.63  fof(f548,plain,(
% 2.21/0.63    spl3_46 | ~spl3_10 | ~spl3_32 | ~spl3_45),
% 2.21/0.63    inference(avatar_split_clause,[],[f544,f541,f370,f99,f546])).
% 2.21/0.63  fof(f541,plain,(
% 2.21/0.63    spl3_45 <=> ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,X6)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 2.21/0.63  fof(f544,plain,(
% 2.21/0.63    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) ) | (~spl3_10 | ~spl3_32 | ~spl3_45)),
% 2.21/0.63    inference(forward_demodulation,[],[f542,f374])).
% 2.21/0.63  fof(f542,plain,(
% 2.21/0.63    ( ! [X6] : (k3_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,X6)) ) | ~spl3_45),
% 2.21/0.63    inference(avatar_component_clause,[],[f541])).
% 2.21/0.63  fof(f543,plain,(
% 2.21/0.63    spl3_45 | ~spl3_4 | ~spl3_18),
% 2.21/0.63    inference(avatar_split_clause,[],[f195,f136,f71,f541])).
% 2.21/0.63  fof(f195,plain,(
% 2.21/0.63    ( ! [X6] : (k3_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,X6)) ) | (~spl3_4 | ~spl3_18)),
% 2.21/0.63    inference(superposition,[],[f137,f72])).
% 2.21/0.63  fof(f505,plain,(
% 2.21/0.63    spl3_42 | ~spl3_4 | ~spl3_15),
% 2.21/0.63    inference(avatar_split_clause,[],[f166,f124,f71,f503])).
% 2.21/0.63  fof(f372,plain,(
% 2.21/0.63    spl3_32 | ~spl3_4 | ~spl3_5),
% 2.21/0.63    inference(avatar_split_clause,[],[f82,f75,f71,f370])).
% 2.21/0.63  fof(f75,plain,(
% 2.21/0.63    spl3_5 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.21/0.63  fof(f82,plain,(
% 2.21/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_5)),
% 2.21/0.63    inference(superposition,[],[f76,f72])).
% 2.21/0.63  fof(f76,plain,(
% 2.21/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_5),
% 2.21/0.63    inference(avatar_component_clause,[],[f75])).
% 2.21/0.63  fof(f338,plain,(
% 2.21/0.63    ~spl3_6 | ~spl3_9 | spl3_30),
% 2.21/0.63    inference(avatar_contradiction_clause,[],[f336])).
% 2.21/0.63  fof(f336,plain,(
% 2.21/0.63    $false | (~spl3_6 | ~spl3_9 | spl3_30)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f93,f331,f80])).
% 2.21/0.63  fof(f80,plain,(
% 2.21/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_6),
% 2.21/0.63    inference(avatar_component_clause,[],[f79])).
% 2.21/0.63  fof(f79,plain,(
% 2.21/0.63    spl3_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.21/0.63  fof(f331,plain,(
% 2.21/0.63    ~r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | spl3_30),
% 2.21/0.63    inference(avatar_component_clause,[],[f329])).
% 2.21/0.63  fof(f329,plain,(
% 2.21/0.63    spl3_30 <=> r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.21/0.63  fof(f332,plain,(
% 2.21/0.63    ~spl3_30 | ~spl3_1 | spl3_3 | ~spl3_19),
% 2.21/0.63    inference(avatar_split_clause,[],[f208,f141,f63,f51,f329])).
% 2.21/0.63  fof(f141,plain,(
% 2.21/0.63    spl3_19 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.21/0.63  fof(f208,plain,(
% 2.21/0.63    ~r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | (~spl3_1 | spl3_3 | ~spl3_19)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f64,f53,f142])).
% 2.21/0.63  fof(f142,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_19),
% 2.21/0.63    inference(avatar_component_clause,[],[f141])).
% 2.21/0.63  fof(f53,plain,(
% 2.21/0.63    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.21/0.63    inference(avatar_component_clause,[],[f51])).
% 2.21/0.63  fof(f64,plain,(
% 2.21/0.63    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_3),
% 2.21/0.63    inference(avatar_component_clause,[],[f63])).
% 2.21/0.63  fof(f307,plain,(
% 2.21/0.63    spl3_28 | ~spl3_1 | ~spl3_14),
% 2.21/0.63    inference(avatar_split_clause,[],[f161,f116,f51,f304])).
% 2.21/0.63  fof(f161,plain,(
% 2.21/0.63    k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_14)),
% 2.21/0.63    inference(unit_resulting_resolution,[],[f53,f117])).
% 2.21/0.63  fof(f249,plain,(
% 2.21/0.63    spl3_24),
% 2.21/0.63    inference(avatar_split_clause,[],[f48,f247])).
% 2.21/0.63  fof(f48,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f9])).
% 2.21/0.63  fof(f9,axiom,(
% 2.21/0.63    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 2.21/0.63  fof(f218,plain,(
% 2.21/0.63    spl3_23),
% 2.21/0.63    inference(avatar_split_clause,[],[f42,f216])).
% 2.21/0.63  fof(f42,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f15])).
% 2.21/0.63  fof(f15,axiom,(
% 2.21/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.21/0.63  fof(f214,plain,(
% 2.21/0.63    spl3_22),
% 2.21/0.63    inference(avatar_split_clause,[],[f41,f212])).
% 2.21/0.63  fof(f41,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f3])).
% 2.21/0.63  fof(f3,axiom,(
% 2.21/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.21/0.63  fof(f143,plain,(
% 2.21/0.63    spl3_19),
% 2.21/0.63    inference(avatar_split_clause,[],[f49,f141])).
% 2.21/0.63  fof(f49,plain,(
% 2.21/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.21/0.63    inference(cnf_transformation,[],[f22])).
% 2.21/0.63  fof(f22,plain,(
% 2.21/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.21/0.63    inference(flattening,[],[f21])).
% 2.21/0.63  fof(f21,plain,(
% 2.21/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.21/0.63    inference(ennf_transformation,[],[f13])).
% 2.21/0.63  fof(f13,axiom,(
% 2.21/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.21/0.63  fof(f138,plain,(
% 2.21/0.63    spl3_18),
% 2.21/0.63    inference(avatar_split_clause,[],[f40,f136])).
% 2.21/0.63  fof(f40,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f12])).
% 2.21/0.63  fof(f12,axiom,(
% 2.21/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.21/0.63  fof(f134,plain,(
% 2.21/0.63    spl3_17),
% 2.21/0.63    inference(avatar_split_clause,[],[f39,f132])).
% 2.21/0.63  fof(f39,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f11])).
% 2.21/0.63  fof(f11,axiom,(
% 2.21/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.21/0.63  fof(f130,plain,(
% 2.21/0.63    spl3_16),
% 2.21/0.63    inference(avatar_split_clause,[],[f38,f128])).
% 2.21/0.63  fof(f38,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f8])).
% 2.21/0.63  fof(f8,axiom,(
% 2.21/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.21/0.63  fof(f126,plain,(
% 2.21/0.63    spl3_15),
% 2.21/0.63    inference(avatar_split_clause,[],[f37,f124])).
% 2.21/0.63  fof(f37,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f16])).
% 2.21/0.63  fof(f16,axiom,(
% 2.21/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.21/0.63  fof(f118,plain,(
% 2.21/0.63    spl3_14),
% 2.21/0.63    inference(avatar_split_clause,[],[f47,f116])).
% 2.21/0.63  fof(f47,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.21/0.63    inference(cnf_transformation,[],[f28])).
% 2.21/0.63  fof(f28,plain,(
% 2.21/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.21/0.63    inference(nnf_transformation,[],[f6])).
% 2.21/0.63  fof(f6,axiom,(
% 2.21/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.21/0.63  fof(f109,plain,(
% 2.21/0.63    spl3_12),
% 2.21/0.63    inference(avatar_split_clause,[],[f46,f107])).
% 2.21/0.63  fof(f46,plain,(
% 2.21/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.21/0.63    inference(cnf_transformation,[],[f28])).
% 2.21/0.63  fof(f101,plain,(
% 2.21/0.63    spl3_10),
% 2.21/0.63    inference(avatar_split_clause,[],[f44,f99])).
% 2.21/0.63  fof(f44,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.21/0.63    inference(cnf_transformation,[],[f27])).
% 2.21/0.63  fof(f27,plain,(
% 2.21/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.21/0.63    inference(nnf_transformation,[],[f4])).
% 2.21/0.63  fof(f4,axiom,(
% 2.21/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.21/0.63  fof(f94,plain,(
% 2.21/0.63    spl3_9),
% 2.21/0.63    inference(avatar_split_clause,[],[f36,f92])).
% 2.21/0.63  fof(f36,plain,(
% 2.21/0.63    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.21/0.63    inference(cnf_transformation,[],[f7])).
% 2.21/0.63  fof(f7,axiom,(
% 2.21/0.63    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.21/0.63  fof(f90,plain,(
% 2.21/0.63    spl3_8),
% 2.21/0.63    inference(avatar_split_clause,[],[f35,f88])).
% 2.21/0.63  fof(f35,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.21/0.63    inference(cnf_transformation,[],[f2])).
% 2.21/0.63  fof(f2,axiom,(
% 2.21/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.21/0.63  fof(f86,plain,(
% 2.21/0.63    spl3_7),
% 2.21/0.63    inference(avatar_split_clause,[],[f34,f84])).
% 2.21/0.63  fof(f34,plain,(
% 2.21/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.21/0.63    inference(cnf_transformation,[],[f1])).
% 2.21/0.63  fof(f1,axiom,(
% 2.21/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.21/0.63  fof(f81,plain,(
% 2.21/0.63    spl3_6),
% 2.21/0.63    inference(avatar_split_clause,[],[f43,f79])).
% 2.21/0.63  fof(f43,plain,(
% 2.21/0.63    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.21/0.63    inference(cnf_transformation,[],[f20])).
% 2.21/0.63  fof(f20,plain,(
% 2.21/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.21/0.63    inference(ennf_transformation,[],[f5])).
% 2.21/0.63  fof(f5,axiom,(
% 2.21/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.21/0.63  fof(f77,plain,(
% 2.21/0.63    spl3_5),
% 2.21/0.63    inference(avatar_split_clause,[],[f33,f75])).
% 2.21/0.63  fof(f33,plain,(
% 2.21/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.21/0.63    inference(cnf_transformation,[],[f14])).
% 2.21/0.63  fof(f14,axiom,(
% 2.21/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.21/0.63  fof(f73,plain,(
% 2.21/0.63    spl3_4),
% 2.21/0.63    inference(avatar_split_clause,[],[f32,f71])).
% 2.21/0.63  fof(f32,plain,(
% 2.21/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.63    inference(cnf_transformation,[],[f10])).
% 2.21/0.63  fof(f10,axiom,(
% 2.21/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.21/0.63  fof(f69,plain,(
% 2.21/0.63    spl3_1 | spl3_3),
% 2.21/0.63    inference(avatar_split_clause,[],[f67,f63,f51])).
% 2.21/0.63  fof(f67,plain,(
% 2.21/0.63    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | spl3_3),
% 2.21/0.63    inference(subsumption_resolution,[],[f30,f64])).
% 2.21/0.63  fof(f30,plain,(
% 2.21/0.63    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.21/0.63    inference(cnf_transformation,[],[f26])).
% 2.21/0.63  fof(f58,plain,(
% 2.21/0.63    spl3_1 | spl3_2),
% 2.21/0.63    inference(avatar_split_clause,[],[f29,f55,f51])).
% 2.21/0.63  fof(f29,plain,(
% 2.21/0.63    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.21/0.63    inference(cnf_transformation,[],[f26])).
% 2.21/0.63  % SZS output end Proof for theBenchmark
% 2.21/0.63  % (21337)------------------------------
% 2.21/0.63  % (21337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.63  % (21337)Termination reason: Refutation
% 2.21/0.63  
% 2.21/0.63  % (21337)Memory used [KB]: 13944
% 2.21/0.63  % (21337)Time elapsed: 0.222 s
% 2.21/0.63  % (21337)------------------------------
% 2.21/0.63  % (21337)------------------------------
% 2.21/0.64  % (21329)Success in time 0.282 s
%------------------------------------------------------------------------------
