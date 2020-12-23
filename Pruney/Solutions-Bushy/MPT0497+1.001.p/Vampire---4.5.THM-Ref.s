%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0497+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:05 EST 2020

% Result     : Theorem 5.18s
% Output     : Refutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 396 expanded)
%              Number of leaves         :   54 ( 199 expanded)
%              Depth                    :    7
%              Number of atoms          :  716 (1244 expanded)
%              Number of equality atoms :   85 ( 148 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f71,f74,f78,f86,f90,f94,f102,f106,f118,f126,f136,f144,f153,f171,f177,f186,f190,f250,f259,f286,f300,f322,f335,f349,f365,f376,f380,f400,f422,f499,f517,f526,f556,f1141,f1152,f1166,f1211,f1263,f1390,f1409,f1410,f1695,f1951,f5330,f5357])).

fof(f5357,plain,
    ( spl8_18
    | ~ spl8_150
    | ~ spl8_295 ),
    inference(avatar_contradiction_clause,[],[f5356])).

fof(f5356,plain,
    ( $false
    | spl8_18
    | ~ spl8_150
    | ~ spl8_295 ),
    inference(subsumption_resolution,[],[f5355,f1408])).

fof(f1408,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_18
  <=> k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f5355,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl8_150
    | ~ spl8_295 ),
    inference(duplicate_literal_removal,[],[f5350])).

fof(f5350,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl8_150
    | ~ spl8_295 ),
    inference(resolution,[],[f5329,f1950])).

fof(f1950,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(X0,X1,k1_xboole_0),X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl8_150 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f1949,plain,
    ( spl8_150
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | r2_hidden(sK7(X0,X1,k1_xboole_0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f5329,plain,
    ( ! [X55] :
        ( ~ r2_hidden(sK7(sK0,X55,k1_xboole_0),k1_relat_1(sK1))
        | k1_xboole_0 = k3_xboole_0(sK0,X55) )
    | ~ spl8_295 ),
    inference(avatar_component_clause,[],[f5328])).

fof(f5328,plain,
    ( spl8_295
  <=> ! [X55] :
        ( k1_xboole_0 = k3_xboole_0(sK0,X55)
        | ~ r2_hidden(sK7(sK0,X55,k1_xboole_0),k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_295])])).

fof(f5330,plain,
    ( spl8_295
    | ~ spl8_114
    | ~ spl8_147 ),
    inference(avatar_split_clause,[],[f1726,f1693,f1150,f5328])).

fof(f1150,plain,
    ( spl8_114
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f1693,plain,
    ( spl8_147
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | r2_hidden(sK7(X0,X1,k1_xboole_0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f1726,plain,
    ( ! [X55] :
        ( k1_xboole_0 = k3_xboole_0(sK0,X55)
        | ~ r2_hidden(sK7(sK0,X55,k1_xboole_0),k1_relat_1(sK1)) )
    | ~ spl8_114
    | ~ spl8_147 ),
    inference(resolution,[],[f1694,f1151])).

fof(f1151,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl8_114 ),
    inference(avatar_component_clause,[],[f1150])).

fof(f1694,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(X0,X1,k1_xboole_0),X0)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl8_147 ),
    inference(avatar_component_clause,[],[f1693])).

fof(f1951,plain,
    ( spl8_150
    | ~ spl8_2
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f522,f515,f62,f1949])).

fof(f62,plain,
    ( spl8_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f515,plain,
    ( spl8_66
  <=> ! [X5,X4,X6] :
        ( r2_hidden(sK7(X4,X5,X6),X5)
        | k3_xboole_0(X4,X5) = X6
        | ~ v1_xboole_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f522,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | r2_hidden(sK7(X0,X1,k1_xboole_0),X1) )
    | ~ spl8_2
    | ~ spl8_66 ),
    inference(resolution,[],[f516,f63])).

fof(f63,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f516,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(X6)
        | k3_xboole_0(X4,X5) = X6
        | r2_hidden(sK7(X4,X5,X6),X5) )
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f515])).

fof(f1695,plain,
    ( spl8_147
    | ~ spl8_2
    | ~ spl8_65 ),
    inference(avatar_split_clause,[],[f500,f497,f62,f1693])).

fof(f497,plain,
    ( spl8_65
  <=> ! [X5,X4,X6] :
        ( r2_hidden(sK7(X4,X5,X6),X4)
        | k3_xboole_0(X4,X5) = X6
        | ~ v1_xboole_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f500,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | r2_hidden(sK7(X0,X1,k1_xboole_0),X0) )
    | ~ spl8_2
    | ~ spl8_65 ),
    inference(resolution,[],[f498,f63])).

fof(f498,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(X6)
        | k3_xboole_0(X4,X5) = X6
        | r2_hidden(sK7(X4,X5,X6),X4) )
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f497])).

fof(f1410,plain,
    ( spl8_113
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f1403,f554,f66,f62,f58,f1139])).

fof(f1139,plain,
    ( spl8_113
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f58,plain,
    ( spl8_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f66,plain,
    ( spl8_3
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f554,plain,
    ( spl8_70
  <=> ! [X5,X7,X8,X6] :
        ( ~ r2_hidden(X5,X6)
        | ~ r2_hidden(k4_tarski(X5,X7),X8)
        | ~ v1_relat_1(X8)
        | ~ v1_xboole_0(k7_relat_1(X8,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f1403,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
        | ~ r2_hidden(X11,sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1402,f59])).

fof(f59,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f1402,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X11,sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1399,f63])).

fof(f1399,plain,
    ( ! [X12,X11] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X11,X12),sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X11,sK0) )
    | ~ spl8_3
    | ~ spl8_70 ),
    inference(superposition,[],[f555,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f555,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ v1_xboole_0(k7_relat_1(X8,X6))
        | ~ r2_hidden(k4_tarski(X5,X7),X8)
        | ~ v1_relat_1(X8)
        | ~ r2_hidden(X5,X6) )
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f554])).

fof(f1409,plain,
    ( ~ spl8_18
    | ~ spl8_11
    | spl8_116 ),
    inference(avatar_split_clause,[],[f1393,f1164,f100,f138])).

fof(f100,plain,
    ( spl8_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f1164,plain,
    ( spl8_116
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f1393,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl8_11
    | spl8_116 ),
    inference(resolution,[],[f1165,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1165,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl8_116 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f1390,plain,
    ( spl8_3
    | ~ spl8_27
    | ~ spl8_51
    | ~ spl8_52
    | ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f1389])).

fof(f1389,plain,
    ( $false
    | spl8_3
    | ~ spl8_27
    | ~ spl8_51
    | ~ spl8_52
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1388,f72])).

fof(f72,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f1388,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl8_27
    | ~ spl8_51
    | ~ spl8_52
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1387,f189])).

fof(f189,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl8_27
  <=> ! [X1,X0] : ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f1387,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl8_51
    | ~ spl8_52
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1379,f379])).

fof(f379,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl8_52
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f1379,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl8_51
    | ~ spl8_124 ),
    inference(resolution,[],[f1262,f375])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),sK1)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),X0)
        | k7_relat_1(sK1,X1) = X0 )
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl8_51
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),sK1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),X0)
        | k7_relat_1(sK1,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f1262,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),X0),sK1)
    | ~ spl8_124 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1261,plain,
    ( spl8_124
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f1263,plain,
    ( spl8_124
    | ~ spl8_15
    | spl8_118 ),
    inference(avatar_split_clause,[],[f1227,f1209,f116,f1261])).

fof(f116,plain,
    ( spl8_15
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f1209,plain,
    ( spl8_118
  <=> r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f1227,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),X0),sK1)
    | ~ spl8_15
    | spl8_118 ),
    inference(resolution,[],[f1210,f117])).

fof(f117,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X2,X3),X0) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f1210,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_relat_1(sK1))
    | spl8_118 ),
    inference(avatar_component_clause,[],[f1209])).

fof(f1211,plain,
    ( ~ spl8_118
    | spl8_3
    | ~ spl8_47
    | ~ spl8_114 ),
    inference(avatar_split_clause,[],[f1203,f1150,f347,f66,f1209])).

fof(f347,plain,
    ( spl8_47
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | r2_hidden(sK2(sK1,X0,k1_xboole_0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f1203,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_relat_1(sK1))
    | spl8_3
    | ~ spl8_47
    | ~ spl8_114 ),
    inference(subsumption_resolution,[],[f1197,f72])).

fof(f1197,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_relat_1(sK1))
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl8_47
    | ~ spl8_114 ),
    inference(resolution,[],[f1151,f348])).

fof(f348,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK1,X0,k1_xboole_0),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f347])).

fof(f1166,plain,
    ( ~ spl8_116
    | spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f1158,f92,f69,f1164])).

fof(f69,plain,
    ( spl8_4
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f92,plain,
    ( spl8_9
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f1158,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f73,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f73,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1152,plain,
    ( spl8_114
    | ~ spl8_17
    | ~ spl8_113 ),
    inference(avatar_split_clause,[],[f1143,f1139,f134,f1150])).

fof(f134,plain,
    ( spl8_17
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f1143,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl8_17
    | ~ spl8_113 ),
    inference(resolution,[],[f1140,f135])).

fof(f135,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1140,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f1141,plain,
    ( spl8_113
    | ~ spl8_1
    | ~ spl8_16
    | ~ spl8_27
    | ~ spl8_35
    | ~ spl8_57
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f548,f524,f420,f257,f188,f124,f58,f1139])).

fof(f124,plain,
    ( spl8_16
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f257,plain,
    ( spl8_35
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f420,plain,
    ( spl8_57
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f524,plain,
    ( spl8_68
  <=> ! [X9,X11,X8,X10] :
        ( ~ r2_hidden(X8,X9)
        | r2_hidden(X8,k3_xboole_0(k1_relat_1(X10),X9))
        | ~ r2_hidden(k4_tarski(X8,X11),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f548,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl8_1
    | ~ spl8_16
    | ~ spl8_27
    | ~ spl8_35
    | ~ spl8_57
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f544,f439])).

fof(f439,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl8_1
    | ~ spl8_27
    | ~ spl8_35
    | ~ spl8_57 ),
    inference(subsumption_resolution,[],[f438,f59])).

fof(f438,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl8_27
    | ~ spl8_35
    | ~ spl8_57 ),
    inference(subsumption_resolution,[],[f436,f189])).

fof(f436,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl8_35
    | ~ spl8_57 ),
    inference(superposition,[],[f258,f421])).

fof(f421,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f420])).

fof(f258,plain,
    ( ! [X4,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f257])).

fof(f544,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl8_16
    | ~ spl8_68 ),
    inference(superposition,[],[f525,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f525,plain,
    ( ! [X10,X8,X11,X9] :
        ( r2_hidden(X8,k3_xboole_0(k1_relat_1(X10),X9))
        | ~ r2_hidden(X8,X9)
        | ~ r2_hidden(k4_tarski(X8,X11),X10) )
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f524])).

fof(f556,plain,
    ( spl8_70
    | ~ spl8_7
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f261,f257,f84,f554])).

fof(f84,plain,
    ( spl8_7
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f261,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ r2_hidden(X5,X6)
        | ~ r2_hidden(k4_tarski(X5,X7),X8)
        | ~ v1_relat_1(X8)
        | ~ v1_xboole_0(k7_relat_1(X8,X6)) )
    | ~ spl8_7
    | ~ spl8_35 ),
    inference(resolution,[],[f258,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f526,plain,
    ( spl8_68
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f148,f142,f116,f524])).

fof(f142,plain,
    ( spl8_19
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f148,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ r2_hidden(X8,X9)
        | r2_hidden(X8,k3_xboole_0(k1_relat_1(X10),X9))
        | ~ r2_hidden(k4_tarski(X8,X11),X10) )
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(resolution,[],[f143,f117])).

fof(f143,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X0)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X3,k3_xboole_0(X0,X1)) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f142])).

fof(f517,plain,
    ( spl8_66
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f231,f184,f84,f515])).

fof(f184,plain,
    ( spl8_26
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK7(X0,X1,X2),X1)
        | r2_hidden(sK7(X0,X1,X2),X2)
        | k3_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f231,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(sK7(X4,X5,X6),X5)
        | k3_xboole_0(X4,X5) = X6
        | ~ v1_xboole_0(X6) )
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(resolution,[],[f185,f85])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK7(X0,X1,X2),X2)
        | r2_hidden(sK7(X0,X1,X2),X1)
        | k3_xboole_0(X0,X1) = X2 )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f184])).

fof(f499,plain,
    ( spl8_65
    | ~ spl8_7
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f225,f175,f84,f497])).

fof(f175,plain,
    ( spl8_25
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK7(X0,X1,X2),X0)
        | r2_hidden(sK7(X0,X1,X2),X2)
        | k3_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f225,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(sK7(X4,X5,X6),X4)
        | k3_xboole_0(X4,X5) = X6
        | ~ v1_xboole_0(X6) )
    | ~ spl8_7
    | ~ spl8_25 ),
    inference(resolution,[],[f176,f85])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK7(X0,X1,X2),X2)
        | r2_hidden(sK7(X0,X1,X2),X0)
        | k3_xboole_0(X0,X1) = X2 )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f175])).

fof(f422,plain,
    ( spl8_57
    | ~ spl8_2
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f409,f398,f62,f420])).

fof(f398,plain,
    ( spl8_54
  <=> ! [X2] :
        ( k1_xboole_0 = k7_relat_1(sK1,X2)
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f409,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_54 ),
    inference(resolution,[],[f399,f63])).

fof(f399,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | k1_xboole_0 = k7_relat_1(sK1,X2) )
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f398])).

fof(f400,plain,
    ( spl8_54
    | ~ spl8_7
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f356,f347,f84,f398])).

fof(f356,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k7_relat_1(sK1,X2)
        | ~ v1_xboole_0(X2) )
    | ~ spl8_7
    | ~ spl8_47 ),
    inference(resolution,[],[f348,f85])).

fof(f380,plain,
    ( spl8_52
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f372,f363,f88,f58,f378])).

fof(f88,plain,
    ( spl8_8
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f363,plain,
    ( spl8_49
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f372,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_49 ),
    inference(subsumption_resolution,[],[f371,f59])).

fof(f371,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl8_8
    | ~ spl8_49 ),
    inference(superposition,[],[f89,f364])).

fof(f364,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_relat_1(k1_xboole_0))
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f363])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f376,plain,
    ( spl8_51
    | ~ spl8_1
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f301,f298,f58,f374])).

fof(f298,plain,
    ( spl8_40
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
        | k7_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f301,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),sK1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),X0)
        | k7_relat_1(sK1,X1) = X0 )
    | ~ spl8_1
    | ~ spl8_40 ),
    inference(resolution,[],[f299,f59])).

fof(f299,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
        | k7_relat_1(X0,X1) = X2 )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f298])).

fof(f365,plain,
    ( spl8_49
    | ~ spl8_24
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f357,f347,f169,f363])).

fof(f169,plain,
    ( spl8_24
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f357,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_relat_1(k1_xboole_0))
    | ~ spl8_24
    | ~ spl8_47 ),
    inference(resolution,[],[f348,f170])).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f169])).

fof(f349,plain,
    ( spl8_47
    | ~ spl8_2
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f341,f333,f62,f347])).

fof(f333,plain,
    ( spl8_44
  <=> ! [X1,X2] :
        ( r2_hidden(sK2(sK1,X1,X2),X1)
        | k7_relat_1(sK1,X1) = X2
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f341,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | r2_hidden(sK2(sK1,X0,k1_xboole_0),X0) )
    | ~ spl8_2
    | ~ spl8_44 ),
    inference(resolution,[],[f334,f63])).

fof(f334,plain,
    ( ! [X2,X1] :
        ( ~ v1_xboole_0(X2)
        | k7_relat_1(sK1,X1) = X2
        | r2_hidden(sK2(sK1,X1,X2),X1) )
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( spl8_44
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f331,f320,f84,f76,f333])).

fof(f76,plain,
    ( spl8_5
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f320,plain,
    ( spl8_43
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK2(sK1,X1,X0),X1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),X0)
        | k7_relat_1(sK1,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f331,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK2(sK1,X1,X2),X1)
        | k7_relat_1(sK1,X1) = X2
        | ~ v1_xboole_0(X2) )
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f329,f85])).

fof(f329,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK2(sK1,X1,X2),X1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X2),sK3(sK1,X1,X2)),X2)
        | k7_relat_1(sK1,X1) = X2
        | ~ v1_xboole_0(X2) )
    | ~ spl8_5
    | ~ spl8_43 ),
    inference(resolution,[],[f321,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK2(sK1,X1,X0),X1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),X0)
        | k7_relat_1(sK1,X1) = X0 )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f320])).

fof(f322,plain,
    ( spl8_43
    | ~ spl8_1
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f290,f284,f58,f320])).

fof(f284,plain,
    ( spl8_38
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
        | k7_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK2(sK1,X1,X0),X1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,X0),sK3(sK1,X1,X0)),X0)
        | k7_relat_1(sK1,X1) = X0 )
    | ~ spl8_1
    | ~ spl8_38 ),
    inference(resolution,[],[f285,f59])).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
        | k7_relat_1(X0,X1) = X2 )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f284])).

fof(f300,plain,(
    spl8_40 ),
    inference(avatar_split_clause,[],[f28,f298])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f286,plain,(
    spl8_38 ),
    inference(avatar_split_clause,[],[f27,f284])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f259,plain,
    ( spl8_35
    | ~ spl8_8
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f251,f248,f88,f257])).

fof(f248,plain,
    ( spl8_33
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f251,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) )
    | ~ spl8_8
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f249,f89])).

fof(f249,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,(
    spl8_33 ),
    inference(avatar_split_clause,[],[f49,f248])).

fof(f49,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f190,plain,
    ( spl8_27
    | ~ spl8_15
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f178,f169,f116,f188])).

fof(f178,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
    | ~ spl8_15
    | ~ spl8_24 ),
    inference(resolution,[],[f170,f117])).

fof(f186,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f45,f184])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f177,plain,(
    spl8_25 ),
    inference(avatar_split_clause,[],[f44,f175])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f171,plain,
    ( spl8_24
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f163,f151,f62,f169])).

fof(f151,plain,
    ( spl8_20
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f163,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(resolution,[],[f152,f63])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( spl8_20
    | ~ spl8_7
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f145,f134,f84,f151])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl8_7
    | ~ spl8_17 ),
    inference(resolution,[],[f135,f85])).

fof(f144,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f54,f142])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f136,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f52,f134])).

fof(f52,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f126,plain,
    ( spl8_16
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f119,f104,f69,f124])).

fof(f104,plain,
    ( spl8_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f119,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(resolution,[],[f105,f70])).

fof(f70,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f118,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f53,f116])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f106,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f37,f104])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f102,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f36,f100])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f35,f92])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f90,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f86,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f78,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f25,f76])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f74,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f22,f69,f66])).

fof(f22,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f71,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f21,f69,f66])).

fof(f21,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f60,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
