%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 276 expanded)
%              Number of leaves         :   52 ( 135 expanded)
%              Depth                    :    7
%              Number of atoms          :  420 ( 640 expanded)
%              Number of equality atoms :   67 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2552,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f82,f86,f90,f94,f98,f108,f119,f125,f129,f145,f153,f163,f177,f218,f292,f341,f464,f746,f854,f904,f1135,f1331,f1496,f1624,f1653,f1905,f1966,f1981,f1990,f2147,f2547])).

fof(f2547,plain,
    ( spl5_3
    | ~ spl5_7
    | ~ spl5_136 ),
    inference(avatar_contradiction_clause,[],[f2546])).

fof(f2546,plain,
    ( $false
    | spl5_3
    | ~ spl5_7
    | ~ spl5_136 ),
    inference(subsumption_resolution,[],[f2523,f77])).

fof(f77,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f2523,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_7
    | ~ spl5_136 ),
    inference(resolution,[],[f2146,f93])).

fof(f93,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2146,plain,
    ( ! [X11] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X11)
        | r1_tarski(sK0,X11) )
    | ~ spl5_136 ),
    inference(avatar_component_clause,[],[f2145])).

fof(f2145,plain,
    ( spl5_136
  <=> ! [X11] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X11)
        | r1_tarski(sK0,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f2147,plain,
    ( spl5_136
    | ~ spl5_32
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f1923,f1902,f290,f2145])).

fof(f290,plain,
    ( spl5_32
  <=> ! [X3,X2,X4] :
        ( ~ r1_tarski(k2_xboole_0(X3,X2),X4)
        | r1_tarski(X2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f1902,plain,
    ( spl5_123
  <=> k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f1923,plain,
    ( ! [X11] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X11)
        | r1_tarski(sK0,X11) )
    | ~ spl5_32
    | ~ spl5_123 ),
    inference(superposition,[],[f291,f1904])).

fof(f1904,plain,
    ( k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f1902])).

fof(f291,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(X3,X2),X4)
        | r1_tarski(X2,X4) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f290])).

fof(f1990,plain,
    ( spl5_4
    | ~ spl5_10
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f1983,f1978,f106,f79])).

fof(f79,plain,
    ( spl5_4
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f106,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1978,plain,
    ( spl5_126
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f1983,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_10
    | ~ spl5_126 ),
    inference(resolution,[],[f1980,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1980,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f1978])).

fof(f1981,plain,
    ( spl5_126
    | ~ spl5_119
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f1973,f1964,f1651,f1978])).

fof(f1651,plain,
    ( spl5_119
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f1964,plain,
    ( spl5_124
  <=> ! [X5] : r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f1973,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl5_119
    | ~ spl5_124 ),
    inference(superposition,[],[f1965,f1652])).

fof(f1652,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4
    | ~ spl5_119 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f1965,plain,
    ( ! [X5] : r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f1964])).

fof(f1966,plain,
    ( spl5_124
    | ~ spl5_21
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f1915,f1902,f175,f1964])).

fof(f175,plain,
    ( spl5_21
  <=> ! [X3,X2,X4] : r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1915,plain,
    ( ! [X5] : r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_21
    | ~ spl5_123 ),
    inference(superposition,[],[f176,f1904])).

fof(f176,plain,
    ( ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X2)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1905,plain,
    ( spl5_123
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f1645,f1621,f216,f88,f1902])).

fof(f88,plain,
    ( spl5_6
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f216,plain,
    ( spl5_24
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1621,plain,
    ( spl5_118
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f1645,plain,
    ( k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f1628,f89])).

fof(f89,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1628,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl5_24
    | ~ spl5_118 ),
    inference(superposition,[],[f217,f1623])).

fof(f1623,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f217,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1653,plain,
    ( spl5_119
    | ~ spl5_5
    | ~ spl5_78
    | ~ spl5_97
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1576,f1494,f1329,f902,f84,f1651])).

fof(f84,plain,
    ( spl5_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f902,plain,
    ( spl5_78
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1329,plain,
    ( spl5_97
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f1494,plain,
    ( spl5_110
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f1576,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4
    | ~ spl5_5
    | ~ spl5_78
    | ~ spl5_97
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1560,f1563])).

fof(f1563,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_5
    | ~ spl5_78
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1551,f903])).

fof(f903,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f902])).

fof(f1551,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl5_5
    | ~ spl5_110 ),
    inference(superposition,[],[f1495,f85])).

fof(f85,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1495,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f1494])).

fof(f1560,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k1_xboole_0)
    | ~ spl5_97
    | ~ spl5_110 ),
    inference(superposition,[],[f1495,f1330])).

fof(f1330,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f1624,plain,
    ( spl5_118
    | ~ spl5_5
    | ~ spl5_78
    | ~ spl5_83
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1599,f1494,f1132,f902,f84,f1621])).

fof(f1132,plain,
    ( spl5_83
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f1599,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_5
    | ~ spl5_78
    | ~ spl5_83
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1562,f1564])).

fof(f1564,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl5_5
    | ~ spl5_78
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1552,f85])).

fof(f1552,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl5_78
    | ~ spl5_110 ),
    inference(superposition,[],[f1495,f903])).

fof(f1562,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)
    | ~ spl5_83
    | ~ spl5_110 ),
    inference(superposition,[],[f1495,f1134])).

fof(f1134,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f1496,plain,(
    spl5_110 ),
    inference(avatar_split_clause,[],[f58,f1494])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1331,plain,
    ( spl5_97
    | ~ spl5_12
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f1304,f744,f117,f1329])).

fof(f117,plain,
    ( spl5_12
  <=> ! [X1,X2] : r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f744,plain,
    ( spl5_70
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f1304,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))
    | ~ spl5_12
    | ~ spl5_70 ),
    inference(resolution,[],[f745,f118])).

fof(f118,plain,
    ( ! [X2,X1] : r1_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f745,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f744])).

fof(f1135,plain,
    ( spl5_83
    | ~ spl5_2
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f897,f462,f70,f1132])).

fof(f70,plain,
    ( spl5_2
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f462,plain,
    ( spl5_46
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f897,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl5_2
    | ~ spl5_46 ),
    inference(resolution,[],[f463,f72])).

fof(f72,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f463,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f462])).

fof(f904,plain,
    ( spl5_78
    | ~ spl5_13
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f855,f852,f123,f902])).

fof(f123,plain,
    ( spl5_13
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f852,plain,
    ( spl5_76
  <=> ! [X1,X0] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f855,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl5_13
    | ~ spl5_76 ),
    inference(resolution,[],[f853,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f853,plain,
    ( ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f852])).

fof(f854,plain,
    ( spl5_76
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f850,f339,f84,f66,f852])).

fof(f66,plain,
    ( spl5_1
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f339,plain,
    ( spl5_35
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f850,plain,
    ( ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f849,f67])).

fof(f67,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f849,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl5_5
    | ~ spl5_35 ),
    inference(superposition,[],[f340,f85])).

fof(f340,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f339])).

fof(f746,plain,(
    spl5_70 ),
    inference(avatar_split_clause,[],[f64,f744])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f464,plain,(
    spl5_46 ),
    inference(avatar_split_clause,[],[f62,f462])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f341,plain,(
    spl5_35 ),
    inference(avatar_split_clause,[],[f60,f339])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f292,plain,
    ( spl5_32
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f208,f151,f127,f290])).

fof(f127,plain,
    ( spl5_14
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f151,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f208,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(X3,X2),X4)
        | r1_tarski(X2,X4) )
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(superposition,[],[f152,f128])).

fof(f128,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f218,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f46,f216])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f177,plain,
    ( spl5_21
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f167,f161,f127,f175])).

fof(f161,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] : r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f167,plain,
    ( ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X2)
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(superposition,[],[f162,f128])).

fof(f162,plain,
    ( ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl5_19
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f154,f143,f96,f161])).

fof(f96,plain,
    ( spl5_8
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f143,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f154,plain,
    ( ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(resolution,[],[f144,f97])).

fof(f97,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f153,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f57,f151])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f145,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f129,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f43,f127])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f125,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f40,f123])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f119,plain,
    ( spl5_12
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f110,f106,f96,f117])).

fof(f110,plain,
    ( ! [X2,X1] : r1_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(resolution,[],[f107,f97])).

fof(f108,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f51,f106])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f98,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f42,f96])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f94,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f41,f92])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f90,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f86,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f84])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f82,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f36,f79,f75])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f73,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (7446)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (7454)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (7444)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (7439)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (7447)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (7440)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (7456)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (7442)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (7449)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (7445)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (7441)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (7446)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f2552,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f68,f73,f82,f86,f90,f94,f98,f108,f119,f125,f129,f145,f153,f163,f177,f218,f292,f341,f464,f746,f854,f904,f1135,f1331,f1496,f1624,f1653,f1905,f1966,f1981,f1990,f2147,f2547])).
% 0.21/0.48  fof(f2547,plain,(
% 0.21/0.48    spl5_3 | ~spl5_7 | ~spl5_136),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f2546])).
% 0.21/0.48  fof(f2546,plain,(
% 0.21/0.48    $false | (spl5_3 | ~spl5_7 | ~spl5_136)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2523,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl5_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f2523,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | (~spl5_7 | ~spl5_136)),
% 0.21/0.48    inference(resolution,[],[f2146,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl5_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f2146,plain,(
% 0.21/0.48    ( ! [X11] : (~r1_tarski(k4_xboole_0(sK1,sK2),X11) | r1_tarski(sK0,X11)) ) | ~spl5_136),
% 0.21/0.48    inference(avatar_component_clause,[],[f2145])).
% 0.21/0.48  fof(f2145,plain,(
% 0.21/0.48    spl5_136 <=> ! [X11] : (~r1_tarski(k4_xboole_0(sK1,sK2),X11) | r1_tarski(sK0,X11))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).
% 0.21/0.48  fof(f2147,plain,(
% 0.21/0.48    spl5_136 | ~spl5_32 | ~spl5_123),
% 0.21/0.48    inference(avatar_split_clause,[],[f1923,f1902,f290,f2145])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    spl5_32 <=> ! [X3,X2,X4] : (~r1_tarski(k2_xboole_0(X3,X2),X4) | r1_tarski(X2,X4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.48  fof(f1902,plain,(
% 0.21/0.48    spl5_123 <=> k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 0.21/0.48  fof(f1923,plain,(
% 0.21/0.48    ( ! [X11] : (~r1_tarski(k4_xboole_0(sK1,sK2),X11) | r1_tarski(sK0,X11)) ) | (~spl5_32 | ~spl5_123)),
% 0.21/0.48    inference(superposition,[],[f291,f1904])).
% 0.21/0.48  fof(f1904,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl5_123),
% 0.21/0.48    inference(avatar_component_clause,[],[f1902])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (~r1_tarski(k2_xboole_0(X3,X2),X4) | r1_tarski(X2,X4)) ) | ~spl5_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f290])).
% 0.21/0.48  fof(f1990,plain,(
% 0.21/0.48    spl5_4 | ~spl5_10 | ~spl5_126),
% 0.21/0.48    inference(avatar_split_clause,[],[f1983,f1978,f106,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl5_4 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl5_10 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f1978,plain,(
% 0.21/0.48    spl5_126 <=> r1_xboole_0(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).
% 0.21/0.48  fof(f1983,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK2) | (~spl5_10 | ~spl5_126)),
% 0.21/0.48    inference(resolution,[],[f1980,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl5_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f1980,plain,(
% 0.21/0.49    r1_xboole_0(sK2,sK0) | ~spl5_126),
% 0.21/0.49    inference(avatar_component_clause,[],[f1978])).
% 0.21/0.49  fof(f1981,plain,(
% 0.21/0.49    spl5_126 | ~spl5_119 | ~spl5_124),
% 0.21/0.49    inference(avatar_split_clause,[],[f1973,f1964,f1651,f1978])).
% 0.21/0.49  fof(f1651,plain,(
% 0.21/0.49    spl5_119 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).
% 0.21/0.49  fof(f1964,plain,(
% 0.21/0.49    spl5_124 <=> ! [X5] : r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(sK1,sK2)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 0.21/0.49  fof(f1973,plain,(
% 0.21/0.49    r1_xboole_0(sK2,sK0) | (~spl5_119 | ~spl5_124)),
% 0.21/0.49    inference(superposition,[],[f1965,f1652])).
% 0.21/0.49  fof(f1652,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) ) | ~spl5_119),
% 0.21/0.49    inference(avatar_component_clause,[],[f1651])).
% 0.21/0.49  fof(f1965,plain,(
% 0.21/0.49    ( ! [X5] : (r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(sK1,sK2)),sK0)) ) | ~spl5_124),
% 0.21/0.49    inference(avatar_component_clause,[],[f1964])).
% 0.21/0.49  fof(f1966,plain,(
% 0.21/0.49    spl5_124 | ~spl5_21 | ~spl5_123),
% 0.21/0.49    inference(avatar_split_clause,[],[f1915,f1902,f175,f1964])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl5_21 <=> ! [X3,X2,X4] : r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.49  fof(f1915,plain,(
% 0.21/0.49    ( ! [X5] : (r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(sK1,sK2)),sK0)) ) | (~spl5_21 | ~spl5_123)),
% 0.21/0.49    inference(superposition,[],[f176,f1904])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X2)) ) | ~spl5_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f1905,plain,(
% 0.21/0.49    spl5_123 | ~spl5_6 | ~spl5_24 | ~spl5_118),
% 0.21/0.49    inference(avatar_split_clause,[],[f1645,f1621,f216,f88,f1902])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl5_6 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl5_24 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.49  fof(f1621,plain,(
% 0.21/0.49    spl5_118 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 0.21/0.49  fof(f1645,plain,(
% 0.21/0.49    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) | (~spl5_6 | ~spl5_24 | ~spl5_118)),
% 0.21/0.49    inference(forward_demodulation,[],[f1628,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f1628,plain,(
% 0.21/0.49    k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) | (~spl5_24 | ~spl5_118)),
% 0.21/0.49    inference(superposition,[],[f217,f1623])).
% 0.21/0.49  fof(f1623,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl5_118),
% 0.21/0.49    inference(avatar_component_clause,[],[f1621])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl5_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f216])).
% 0.21/0.49  fof(f1653,plain,(
% 0.21/0.49    spl5_119 | ~spl5_5 | ~spl5_78 | ~spl5_97 | ~spl5_110),
% 0.21/0.49    inference(avatar_split_clause,[],[f1576,f1494,f1329,f902,f84,f1651])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl5_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f902,plain,(
% 0.21/0.49    spl5_78 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 0.21/0.49  fof(f1329,plain,(
% 0.21/0.49    spl5_97 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 0.21/0.49  fof(f1494,plain,(
% 0.21/0.49    spl5_110 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 0.21/0.49  fof(f1576,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) ) | (~spl5_5 | ~spl5_78 | ~spl5_97 | ~spl5_110)),
% 0.21/0.49    inference(forward_demodulation,[],[f1560,f1563])).
% 0.21/0.49  fof(f1563,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl5_5 | ~spl5_78 | ~spl5_110)),
% 0.21/0.49    inference(forward_demodulation,[],[f1551,f903])).
% 0.21/0.49  fof(f903,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl5_78),
% 0.21/0.49    inference(avatar_component_clause,[],[f902])).
% 0.21/0.49  fof(f1551,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl5_5 | ~spl5_110)),
% 0.21/0.49    inference(superposition,[],[f1495,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f1495,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl5_110),
% 0.21/0.49    inference(avatar_component_clause,[],[f1494])).
% 0.21/0.49  fof(f1560,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k1_xboole_0)) ) | (~spl5_97 | ~spl5_110)),
% 0.21/0.49    inference(superposition,[],[f1495,f1330])).
% 0.21/0.49  fof(f1330,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) ) | ~spl5_97),
% 0.21/0.49    inference(avatar_component_clause,[],[f1329])).
% 0.21/0.49  fof(f1624,plain,(
% 0.21/0.49    spl5_118 | ~spl5_5 | ~spl5_78 | ~spl5_83 | ~spl5_110),
% 0.21/0.49    inference(avatar_split_clause,[],[f1599,f1494,f1132,f902,f84,f1621])).
% 0.21/0.49  fof(f1132,plain,(
% 0.21/0.49    spl5_83 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 0.21/0.49  fof(f1599,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl5_5 | ~spl5_78 | ~spl5_83 | ~spl5_110)),
% 0.21/0.49    inference(forward_demodulation,[],[f1562,f1564])).
% 0.21/0.49  fof(f1564,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | (~spl5_5 | ~spl5_78 | ~spl5_110)),
% 0.21/0.49    inference(forward_demodulation,[],[f1552,f85])).
% 0.21/0.49  fof(f1552,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl5_78 | ~spl5_110)),
% 0.21/0.49    inference(superposition,[],[f1495,f903])).
% 0.21/0.49  fof(f1562,plain,(
% 0.21/0.49    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) | (~spl5_83 | ~spl5_110)),
% 0.21/0.49    inference(superposition,[],[f1495,f1134])).
% 0.21/0.49  fof(f1134,plain,(
% 0.21/0.49    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl5_83),
% 0.21/0.49    inference(avatar_component_clause,[],[f1132])).
% 0.21/0.49  fof(f1496,plain,(
% 0.21/0.49    spl5_110),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f1494])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f45,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.49  fof(f1331,plain,(
% 0.21/0.49    spl5_97 | ~spl5_12 | ~spl5_70),
% 0.21/0.49    inference(avatar_split_clause,[],[f1304,f744,f117,f1329])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl5_12 <=> ! [X1,X2] : r1_xboole_0(X1,k4_xboole_0(X2,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.49  fof(f744,plain,(
% 0.21/0.49    spl5_70 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 0.21/0.49  fof(f1304,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) ) | (~spl5_12 | ~spl5_70)),
% 0.21/0.49    inference(resolution,[],[f745,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X2,X1] : (r1_xboole_0(X1,k4_xboole_0(X2,X1))) ) | ~spl5_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f745,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl5_70),
% 0.21/0.49    inference(avatar_component_clause,[],[f744])).
% 0.21/0.49  fof(f1135,plain,(
% 0.21/0.49    spl5_83 | ~spl5_2 | ~spl5_46),
% 0.21/0.49    inference(avatar_split_clause,[],[f897,f462,f70,f1132])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl5_2 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    spl5_46 <=> ! [X1,X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.21/0.49  fof(f897,plain,(
% 0.21/0.49    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | (~spl5_2 | ~spl5_46)),
% 0.21/0.49    inference(resolution,[],[f463,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f463,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl5_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f462])).
% 0.21/0.49  fof(f904,plain,(
% 0.21/0.49    spl5_78 | ~spl5_13 | ~spl5_76),
% 0.21/0.49    inference(avatar_split_clause,[],[f855,f852,f123,f902])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl5_13 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.49  fof(f852,plain,(
% 0.21/0.49    spl5_76 <=> ! [X1,X0] : ~r2_hidden(X1,k4_xboole_0(X0,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 0.21/0.49  fof(f855,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl5_13 | ~spl5_76)),
% 0.21/0.49    inference(resolution,[],[f853,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f853,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) ) | ~spl5_76),
% 0.21/0.49    inference(avatar_component_clause,[],[f852])).
% 0.21/0.49  fof(f854,plain,(
% 0.21/0.49    spl5_76 | ~spl5_1 | ~spl5_5 | ~spl5_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f850,f339,f84,f66,f852])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl5_1 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    spl5_35 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.49  fof(f850,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) ) | (~spl5_1 | ~spl5_5 | ~spl5_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f849,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f849,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl5_5 | ~spl5_35)),
% 0.21/0.49    inference(superposition,[],[f340,f85])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) ) | ~spl5_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f339])).
% 0.21/0.49  fof(f746,plain,(
% 0.21/0.49    spl5_70),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f744])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f52,f47])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.49  fof(f464,plain,(
% 0.21/0.49    spl5_46),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f462])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f50,f47])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f341,plain,(
% 0.21/0.49    spl5_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f339])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f49,f47])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    spl5_32 | ~spl5_14 | ~spl5_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f208,f151,f127,f290])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl5_14 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl5_18 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (~r1_tarski(k2_xboole_0(X3,X2),X4) | r1_tarski(X2,X4)) ) | (~spl5_14 | ~spl5_18)),
% 0.21/0.49    inference(superposition,[],[f152,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl5_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f151])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl5_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f216])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl5_21 | ~spl5_14 | ~spl5_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f161,f127,f175])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl5_19 <=> ! [X1,X0,X2] : r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X2)) ) | (~spl5_14 | ~spl5_19)),
% 0.21/0.49    inference(superposition,[],[f162,f128])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) ) | ~spl5_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl5_19 | ~spl5_8 | ~spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f154,f143,f96,f161])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl5_8 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl5_16 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) ) | (~spl5_8 | ~spl5_16)),
% 0.21/0.49    inference(resolution,[],[f144,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) ) | ~spl5_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl5_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f151])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f143])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl5_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f127])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl5_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f123])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl5_12 | ~spl5_8 | ~spl5_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f110,f106,f96,f117])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X2,X1] : (r1_xboole_0(X1,k4_xboole_0(X2,X1))) ) | (~spl5_8 | ~spl5_10)),
% 0.21/0.49    inference(resolution,[],[f107,f97])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl5_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f106])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl5_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f96])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f92])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl5_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f88])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f84])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl5_3 | ~spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f79,f75])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f18])).
% 0.21/0.49  fof(f18,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f70])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f66])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (7446)------------------------------
% 0.21/0.49  % (7446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7446)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (7446)Memory used [KB]: 7547
% 0.21/0.49  % (7446)Time elapsed: 0.043 s
% 0.21/0.49  % (7446)------------------------------
% 0.21/0.49  % (7446)------------------------------
% 0.21/0.49  % (7450)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (7443)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (7437)Success in time 0.129 s
%------------------------------------------------------------------------------
