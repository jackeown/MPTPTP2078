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
% DateTime   : Thu Dec  3 12:43:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 265 expanded)
%              Number of leaves         :   44 ( 120 expanded)
%              Depth                    :    7
%              Number of atoms          :  459 ( 786 expanded)
%              Number of equality atoms :   39 (  72 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f88,f96,f100,f104,f119,f124,f132,f136,f140,f144,f151,f194,f212,f224,f414,f654,f713,f736,f834,f915,f1149,f1178,f1375,f1483,f1537,f2119,f2265])).

fof(f2265,plain,
    ( ~ spl6_4
    | ~ spl6_44
    | ~ spl6_55
    | ~ spl6_62
    | spl6_89
    | ~ spl6_118 ),
    inference(avatar_contradiction_clause,[],[f2264])).

fof(f2264,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_44
    | ~ spl6_55
    | ~ spl6_62
    | spl6_89
    | ~ spl6_118 ),
    inference(subsumption_resolution,[],[f1460,f2247])).

fof(f2247,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl6_4
    | ~ spl6_55
    | ~ spl6_118 ),
    inference(unit_resulting_resolution,[],[f83,f2118,f735])).

fof(f735,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f734])).

fof(f734,plain,
    ( spl6_55
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f2118,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl6_118 ),
    inference(avatar_component_clause,[],[f2116])).

fof(f2116,plain,
    ( spl6_118
  <=> r1_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f83,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1460,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl6_44
    | ~ spl6_62
    | spl6_89 ),
    inference(unit_resulting_resolution,[],[f413,f1452,f914])).

fof(f914,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | ~ r1_xboole_0(X2,X3)
        | k1_xboole_0 = X2 )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f913])).

fof(f913,plain,
    ( spl6_62
  <=> ! [X3,X2] :
        ( k1_xboole_0 = X2
        | ~ r1_xboole_0(X2,X3)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f1452,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl6_89 ),
    inference(avatar_component_clause,[],[f1450])).

fof(f1450,plain,
    ( spl6_89
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f413,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl6_44
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f2119,plain,
    ( spl6_118
    | ~ spl6_49
    | spl6_78 ),
    inference(avatar_split_clause,[],[f1202,f1175,f652,f2116])).

fof(f652,plain,
    ( spl6_49
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | r1_xboole_0(X1,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f1175,plain,
    ( spl6_78
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1202,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl6_49
    | spl6_78 ),
    inference(unit_resulting_resolution,[],[f1177,f653])).

fof(f653,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,k1_tarski(X0))
        | r2_hidden(X0,X1) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f652])).

fof(f1177,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl6_78 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1537,plain,
    ( spl6_20
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(avatar_contradiction_clause,[],[f1535])).

fof(f1535,plain,
    ( $false
    | spl6_20
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f1380,f664])).

fof(f664,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f663])).

fof(f663,plain,
    ( spl6_51
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f1380,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_20
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(unit_resulting_resolution,[],[f193,f1374,f1148])).

fof(f1148,plain,
    ( ! [X21,X19,X20] :
        ( k1_xboole_0 != k3_xboole_0(X19,X21)
        | r1_xboole_0(X19,k2_xboole_0(X20,X21))
        | ~ r1_xboole_0(X19,X20) )
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f1147,plain,
    ( spl6_76
  <=> ! [X20,X19,X21] :
        ( k1_xboole_0 != k3_xboole_0(X19,X21)
        | r1_xboole_0(X19,k2_xboole_0(X20,X21))
        | ~ r1_xboole_0(X19,X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f1374,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1372,plain,
    ( spl6_85
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f193,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_20
  <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1483,plain,
    ( spl6_51
    | ~ spl6_58
    | ~ spl6_89 ),
    inference(avatar_contradiction_clause,[],[f1482])).

fof(f1482,plain,
    ( $false
    | spl6_51
    | ~ spl6_58
    | ~ spl6_89 ),
    inference(subsumption_resolution,[],[f839,f1451])).

fof(f1451,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f1450])).

fof(f839,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl6_51
    | ~ spl6_58 ),
    inference(unit_resulting_resolution,[],[f665,f833])).

fof(f833,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 != k3_xboole_0(X5,X4)
        | r1_xboole_0(X4,X5) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f832])).

fof(f832,plain,
    ( spl6_58
  <=> ! [X5,X4] :
        ( k1_xboole_0 != k3_xboole_0(X5,X4)
        | r1_xboole_0(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f665,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_51 ),
    inference(avatar_component_clause,[],[f663])).

fof(f1375,plain,
    ( spl6_85
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f174,f138,f121,f1372])).

fof(f121,plain,
    ( spl6_13
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f138,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f174,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f123,f139])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f123,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1178,plain,
    ( ~ spl6_78
    | ~ spl6_1
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f205,f149,f121,f66,f1175])).

fof(f66,plain,
    ( spl6_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f149,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f205,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_1
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f123,f68,f150])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f68,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f1149,plain,
    ( spl6_76
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f251,f222,f142,f1147])).

fof(f142,plain,
    ( spl6_18
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f222,plain,
    ( spl6_24
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f251,plain,
    ( ! [X21,X19,X20] :
        ( k1_xboole_0 != k3_xboole_0(X19,X21)
        | r1_xboole_0(X19,k2_xboole_0(X20,X21))
        | ~ r1_xboole_0(X19,X20) )
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(superposition,[],[f143,f223])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f915,plain,
    ( spl6_62
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f175,f138,f134,f913])).

fof(f134,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f175,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = X2
        | ~ r1_xboole_0(X2,X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(superposition,[],[f139,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f834,plain,
    ( spl6_58
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f188,f142,f98,f832])).

fof(f98,plain,
    ( spl6_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f188,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 != k3_xboole_0(X5,X4)
        | r1_xboole_0(X4,X5) )
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(superposition,[],[f143,f99])).

fof(f99,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f736,plain,
    ( spl6_55
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f730,f711,f210,f138,f121,f734])).

fof(f210,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f711,plain,
    ( spl6_54
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f730,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f235,f728])).

fof(f728,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_54 ),
    inference(forward_demodulation,[],[f715,f174])).

fof(f715,plain,
    ( ! [X0] : r1_xboole_0(X0,k3_xboole_0(sK1,sK2))
    | ~ spl6_13
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f123,f712])).

fof(f712,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f711])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(superposition,[],[f211,f139])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | r1_xboole_0(X0,X1) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f713,plain,
    ( spl6_54
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f163,f130,f117,f711])).

fof(f117,plain,
    ( spl6_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f130,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(resolution,[],[f131,f118])).

fof(f118,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f654,plain,
    ( spl6_49
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f147,f102,f94,f652])).

fof(f94,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f102,plain,
    ( spl6_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | r1_xboole_0(X1,k1_tarski(X0)) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f103,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f414,plain,
    ( spl6_44
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f145,f98,f86,f412])).

fof(f86,plain,
    ( spl6_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f145,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(superposition,[],[f87,f99])).

fof(f87,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f224,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f59,f222])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f212,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f60,f210])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f194,plain,
    ( ~ spl6_20
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f105,f94,f76,f191])).

fof(f76,plain,
    ( spl6_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f105,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl6_3
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f78,f95])).

fof(f78,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f151,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f52,f149])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f144,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f57,f142])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f140,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f56,f138])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f54,f134])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f132,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f51,f130])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f124,plain,
    ( spl6_13
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f106,f94,f71,f121])).

fof(f71,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f106,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f73,f95])).

fof(f73,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f119,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f49,f117])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f104,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f100,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f96,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f55,f94])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f88,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f84,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f79,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f42,f76])).

fof(f42,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f41,f71])).

fof(f41,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10649)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (10661)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (10653)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (10652)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (10656)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (10651)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (10648)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (10655)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (10657)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (10660)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (10650)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (10662)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (10659)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (10663)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (10654)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (10664)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (10647)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (10658)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.54  % (10652)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f2267,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f88,f96,f100,f104,f119,f124,f132,f136,f140,f144,f151,f194,f212,f224,f414,f654,f713,f736,f834,f915,f1149,f1178,f1375,f1483,f1537,f2119,f2265])).
% 0.22/0.54  fof(f2265,plain,(
% 0.22/0.54    ~spl6_4 | ~spl6_44 | ~spl6_55 | ~spl6_62 | spl6_89 | ~spl6_118),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f2264])).
% 0.22/0.54  fof(f2264,plain,(
% 0.22/0.54    $false | (~spl6_4 | ~spl6_44 | ~spl6_55 | ~spl6_62 | spl6_89 | ~spl6_118)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1460,f2247])).
% 0.22/0.54  fof(f2247,plain,(
% 0.22/0.54    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl6_4 | ~spl6_55 | ~spl6_118)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f83,f2118,f735])).
% 0.22/0.54  fof(f735,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl6_55),
% 0.22/0.54    inference(avatar_component_clause,[],[f734])).
% 0.22/0.54  fof(f734,plain,(
% 0.22/0.54    spl6_55 <=> ! [X1,X0,X2] : (~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.22/0.54  fof(f2118,plain,(
% 0.22/0.54    r1_xboole_0(sK1,k1_tarski(sK3)) | ~spl6_118),
% 0.22/0.54    inference(avatar_component_clause,[],[f2116])).
% 0.22/0.54  fof(f2116,plain,(
% 0.22/0.54    spl6_118 <=> r1_xboole_0(sK1,k1_tarski(sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl6_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.54  fof(f1460,plain,(
% 0.22/0.54    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl6_44 | ~spl6_62 | spl6_89)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f413,f1452,f914])).
% 0.22/0.54  fof(f914,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) ) | ~spl6_62),
% 0.22/0.54    inference(avatar_component_clause,[],[f913])).
% 0.22/0.54  fof(f913,plain,(
% 0.22/0.54    spl6_62 <=> ! [X3,X2] : (k1_xboole_0 = X2 | ~r1_xboole_0(X2,X3) | ~r1_tarski(X2,X3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.22/0.54  fof(f1452,plain,(
% 0.22/0.54    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl6_89),
% 0.22/0.54    inference(avatar_component_clause,[],[f1450])).
% 0.22/0.54  fof(f1450,plain,(
% 0.22/0.54    spl6_89 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).
% 0.22/0.54  fof(f413,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl6_44),
% 0.22/0.54    inference(avatar_component_clause,[],[f412])).
% 0.22/0.54  fof(f412,plain,(
% 0.22/0.54    spl6_44 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.22/0.54  fof(f2119,plain,(
% 0.22/0.54    spl6_118 | ~spl6_49 | spl6_78),
% 0.22/0.54    inference(avatar_split_clause,[],[f1202,f1175,f652,f2116])).
% 0.22/0.54  fof(f652,plain,(
% 0.22/0.54    spl6_49 <=> ! [X1,X0] : (r2_hidden(X0,X1) | r1_xboole_0(X1,k1_tarski(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.22/0.54  fof(f1175,plain,(
% 0.22/0.54    spl6_78 <=> r2_hidden(sK3,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.22/0.54  fof(f1202,plain,(
% 0.22/0.54    r1_xboole_0(sK1,k1_tarski(sK3)) | (~spl6_49 | spl6_78)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f1177,f653])).
% 0.22/0.54  fof(f653,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,k1_tarski(X0)) | r2_hidden(X0,X1)) ) | ~spl6_49),
% 0.22/0.54    inference(avatar_component_clause,[],[f652])).
% 0.22/0.54  fof(f1177,plain,(
% 0.22/0.54    ~r2_hidden(sK3,sK1) | spl6_78),
% 0.22/0.54    inference(avatar_component_clause,[],[f1175])).
% 0.22/0.54  fof(f1537,plain,(
% 0.22/0.54    spl6_20 | ~spl6_51 | ~spl6_76 | ~spl6_85),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1535])).
% 0.22/0.54  fof(f1535,plain,(
% 0.22/0.54    $false | (spl6_20 | ~spl6_51 | ~spl6_76 | ~spl6_85)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1380,f664])).
% 0.22/0.54  fof(f664,plain,(
% 0.22/0.54    r1_xboole_0(sK1,sK0) | ~spl6_51),
% 0.22/0.54    inference(avatar_component_clause,[],[f663])).
% 0.22/0.54  fof(f663,plain,(
% 0.22/0.54    spl6_51 <=> r1_xboole_0(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.22/0.54  fof(f1380,plain,(
% 0.22/0.54    ~r1_xboole_0(sK1,sK0) | (spl6_20 | ~spl6_76 | ~spl6_85)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f193,f1374,f1148])).
% 0.22/0.54  fof(f1148,plain,(
% 0.22/0.54    ( ! [X21,X19,X20] : (k1_xboole_0 != k3_xboole_0(X19,X21) | r1_xboole_0(X19,k2_xboole_0(X20,X21)) | ~r1_xboole_0(X19,X20)) ) | ~spl6_76),
% 0.22/0.54    inference(avatar_component_clause,[],[f1147])).
% 0.22/0.54  fof(f1147,plain,(
% 0.22/0.54    spl6_76 <=> ! [X20,X19,X21] : (k1_xboole_0 != k3_xboole_0(X19,X21) | r1_xboole_0(X19,k2_xboole_0(X20,X21)) | ~r1_xboole_0(X19,X20))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 0.22/0.54  fof(f1374,plain,(
% 0.22/0.54    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl6_85),
% 0.22/0.54    inference(avatar_component_clause,[],[f1372])).
% 0.22/0.54  fof(f1372,plain,(
% 0.22/0.54    spl6_85 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl6_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f191])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    spl6_20 <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.54  fof(f1483,plain,(
% 0.22/0.54    spl6_51 | ~spl6_58 | ~spl6_89),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1482])).
% 0.22/0.54  fof(f1482,plain,(
% 0.22/0.54    $false | (spl6_51 | ~spl6_58 | ~spl6_89)),
% 0.22/0.54    inference(subsumption_resolution,[],[f839,f1451])).
% 0.22/0.54  fof(f1451,plain,(
% 0.22/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl6_89),
% 0.22/0.54    inference(avatar_component_clause,[],[f1450])).
% 0.22/0.54  fof(f839,plain,(
% 0.22/0.54    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (spl6_51 | ~spl6_58)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f665,f833])).
% 0.22/0.54  fof(f833,plain,(
% 0.22/0.54    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) ) | ~spl6_58),
% 0.22/0.54    inference(avatar_component_clause,[],[f832])).
% 0.22/0.54  fof(f832,plain,(
% 0.22/0.54    spl6_58 <=> ! [X5,X4] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.22/0.54  fof(f665,plain,(
% 0.22/0.54    ~r1_xboole_0(sK1,sK0) | spl6_51),
% 0.22/0.54    inference(avatar_component_clause,[],[f663])).
% 0.22/0.54  fof(f1375,plain,(
% 0.22/0.54    spl6_85 | ~spl6_13 | ~spl6_17),
% 0.22/0.54    inference(avatar_split_clause,[],[f174,f138,f121,f1372])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl6_13 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl6_17 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    k1_xboole_0 = k3_xboole_0(sK1,sK2) | (~spl6_13 | ~spl6_17)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f123,f139])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl6_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f138])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    r1_xboole_0(sK1,sK2) | ~spl6_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f121])).
% 0.22/0.54  fof(f1178,plain,(
% 0.22/0.54    ~spl6_78 | ~spl6_1 | ~spl6_13 | ~spl6_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f205,f149,f121,f66,f1175])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    spl6_1 <=> r2_hidden(sK3,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    spl6_19 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    ~r2_hidden(sK3,sK1) | (~spl6_1 | ~spl6_13 | ~spl6_19)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f123,f68,f150])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl6_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f149])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    r2_hidden(sK3,sK2) | ~spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f1149,plain,(
% 0.22/0.54    spl6_76 | ~spl6_18 | ~spl6_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f251,f222,f142,f1147])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    spl6_18 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    spl6_24 <=> ! [X1,X0,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    ( ! [X21,X19,X20] : (k1_xboole_0 != k3_xboole_0(X19,X21) | r1_xboole_0(X19,k2_xboole_0(X20,X21)) | ~r1_xboole_0(X19,X20)) ) | (~spl6_18 | ~spl6_24)),
% 0.22/0.54    inference(superposition,[],[f143,f223])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) ) | ~spl6_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f222])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl6_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f142])).
% 0.22/0.54  fof(f915,plain,(
% 0.22/0.54    spl6_62 | ~spl6_16 | ~spl6_17),
% 0.22/0.54    inference(avatar_split_clause,[],[f175,f138,f134,f913])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl6_16 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k1_xboole_0 = X2 | ~r1_xboole_0(X2,X3) | ~r1_tarski(X2,X3)) ) | (~spl6_16 | ~spl6_17)),
% 0.22/0.54    inference(superposition,[],[f139,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl6_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f134])).
% 0.22/0.54  fof(f834,plain,(
% 0.22/0.54    spl6_58 | ~spl6_8 | ~spl6_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f188,f142,f98,f832])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl6_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) ) | (~spl6_8 | ~spl6_18)),
% 0.22/0.54    inference(superposition,[],[f143,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl6_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f98])).
% 0.22/0.54  fof(f736,plain,(
% 0.22/0.54    spl6_55 | ~spl6_13 | ~spl6_17 | ~spl6_23 | ~spl6_54),
% 0.22/0.54    inference(avatar_split_clause,[],[f730,f711,f210,f138,f121,f734])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    spl6_23 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.54  fof(f711,plain,(
% 0.22/0.54    spl6_54 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.22/0.54  fof(f730,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1)) ) | (~spl6_13 | ~spl6_17 | ~spl6_23 | ~spl6_54)),
% 0.22/0.54    inference(subsumption_resolution,[],[f235,f728])).
% 0.22/0.54  fof(f728,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl6_13 | ~spl6_17 | ~spl6_54)),
% 0.22/0.54    inference(forward_demodulation,[],[f715,f174])).
% 0.22/0.54  fof(f715,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK1,sK2))) ) | (~spl6_13 | ~spl6_54)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f123,f712])).
% 0.22/0.54  fof(f712,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2)) ) | ~spl6_54),
% 0.22/0.54    inference(avatar_component_clause,[],[f711])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1)) ) | (~spl6_17 | ~spl6_23)),
% 0.22/0.54    inference(superposition,[],[f211,f139])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) ) | ~spl6_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f210])).
% 0.22/0.54  fof(f713,plain,(
% 0.22/0.54    spl6_54 | ~spl6_12 | ~spl6_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f163,f130,f117,f711])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    spl6_12 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    spl6_15 <=> ! [X1,X0] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2)) ) | (~spl6_12 | ~spl6_15)),
% 0.22/0.54    inference(resolution,[],[f131,f118])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl6_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f117])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl6_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f130])).
% 0.22/0.54  fof(f654,plain,(
% 0.22/0.54    spl6_49 | ~spl6_7 | ~spl6_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f147,f102,f94,f652])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl6_7 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    spl6_9 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(X1,k1_tarski(X0))) ) | (~spl6_7 | ~spl6_9)),
% 0.22/0.54    inference(resolution,[],[f103,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl6_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f94])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl6_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f102])).
% 0.22/0.54  fof(f414,plain,(
% 0.22/0.54    spl6_44 | ~spl6_5 | ~spl6_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f145,f98,f86,f412])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl6_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl6_5 | ~spl6_8)),
% 0.22/0.54    inference(superposition,[],[f87,f99])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl6_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f86])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    spl6_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f59,f222])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    spl6_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f60,f210])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ~spl6_20 | spl6_3 | ~spl6_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f105,f94,f76,f191])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl6_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | (spl6_3 | ~spl6_7)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f78,f95])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f76])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl6_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f52,f149])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    spl6_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f57,f142])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    spl6_17),
% 0.22/0.54    inference(avatar_split_clause,[],[f56,f138])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    spl6_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f54,f134])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl6_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f51,f130])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    spl6_13 | ~spl6_2 | ~spl6_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f106,f94,f71,f121])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    r1_xboole_0(sK1,sK2) | (~spl6_2 | ~spl6_7)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f73,f95])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f71])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    spl6_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f49,f117])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl6_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f53,f102])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    spl6_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f98])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl6_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f55,f94])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    spl6_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f86])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl6_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f39,f81])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f19])).
% 0.22/0.54  fof(f19,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ~spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f76])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f71])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    r1_xboole_0(sK2,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    spl6_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f66])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    r2_hidden(sK3,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (10652)------------------------------
% 0.22/0.54  % (10652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10652)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (10652)Memory used [KB]: 7419
% 0.22/0.54  % (10652)Time elapsed: 0.110 s
% 0.22/0.54  % (10652)------------------------------
% 0.22/0.54  % (10652)------------------------------
% 0.22/0.55  % (10646)Success in time 0.179 s
%------------------------------------------------------------------------------
