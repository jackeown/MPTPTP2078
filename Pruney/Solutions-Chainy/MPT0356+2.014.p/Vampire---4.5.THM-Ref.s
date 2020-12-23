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
% DateTime   : Thu Dec  3 12:44:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  248 ( 413 expanded)
%              Number of leaves         :   68 ( 201 expanded)
%              Depth                    :    7
%              Number of atoms          :  721 (1215 expanded)
%              Number of equality atoms :   52 (  92 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f99,f104,f109,f114,f118,f122,f139,f143,f147,f170,f189,f193,f197,f201,f213,f218,f229,f253,f260,f267,f339,f392,f402,f424,f429,f457,f481,f589,f643,f664,f964,f995,f1336,f1340,f1415,f1551,f1853,f1925,f1960,f2028,f2247,f2258,f2266])).

fof(f2266,plain,
    ( spl3_31
    | ~ spl3_33
    | ~ spl3_179 ),
    inference(avatar_contradiction_clause,[],[f2265])).

fof(f2265,plain,
    ( $false
    | spl3_31
    | ~ spl3_33
    | ~ spl3_179 ),
    inference(subsumption_resolution,[],[f2264,f259])).

fof(f259,plain,
    ( ! [X1] : r1_tarski(X1,X1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_33
  <=> ! [X1] : r1_tarski(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f2264,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_31
    | ~ spl3_179 ),
    inference(resolution,[],[f2257,f246])).

fof(f246,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_31
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f2257,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_179 ),
    inference(avatar_component_clause,[],[f2256])).

fof(f2256,plain,
    ( spl3_179
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_xboole_0(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).

fof(f2258,plain,
    ( spl3_179
    | ~ spl3_33
    | ~ spl3_178 ),
    inference(avatar_split_clause,[],[f2248,f2245,f258,f2256])).

fof(f2245,plain,
    ( spl3_178
  <=> ! [X34,X35] :
        ( r1_xboole_0(X34,sK1)
        | ~ r1_tarski(X34,X35)
        | ~ r1_tarski(X35,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_178])])).

fof(f2248,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_xboole_0(X0,sK1) )
    | ~ spl3_33
    | ~ spl3_178 ),
    inference(resolution,[],[f2246,f259])).

fof(f2246,plain,
    ( ! [X35,X34] :
        ( ~ r1_tarski(X35,sK2)
        | ~ r1_tarski(X34,X35)
        | r1_xboole_0(X34,sK1) )
    | ~ spl3_178 ),
    inference(avatar_component_clause,[],[f2245])).

fof(f2247,plain,
    ( spl3_178
    | ~ spl3_26
    | ~ spl3_157 ),
    inference(avatar_split_clause,[],[f2240,f2026,f215,f2245])).

fof(f215,plain,
    ( spl3_26
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f2026,plain,
    ( spl3_157
  <=> ! [X3,X5,X7,X4,X6] :
        ( r1_xboole_0(X3,X4)
        | ~ r1_tarski(X4,k4_xboole_0(X5,X6))
        | ~ r1_tarski(X3,X7)
        | ~ r1_tarski(X7,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).

fof(f2240,plain,
    ( ! [X35,X34] :
        ( r1_xboole_0(X34,sK1)
        | ~ r1_tarski(X34,X35)
        | ~ r1_tarski(X35,sK2) )
    | ~ spl3_26
    | ~ spl3_157 ),
    inference(resolution,[],[f2027,f217])).

fof(f217,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f215])).

fof(f2027,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ r1_tarski(X4,k4_xboole_0(X5,X6))
        | r1_xboole_0(X3,X4)
        | ~ r1_tarski(X3,X7)
        | ~ r1_tarski(X7,X6) )
    | ~ spl3_157 ),
    inference(avatar_component_clause,[],[f2026])).

fof(f2028,plain,
    ( spl3_157
    | ~ spl3_15
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f394,f390,f145,f2026])).

fof(f145,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f390,plain,
    ( spl3_43
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X3)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f394,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( r1_xboole_0(X3,X4)
        | ~ r1_tarski(X4,k4_xboole_0(X5,X6))
        | ~ r1_tarski(X3,X7)
        | ~ r1_tarski(X7,X6) )
    | ~ spl3_15
    | ~ spl3_43 ),
    inference(resolution,[],[f391,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f391,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X1,X3)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f390])).

fof(f1960,plain,
    ( ~ spl3_31
    | ~ spl3_3
    | ~ spl3_22
    | spl3_25
    | ~ spl3_47
    | ~ spl3_109
    | ~ spl3_146 ),
    inference(avatar_split_clause,[],[f1959,f1923,f1549,f422,f210,f191,f92,f244])).

fof(f92,plain,
    ( spl3_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f191,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f210,plain,
    ( spl3_25
  <=> r1_tarski(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f422,plain,
    ( spl3_47
  <=> ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1549,plain,
    ( spl3_109
  <=> ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).

fof(f1923,plain,
    ( spl3_146
  <=> ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2))
        | r1_tarski(sK2,X0)
        | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).

fof(f1959,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl3_3
    | ~ spl3_22
    | spl3_25
    | ~ spl3_47
    | ~ spl3_109
    | ~ spl3_146 ),
    inference(subsumption_resolution,[],[f526,f1955])).

fof(f1955,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_47
    | ~ spl3_109
    | ~ spl3_146 ),
    inference(subsumption_resolution,[],[f1954,f93])).

fof(f93,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1954,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | r1_tarski(sK2,sK0)
    | ~ spl3_47
    | ~ spl3_109
    | ~ spl3_146 ),
    inference(forward_demodulation,[],[f1947,f1550])).

fof(f1550,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)
    | ~ spl3_109 ),
    inference(avatar_component_clause,[],[f1549])).

fof(f1947,plain,
    ( r1_tarski(sK2,sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK0),k4_xboole_0(sK0,sK2))
    | ~ spl3_47
    | ~ spl3_146 ),
    inference(resolution,[],[f1924,f423])).

fof(f423,plain,
    ( ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1924,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
        | r1_tarski(sK2,X0)
        | ~ r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2)) )
    | ~ spl3_146 ),
    inference(avatar_component_clause,[],[f1923])).

fof(f526,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ r1_tarski(sK2,sK0)
    | ~ spl3_22
    | spl3_25 ),
    inference(resolution,[],[f212,f192])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f191])).

fof(f212,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK0,sK1))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f1925,plain,
    ( spl3_146
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_136 ),
    inference(avatar_split_clause,[],[f1881,f1851,f137,f84,f1923])).

fof(f84,plain,
    ( spl3_1
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f137,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1851,plain,
    ( spl3_136
  <=> ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).

fof(f1881,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2))
        | r1_tarski(sK2,X0)
        | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_136 ),
    inference(subsumption_resolution,[],[f1878,f85])).

fof(f85,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1878,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2))
        | r1_tarski(sK2,X0)
        | ~ r2_hidden(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl3_13
    | ~ spl3_136 ),
    inference(resolution,[],[f1852,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f1852,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2))
        | r1_tarski(sK2,X0) )
    | ~ spl3_136 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f1853,plain,
    ( spl3_136
    | ~ spl3_5
    | ~ spl3_28
    | ~ spl3_105 ),
    inference(avatar_split_clause,[],[f1718,f1334,f226,f101,f1851])).

fof(f101,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f226,plain,
    ( spl3_28
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1334,plain,
    ( spl3_105
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).

fof(f1718,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(sK2,X0) )
    | ~ spl3_5
    | ~ spl3_28
    | ~ spl3_105 ),
    inference(forward_demodulation,[],[f1715,f228])).

fof(f228,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f226])).

fof(f1715,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(sK2,X0) )
    | ~ spl3_5
    | ~ spl3_105 ),
    inference(resolution,[],[f1335,f103])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1335,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | r1_tarski(X1,X2) )
    | ~ spl3_105 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1551,plain,
    ( spl3_109
    | ~ spl3_9
    | ~ spl3_48
    | ~ spl3_108 ),
    inference(avatar_split_clause,[],[f1465,f1413,f427,f120,f1549])).

fof(f120,plain,
    ( spl3_9
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f427,plain,
    ( spl3_48
  <=> ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f1413,plain,
    ( spl3_108
  <=> ! [X6] : r1_tarski(k4_xboole_0(X6,X6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).

fof(f1465,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)
    | ~ spl3_9
    | ~ spl3_48
    | ~ spl3_108 ),
    inference(backward_demodulation,[],[f428,f1420])).

fof(f1420,plain,
    ( ! [X8] : k1_xboole_0 = k4_xboole_0(X8,X8)
    | ~ spl3_9
    | ~ spl3_108 ),
    inference(resolution,[],[f1414,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f1414,plain,
    ( ! [X6] : r1_tarski(k4_xboole_0(X6,X6),k1_xboole_0)
    | ~ spl3_108 ),
    inference(avatar_component_clause,[],[f1413])).

fof(f428,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f427])).

fof(f1415,plain,
    ( spl3_108
    | ~ spl3_33
    | ~ spl3_106 ),
    inference(avatar_split_clause,[],[f1344,f1338,f258,f1413])).

fof(f1338,plain,
    ( spl3_106
  <=> ! [X5,X6] :
        ( ~ r1_tarski(k4_xboole_0(X5,X5),k4_xboole_0(X6,X5))
        | r1_tarski(k4_xboole_0(X5,X5),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).

fof(f1344,plain,
    ( ! [X6] : r1_tarski(k4_xboole_0(X6,X6),k1_xboole_0)
    | ~ spl3_33
    | ~ spl3_106 ),
    inference(resolution,[],[f1339,f259])).

fof(f1339,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k4_xboole_0(X5,X5),k4_xboole_0(X6,X5))
        | r1_tarski(k4_xboole_0(X5,X5),k1_xboole_0) )
    | ~ spl3_106 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1340,plain,
    ( spl3_106
    | ~ spl3_72
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f1003,f993,f662,f1338])).

fof(f662,plain,
    ( spl3_72
  <=> ! [X5] : k2_xboole_0(k4_xboole_0(X5,X5),X5) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f993,plain,
    ( spl3_87
  <=> ! [X22,X21,X23] :
        ( ~ r1_tarski(X22,k4_xboole_0(X21,k2_xboole_0(X22,X23)))
        | r1_tarski(X22,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f1003,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k4_xboole_0(X5,X5),k4_xboole_0(X6,X5))
        | r1_tarski(k4_xboole_0(X5,X5),k1_xboole_0) )
    | ~ spl3_72
    | ~ spl3_87 ),
    inference(superposition,[],[f994,f663])).

fof(f663,plain,
    ( ! [X5] : k2_xboole_0(k4_xboole_0(X5,X5),X5) = X5
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f662])).

fof(f994,plain,
    ( ! [X23,X21,X22] :
        ( ~ r1_tarski(X22,k4_xboole_0(X21,k2_xboole_0(X22,X23)))
        | r1_tarski(X22,k1_xboole_0) )
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f993])).

fof(f1336,plain,(
    spl3_105 ),
    inference(avatar_split_clause,[],[f66,f1334])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f995,plain,
    ( spl3_87
    | ~ spl3_18
    | ~ spl3_86 ),
    inference(avatar_split_clause,[],[f991,f962,f168,f993])).

fof(f168,plain,
    ( spl3_18
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f962,plain,
    ( spl3_86
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3))))
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f991,plain,
    ( ! [X23,X21,X22] :
        ( ~ r1_tarski(X22,k4_xboole_0(X21,k2_xboole_0(X22,X23)))
        | r1_tarski(X22,k1_xboole_0) )
    | ~ spl3_18
    | ~ spl3_86 ),
    inference(superposition,[],[f963,f169])).

fof(f169,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f963,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3))))
        | r1_tarski(X0,X1) )
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f962])).

fof(f964,plain,
    ( spl3_86
    | ~ spl3_8
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f458,f455,f116,f962])).

fof(f116,plain,
    ( spl3_8
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f455,plain,
    ( spl3_53
  <=> ! [X3,X5,X2,X4] :
        ( r1_tarski(X2,X3)
        | ~ r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X4,X5)))
        | ~ r1_tarski(X2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f458,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3))))
        | r1_tarski(X0,X1) )
    | ~ spl3_8
    | ~ spl3_53 ),
    inference(resolution,[],[f456,f117])).

fof(f117,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f456,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ r1_tarski(X2,X5)
        | ~ r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X4,X5)))
        | r1_tarski(X2,X3) )
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f455])).

fof(f664,plain,
    ( spl3_72
    | ~ spl3_33
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f650,f641,f258,f662])).

fof(f641,plain,
    ( spl3_70
  <=> ! [X5,X4] :
        ( ~ r1_tarski(X4,X5)
        | k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f650,plain,
    ( ! [X5] : k2_xboole_0(k4_xboole_0(X5,X5),X5) = X5
    | ~ spl3_33
    | ~ spl3_70 ),
    inference(resolution,[],[f642,f259])).

fof(f642,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,X5)
        | k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5 )
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f641])).

fof(f643,plain,
    ( spl3_70
    | ~ spl3_14
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f594,f587,f141,f641])).

fof(f141,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f587,plain,
    ( spl3_66
  <=> ! [X1,X0] :
        ( r1_tarski(k4_xboole_0(X0,X0),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f594,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,X5)
        | k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5 )
    | ~ spl3_14
    | ~ spl3_66 ),
    inference(resolution,[],[f588,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f588,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f587])).

fof(f589,plain,
    ( spl3_66
    | ~ spl3_34
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f581,f479,f265,f587])).

fof(f265,plain,
    ( spl3_34
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f479,plain,
    ( spl3_55
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f581,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_34
    | ~ spl3_55 ),
    inference(duplicate_literal_removal,[],[f580])).

fof(f580,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X0),X1)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_34
    | ~ spl3_55 ),
    inference(superposition,[],[f480,f266])).

fof(f266,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f265])).

fof(f480,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f479])).

fof(f481,plain,(
    spl3_55 ),
    inference(avatar_split_clause,[],[f79,f479])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f457,plain,
    ( spl3_53
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f249,f195,f145,f455])).

fof(f195,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f249,plain,
    ( ! [X4,X2,X5,X3] :
        ( r1_tarski(X2,X3)
        | ~ r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X4,X5)))
        | ~ r1_tarski(X2,X5) )
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(resolution,[],[f196,f146])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X2)
        | r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f429,plain,
    ( spl3_48
    | ~ spl3_40
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f425,f422,f337,f427])).

fof(f337,plain,
    ( spl3_40
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ r2_hidden(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f425,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)
    | ~ spl3_40
    | ~ spl3_47 ),
    inference(resolution,[],[f423,f338])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f337])).

fof(f424,plain,
    ( spl3_47
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f417,f400,f199,f422])).

fof(f199,plain,
    ( spl3_24
  <=> ! [X0] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f400,plain,
    ( spl3_45
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X2)
        | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f417,plain,
    ( ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0))
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(resolution,[],[f401,f200])).

fof(f200,plain,
    ( ! [X0] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f199])).

fof(f401,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
        | r2_hidden(X1,X2) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f400])).

fof(f402,plain,(
    spl3_45 ),
    inference(avatar_split_clause,[],[f81,f400])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f72,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f392,plain,(
    spl3_43 ),
    inference(avatar_split_clause,[],[f75,f390])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f339,plain,
    ( spl3_40
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f208,f187,f137,f84,f337])).

fof(f187,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ r2_hidden(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f204,f85])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ r2_hidden(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(X0)) )
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(resolution,[],[f188,f138])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f267,plain,
    ( spl3_34
    | ~ spl3_14
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f262,f258,f141,f265])).

fof(f262,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_14
    | ~ spl3_33 ),
    inference(resolution,[],[f259,f142])).

fof(f260,plain,
    ( spl3_33
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f255,f251,f116,f258])).

fof(f251,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f255,plain,
    ( ! [X1] : r1_tarski(X1,X1)
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(resolution,[],[f252,f117])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))
        | r1_tarski(X0,X1) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f248,f195,f88,f251])).

fof(f88,plain,
    ( spl3_2
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) )
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(resolution,[],[f196,f89])).

fof(f89,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f229,plain,
    ( spl3_28
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f203,f187,f101,f226])).

fof(f203,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(resolution,[],[f188,f103])).

fof(f218,plain,
    ( spl3_26
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f207,f187,f106,f101,f215])).

fof(f106,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f207,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f108,f203])).

fof(f108,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f213,plain,
    ( ~ spl3_25
    | ~ spl3_4
    | spl3_7
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f205,f187,f111,f96,f210])).

fof(f96,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f111,plain,
    ( spl3_7
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f205,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_4
    | spl3_7
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f113,f202])).

fof(f202,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(resolution,[],[f188,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f113,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f201,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f78,f199])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f54,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f197,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f70,f195])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f193,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f68,f191])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f189,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f64,f187])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f170,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f164,f141,f92,f168])).

fof(f164,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(resolution,[],[f142,f93])).

fof(f147,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f67,f145])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f143,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f63,f141])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f139,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f60,f137])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f122,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f55,f120])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f118,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f56,f116])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f114,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f49,f111])).

fof(f49,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
          & r1_tarski(sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
        & r1_tarski(sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f109,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f48,f106])).

fof(f48,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f47,f101])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f46,f96])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f92])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f90,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f86,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f50,f84])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (20202)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (20205)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (20207)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (20201)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (20203)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (20215)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (20206)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (20210)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (20209)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (20213)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (20208)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (20216)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (20218)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (20211)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (20204)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.54  % (20212)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.55  % (20214)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.55  % (20217)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.56  % (20208)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f2267,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f86,f90,f94,f99,f104,f109,f114,f118,f122,f139,f143,f147,f170,f189,f193,f197,f201,f213,f218,f229,f253,f260,f267,f339,f392,f402,f424,f429,f457,f481,f589,f643,f664,f964,f995,f1336,f1340,f1415,f1551,f1853,f1925,f1960,f2028,f2247,f2258,f2266])).
% 0.21/0.56  fof(f2266,plain,(
% 0.21/0.56    spl3_31 | ~spl3_33 | ~spl3_179),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f2265])).
% 0.21/0.56  fof(f2265,plain,(
% 0.21/0.56    $false | (spl3_31 | ~spl3_33 | ~spl3_179)),
% 0.21/0.56    inference(subsumption_resolution,[],[f2264,f259])).
% 0.21/0.56  fof(f259,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) ) | ~spl3_33),
% 0.21/0.56    inference(avatar_component_clause,[],[f258])).
% 0.21/0.56  fof(f258,plain,(
% 0.21/0.56    spl3_33 <=> ! [X1] : r1_tarski(X1,X1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.56  fof(f2264,plain,(
% 0.21/0.56    ~r1_tarski(sK2,sK2) | (spl3_31 | ~spl3_179)),
% 0.21/0.56    inference(resolution,[],[f2257,f246])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    ~r1_xboole_0(sK2,sK1) | spl3_31),
% 0.21/0.56    inference(avatar_component_clause,[],[f244])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    spl3_31 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.56  fof(f2257,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK2)) ) | ~spl3_179),
% 0.21/0.56    inference(avatar_component_clause,[],[f2256])).
% 0.21/0.56  fof(f2256,plain,(
% 0.21/0.56    spl3_179 <=> ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).
% 0.21/0.56  fof(f2258,plain,(
% 0.21/0.56    spl3_179 | ~spl3_33 | ~spl3_178),
% 0.21/0.56    inference(avatar_split_clause,[],[f2248,f2245,f258,f2256])).
% 0.21/0.56  fof(f2245,plain,(
% 0.21/0.56    spl3_178 <=> ! [X34,X35] : (r1_xboole_0(X34,sK1) | ~r1_tarski(X34,X35) | ~r1_tarski(X35,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_178])])).
% 0.21/0.56  fof(f2248,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK1)) ) | (~spl3_33 | ~spl3_178)),
% 0.21/0.56    inference(resolution,[],[f2246,f259])).
% 0.21/0.56  fof(f2246,plain,(
% 0.21/0.56    ( ! [X35,X34] : (~r1_tarski(X35,sK2) | ~r1_tarski(X34,X35) | r1_xboole_0(X34,sK1)) ) | ~spl3_178),
% 0.21/0.56    inference(avatar_component_clause,[],[f2245])).
% 0.21/0.56  fof(f2247,plain,(
% 0.21/0.56    spl3_178 | ~spl3_26 | ~spl3_157),
% 0.21/0.56    inference(avatar_split_clause,[],[f2240,f2026,f215,f2245])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    spl3_26 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.56  fof(f2026,plain,(
% 0.21/0.56    spl3_157 <=> ! [X3,X5,X7,X4,X6] : (r1_xboole_0(X3,X4) | ~r1_tarski(X4,k4_xboole_0(X5,X6)) | ~r1_tarski(X3,X7) | ~r1_tarski(X7,X6))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).
% 0.21/0.56  fof(f2240,plain,(
% 0.21/0.56    ( ! [X35,X34] : (r1_xboole_0(X34,sK1) | ~r1_tarski(X34,X35) | ~r1_tarski(X35,sK2)) ) | (~spl3_26 | ~spl3_157)),
% 0.21/0.56    inference(resolution,[],[f2027,f217])).
% 0.21/0.56  fof(f217,plain,(
% 0.21/0.56    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_26),
% 0.21/0.56    inference(avatar_component_clause,[],[f215])).
% 0.21/0.56  fof(f2027,plain,(
% 0.21/0.56    ( ! [X6,X4,X7,X5,X3] : (~r1_tarski(X4,k4_xboole_0(X5,X6)) | r1_xboole_0(X3,X4) | ~r1_tarski(X3,X7) | ~r1_tarski(X7,X6)) ) | ~spl3_157),
% 0.21/0.56    inference(avatar_component_clause,[],[f2026])).
% 0.21/0.56  fof(f2028,plain,(
% 0.21/0.56    spl3_157 | ~spl3_15 | ~spl3_43),
% 0.21/0.56    inference(avatar_split_clause,[],[f394,f390,f145,f2026])).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    spl3_15 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.56  fof(f390,plain,(
% 0.21/0.56    spl3_43 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.56  fof(f394,plain,(
% 0.21/0.56    ( ! [X6,X4,X7,X5,X3] : (r1_xboole_0(X3,X4) | ~r1_tarski(X4,k4_xboole_0(X5,X6)) | ~r1_tarski(X3,X7) | ~r1_tarski(X7,X6)) ) | (~spl3_15 | ~spl3_43)),
% 0.21/0.56    inference(resolution,[],[f391,f146])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_15),
% 0.21/0.56    inference(avatar_component_clause,[],[f145])).
% 0.21/0.56  fof(f391,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) ) | ~spl3_43),
% 0.21/0.56    inference(avatar_component_clause,[],[f390])).
% 0.21/0.56  fof(f1960,plain,(
% 0.21/0.56    ~spl3_31 | ~spl3_3 | ~spl3_22 | spl3_25 | ~spl3_47 | ~spl3_109 | ~spl3_146),
% 0.21/0.56    inference(avatar_split_clause,[],[f1959,f1923,f1549,f422,f210,f191,f92,f244])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    spl3_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    spl3_22 <=> ! [X1,X0,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.56  fof(f210,plain,(
% 0.21/0.56    spl3_25 <=> r1_tarski(sK2,k4_xboole_0(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.56  fof(f422,plain,(
% 0.21/0.56    spl3_47 <=> ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.56  fof(f1549,plain,(
% 0.21/0.56    spl3_109 <=> ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).
% 0.21/0.56  fof(f1923,plain,(
% 0.21/0.56    spl3_146 <=> ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2)) | r1_tarski(sK2,X0) | ~r2_hidden(X0,k1_zfmisc_1(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).
% 0.21/0.56  fof(f1959,plain,(
% 0.21/0.56    ~r1_xboole_0(sK2,sK1) | (~spl3_3 | ~spl3_22 | spl3_25 | ~spl3_47 | ~spl3_109 | ~spl3_146)),
% 0.21/0.56    inference(subsumption_resolution,[],[f526,f1955])).
% 0.21/0.56  fof(f1955,plain,(
% 0.21/0.56    r1_tarski(sK2,sK0) | (~spl3_3 | ~spl3_47 | ~spl3_109 | ~spl3_146)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1954,f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f92])).
% 0.21/0.56  fof(f1954,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK2)) | r1_tarski(sK2,sK0) | (~spl3_47 | ~spl3_109 | ~spl3_146)),
% 0.21/0.56    inference(forward_demodulation,[],[f1947,f1550])).
% 0.21/0.56  fof(f1550,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) ) | ~spl3_109),
% 0.21/0.56    inference(avatar_component_clause,[],[f1549])).
% 0.21/0.56  fof(f1947,plain,(
% 0.21/0.56    r1_tarski(sK2,sK0) | ~r1_tarski(k3_subset_1(sK0,sK0),k4_xboole_0(sK0,sK2)) | (~spl3_47 | ~spl3_146)),
% 0.21/0.56    inference(resolution,[],[f1924,f423])).
% 0.21/0.56  fof(f423,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) ) | ~spl3_47),
% 0.21/0.56    inference(avatar_component_clause,[],[f422])).
% 0.21/0.56  fof(f1924,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,X0) | ~r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2))) ) | ~spl3_146),
% 0.21/0.56    inference(avatar_component_clause,[],[f1923])).
% 0.21/0.56  fof(f526,plain,(
% 0.21/0.56    ~r1_xboole_0(sK2,sK1) | ~r1_tarski(sK2,sK0) | (~spl3_22 | spl3_25)),
% 0.21/0.56    inference(resolution,[],[f212,f192])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_22),
% 0.21/0.56    inference(avatar_component_clause,[],[f191])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    ~r1_tarski(sK2,k4_xboole_0(sK0,sK1)) | spl3_25),
% 0.21/0.56    inference(avatar_component_clause,[],[f210])).
% 0.21/0.56  fof(f1925,plain,(
% 0.21/0.56    spl3_146 | ~spl3_1 | ~spl3_13 | ~spl3_136),
% 0.21/0.56    inference(avatar_split_clause,[],[f1881,f1851,f137,f84,f1923])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    spl3_1 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    spl3_13 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.56  fof(f1851,plain,(
% 0.21/0.56    spl3_136 <=> ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).
% 0.21/0.56  fof(f1881,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2)) | r1_tarski(sK2,X0) | ~r2_hidden(X0,k1_zfmisc_1(sK0))) ) | (~spl3_1 | ~spl3_13 | ~spl3_136)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1878,f85])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl3_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f84])).
% 0.21/0.56  fof(f1878,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2)) | r1_tarski(sK2,X0) | ~r2_hidden(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))) ) | (~spl3_13 | ~spl3_136)),
% 0.21/0.56    inference(resolution,[],[f1852,f138])).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl3_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f137])).
% 0.21/0.56  fof(f1852,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2)) | r1_tarski(sK2,X0)) ) | ~spl3_136),
% 0.21/0.56    inference(avatar_component_clause,[],[f1851])).
% 0.21/0.56  fof(f1853,plain,(
% 0.21/0.56    spl3_136 | ~spl3_5 | ~spl3_28 | ~spl3_105),
% 0.21/0.56    inference(avatar_split_clause,[],[f1718,f1334,f226,f101,f1851])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    spl3_28 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.56  fof(f1334,plain,(
% 0.21/0.56    spl3_105 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).
% 0.21/0.56  fof(f1718,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,X0)) ) | (~spl3_5 | ~spl3_28 | ~spl3_105)),
% 0.21/0.56    inference(forward_demodulation,[],[f1715,f228])).
% 0.21/0.56  fof(f228,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_28),
% 0.21/0.56    inference(avatar_component_clause,[],[f226])).
% 0.21/0.56  fof(f1715,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,X0)) ) | (~spl3_5 | ~spl3_105)),
% 0.21/0.56    inference(resolution,[],[f1335,f103])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f101])).
% 0.21/0.56  fof(f1335,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) ) | ~spl3_105),
% 0.21/0.56    inference(avatar_component_clause,[],[f1334])).
% 0.21/0.56  fof(f1551,plain,(
% 0.21/0.56    spl3_109 | ~spl3_9 | ~spl3_48 | ~spl3_108),
% 0.21/0.56    inference(avatar_split_clause,[],[f1465,f1413,f427,f120,f1549])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    spl3_9 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.56  fof(f427,plain,(
% 0.21/0.56    spl3_48 <=> ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.56  fof(f1413,plain,(
% 0.21/0.56    spl3_108 <=> ! [X6] : r1_tarski(k4_xboole_0(X6,X6),k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).
% 0.21/0.56  fof(f1465,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) ) | (~spl3_9 | ~spl3_48 | ~spl3_108)),
% 0.21/0.56    inference(backward_demodulation,[],[f428,f1420])).
% 0.21/0.56  fof(f1420,plain,(
% 0.21/0.56    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(X8,X8)) ) | (~spl3_9 | ~spl3_108)),
% 0.21/0.56    inference(resolution,[],[f1414,f121])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f120])).
% 0.21/0.56  fof(f1414,plain,(
% 0.21/0.56    ( ! [X6] : (r1_tarski(k4_xboole_0(X6,X6),k1_xboole_0)) ) | ~spl3_108),
% 0.21/0.56    inference(avatar_component_clause,[],[f1413])).
% 0.21/0.56  fof(f428,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) ) | ~spl3_48),
% 0.21/0.56    inference(avatar_component_clause,[],[f427])).
% 0.21/0.56  fof(f1415,plain,(
% 0.21/0.56    spl3_108 | ~spl3_33 | ~spl3_106),
% 0.21/0.56    inference(avatar_split_clause,[],[f1344,f1338,f258,f1413])).
% 0.21/0.56  fof(f1338,plain,(
% 0.21/0.56    spl3_106 <=> ! [X5,X6] : (~r1_tarski(k4_xboole_0(X5,X5),k4_xboole_0(X6,X5)) | r1_tarski(k4_xboole_0(X5,X5),k1_xboole_0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).
% 0.21/0.56  fof(f1344,plain,(
% 0.21/0.56    ( ! [X6] : (r1_tarski(k4_xboole_0(X6,X6),k1_xboole_0)) ) | (~spl3_33 | ~spl3_106)),
% 0.21/0.56    inference(resolution,[],[f1339,f259])).
% 0.21/0.56  fof(f1339,plain,(
% 0.21/0.56    ( ! [X6,X5] : (~r1_tarski(k4_xboole_0(X5,X5),k4_xboole_0(X6,X5)) | r1_tarski(k4_xboole_0(X5,X5),k1_xboole_0)) ) | ~spl3_106),
% 0.21/0.56    inference(avatar_component_clause,[],[f1338])).
% 0.21/0.56  fof(f1340,plain,(
% 0.21/0.56    spl3_106 | ~spl3_72 | ~spl3_87),
% 0.21/0.56    inference(avatar_split_clause,[],[f1003,f993,f662,f1338])).
% 0.21/0.56  fof(f662,plain,(
% 0.21/0.56    spl3_72 <=> ! [X5] : k2_xboole_0(k4_xboole_0(X5,X5),X5) = X5),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.56  fof(f993,plain,(
% 0.21/0.56    spl3_87 <=> ! [X22,X21,X23] : (~r1_tarski(X22,k4_xboole_0(X21,k2_xboole_0(X22,X23))) | r1_tarski(X22,k1_xboole_0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 0.21/0.56  fof(f1003,plain,(
% 0.21/0.56    ( ! [X6,X5] : (~r1_tarski(k4_xboole_0(X5,X5),k4_xboole_0(X6,X5)) | r1_tarski(k4_xboole_0(X5,X5),k1_xboole_0)) ) | (~spl3_72 | ~spl3_87)),
% 0.21/0.56    inference(superposition,[],[f994,f663])).
% 0.21/0.56  fof(f663,plain,(
% 0.21/0.56    ( ! [X5] : (k2_xboole_0(k4_xboole_0(X5,X5),X5) = X5) ) | ~spl3_72),
% 0.21/0.56    inference(avatar_component_clause,[],[f662])).
% 0.21/0.56  fof(f994,plain,(
% 0.21/0.56    ( ! [X23,X21,X22] : (~r1_tarski(X22,k4_xboole_0(X21,k2_xboole_0(X22,X23))) | r1_tarski(X22,k1_xboole_0)) ) | ~spl3_87),
% 0.21/0.56    inference(avatar_component_clause,[],[f993])).
% 0.21/0.56  fof(f1336,plain,(
% 0.21/0.56    spl3_105),
% 0.21/0.56    inference(avatar_split_clause,[],[f66,f1334])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.56  fof(f995,plain,(
% 0.21/0.56    spl3_87 | ~spl3_18 | ~spl3_86),
% 0.21/0.56    inference(avatar_split_clause,[],[f991,f962,f168,f993])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    spl3_18 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.56  fof(f962,plain,(
% 0.21/0.56    spl3_86 <=> ! [X1,X3,X0,X2] : (~r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3)))) | r1_tarski(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 0.21/0.56  fof(f991,plain,(
% 0.21/0.56    ( ! [X23,X21,X22] : (~r1_tarski(X22,k4_xboole_0(X21,k2_xboole_0(X22,X23))) | r1_tarski(X22,k1_xboole_0)) ) | (~spl3_18 | ~spl3_86)),
% 0.21/0.56    inference(superposition,[],[f963,f169])).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f168])).
% 0.21/0.56  fof(f963,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3)))) | r1_tarski(X0,X1)) ) | ~spl3_86),
% 0.21/0.56    inference(avatar_component_clause,[],[f962])).
% 0.21/0.56  fof(f964,plain,(
% 0.21/0.56    spl3_86 | ~spl3_8 | ~spl3_53),
% 0.21/0.56    inference(avatar_split_clause,[],[f458,f455,f116,f962])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    spl3_8 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.56  fof(f455,plain,(
% 0.21/0.56    spl3_53 <=> ! [X3,X5,X2,X4] : (r1_tarski(X2,X3) | ~r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X4,X5))) | ~r1_tarski(X2,X5))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.56  fof(f458,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3)))) | r1_tarski(X0,X1)) ) | (~spl3_8 | ~spl3_53)),
% 0.21/0.56    inference(resolution,[],[f456,f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f116])).
% 0.21/0.56  fof(f456,plain,(
% 0.21/0.56    ( ! [X4,X2,X5,X3] : (~r1_tarski(X2,X5) | ~r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X4,X5))) | r1_tarski(X2,X3)) ) | ~spl3_53),
% 0.21/0.56    inference(avatar_component_clause,[],[f455])).
% 0.21/0.56  fof(f664,plain,(
% 0.21/0.56    spl3_72 | ~spl3_33 | ~spl3_70),
% 0.21/0.56    inference(avatar_split_clause,[],[f650,f641,f258,f662])).
% 0.21/0.56  fof(f641,plain,(
% 0.21/0.56    spl3_70 <=> ! [X5,X4] : (~r1_tarski(X4,X5) | k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 0.21/0.56  fof(f650,plain,(
% 0.21/0.56    ( ! [X5] : (k2_xboole_0(k4_xboole_0(X5,X5),X5) = X5) ) | (~spl3_33 | ~spl3_70)),
% 0.21/0.56    inference(resolution,[],[f642,f259])).
% 0.21/0.56  fof(f642,plain,(
% 0.21/0.56    ( ! [X4,X5] : (~r1_tarski(X4,X5) | k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5) ) | ~spl3_70),
% 0.21/0.56    inference(avatar_component_clause,[],[f641])).
% 0.21/0.56  fof(f643,plain,(
% 0.21/0.56    spl3_70 | ~spl3_14 | ~spl3_66),
% 0.21/0.56    inference(avatar_split_clause,[],[f594,f587,f141,f641])).
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    spl3_14 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.56  fof(f587,plain,(
% 0.21/0.56    spl3_66 <=> ! [X1,X0] : (r1_tarski(k4_xboole_0(X0,X0),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.56  fof(f594,plain,(
% 0.21/0.56    ( ! [X4,X5] : (~r1_tarski(X4,X5) | k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5) ) | (~spl3_14 | ~spl3_66)),
% 0.21/0.56    inference(resolution,[],[f588,f142])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_14),
% 0.21/0.56    inference(avatar_component_clause,[],[f141])).
% 0.21/0.56  fof(f588,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_66),
% 0.21/0.56    inference(avatar_component_clause,[],[f587])).
% 0.21/0.56  fof(f589,plain,(
% 0.21/0.56    spl3_66 | ~spl3_34 | ~spl3_55),
% 0.21/0.56    inference(avatar_split_clause,[],[f581,f479,f265,f587])).
% 0.21/0.56  fof(f265,plain,(
% 0.21/0.56    spl3_34 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.56  fof(f479,plain,(
% 0.21/0.56    spl3_55 <=> ! [X1,X0,X2] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.21/0.56  fof(f581,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1) | ~r1_tarski(X0,X1)) ) | (~spl3_34 | ~spl3_55)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f580])).
% 0.21/0.56  fof(f580,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1) | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X1)) ) | (~spl3_34 | ~spl3_55)),
% 0.21/0.56    inference(superposition,[],[f480,f266])).
% 0.21/0.56  fof(f266,plain,(
% 0.21/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl3_34),
% 0.21/0.56    inference(avatar_component_clause,[],[f265])).
% 0.21/0.56  fof(f480,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl3_55),
% 0.21/0.56    inference(avatar_component_clause,[],[f479])).
% 0.21/0.56  fof(f481,plain,(
% 0.21/0.56    spl3_55),
% 0.21/0.56    inference(avatar_split_clause,[],[f79,f479])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f69,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.56  fof(f457,plain,(
% 0.21/0.56    spl3_53 | ~spl3_15 | ~spl3_23),
% 0.21/0.56    inference(avatar_split_clause,[],[f249,f195,f145,f455])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    spl3_23 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.56  fof(f249,plain,(
% 0.21/0.56    ( ! [X4,X2,X5,X3] : (r1_tarski(X2,X3) | ~r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X4,X5))) | ~r1_tarski(X2,X5)) ) | (~spl3_15 | ~spl3_23)),
% 0.21/0.56    inference(resolution,[],[f196,f146])).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_23),
% 0.21/0.56    inference(avatar_component_clause,[],[f195])).
% 0.21/0.56  fof(f429,plain,(
% 0.21/0.56    spl3_48 | ~spl3_40 | ~spl3_47),
% 0.21/0.56    inference(avatar_split_clause,[],[f425,f422,f337,f427])).
% 0.21/0.56  fof(f337,plain,(
% 0.21/0.56    spl3_40 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r2_hidden(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.56  fof(f425,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) ) | (~spl3_40 | ~spl3_47)),
% 0.21/0.56    inference(resolution,[],[f423,f338])).
% 0.21/0.56  fof(f338,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl3_40),
% 0.21/0.56    inference(avatar_component_clause,[],[f337])).
% 0.21/0.56  fof(f424,plain,(
% 0.21/0.56    spl3_47 | ~spl3_24 | ~spl3_45),
% 0.21/0.56    inference(avatar_split_clause,[],[f417,f400,f199,f422])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    spl3_24 <=> ! [X0] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.56  fof(f400,plain,(
% 0.21/0.56    spl3_45 <=> ! [X1,X0,X2] : (r2_hidden(X1,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.56  fof(f417,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) ) | (~spl3_24 | ~spl3_45)),
% 0.21/0.56    inference(resolution,[],[f401,f200])).
% 0.21/0.56  fof(f200,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0))) ) | ~spl3_24),
% 0.21/0.56    inference(avatar_component_clause,[],[f199])).
% 0.21/0.56  fof(f401,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) ) | ~spl3_45),
% 0.21/0.56    inference(avatar_component_clause,[],[f400])).
% 0.21/0.56  fof(f402,plain,(
% 0.21/0.56    spl3_45),
% 0.21/0.56    inference(avatar_split_clause,[],[f81,f400])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f72,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f57,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.56    inference(flattening,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.56    inference(nnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.56  fof(f392,plain,(
% 0.21/0.56    spl3_43),
% 0.21/0.56    inference(avatar_split_clause,[],[f75,f390])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.21/0.56  fof(f339,plain,(
% 0.21/0.56    spl3_40 | ~spl3_1 | ~spl3_13 | ~spl3_21),
% 0.21/0.56    inference(avatar_split_clause,[],[f208,f187,f137,f84,f337])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    spl3_21 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r2_hidden(X1,k1_zfmisc_1(X0))) ) | (~spl3_1 | ~spl3_13 | ~spl3_21)),
% 0.21/0.56    inference(subsumption_resolution,[],[f204,f85])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r2_hidden(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) ) | (~spl3_13 | ~spl3_21)),
% 0.21/0.56    inference(resolution,[],[f188,f138])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl3_21),
% 0.21/0.56    inference(avatar_component_clause,[],[f187])).
% 0.21/0.56  fof(f267,plain,(
% 0.21/0.56    spl3_34 | ~spl3_14 | ~spl3_33),
% 0.21/0.56    inference(avatar_split_clause,[],[f262,f258,f141,f265])).
% 0.21/0.56  fof(f262,plain,(
% 0.21/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | (~spl3_14 | ~spl3_33)),
% 0.21/0.56    inference(resolution,[],[f259,f142])).
% 0.21/0.56  fof(f260,plain,(
% 0.21/0.56    spl3_33 | ~spl3_8 | ~spl3_32),
% 0.21/0.56    inference(avatar_split_clause,[],[f255,f251,f116,f258])).
% 0.21/0.56  fof(f251,plain,(
% 0.21/0.56    spl3_32 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.56  fof(f255,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) ) | (~spl3_8 | ~spl3_32)),
% 0.21/0.56    inference(resolution,[],[f252,f117])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) | r1_tarski(X0,X1)) ) | ~spl3_32),
% 0.21/0.56    inference(avatar_component_clause,[],[f251])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    spl3_32 | ~spl3_2 | ~spl3_23),
% 0.21/0.56    inference(avatar_split_clause,[],[f248,f195,f88,f251])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    spl3_2 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.56  fof(f248,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))) ) | (~spl3_2 | ~spl3_23)),
% 0.21/0.56    inference(resolution,[],[f196,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f88])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    spl3_28 | ~spl3_5 | ~spl3_21),
% 0.21/0.56    inference(avatar_split_clause,[],[f203,f187,f101,f226])).
% 0.21/0.56  fof(f203,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_5 | ~spl3_21)),
% 0.21/0.56    inference(resolution,[],[f188,f103])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    spl3_26 | ~spl3_5 | ~spl3_6 | ~spl3_21),
% 0.21/0.56    inference(avatar_split_clause,[],[f207,f187,f106,f101,f215])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    spl3_6 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_5 | ~spl3_6 | ~spl3_21)),
% 0.21/0.56    inference(backward_demodulation,[],[f108,f203])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl3_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f106])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    ~spl3_25 | ~spl3_4 | spl3_7 | ~spl3_21),
% 0.21/0.56    inference(avatar_split_clause,[],[f205,f187,f111,f96,f210])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    spl3_7 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    ~r1_tarski(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_4 | spl3_7 | ~spl3_21)),
% 0.21/0.56    inference(backward_demodulation,[],[f113,f202])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_21)),
% 0.21/0.56    inference(resolution,[],[f188,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f96])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | spl3_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f111])).
% 0.21/0.56  fof(f201,plain,(
% 0.21/0.56    spl3_24),
% 0.21/0.56    inference(avatar_split_clause,[],[f78,f199])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f53,f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f54,f74])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 0.21/0.56  fof(f197,plain,(
% 0.21/0.56    spl3_23),
% 0.21/0.56    inference(avatar_split_clause,[],[f70,f195])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.57    inference(flattening,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    spl3_22),
% 0.21/0.57    inference(avatar_split_clause,[],[f68,f191])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    spl3_21),
% 0.21/0.57    inference(avatar_split_clause,[],[f64,f187])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    spl3_18 | ~spl3_3 | ~spl3_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f164,f141,f92,f168])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_3 | ~spl3_14)),
% 0.21/0.57    inference(resolution,[],[f142,f93])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    spl3_15),
% 0.21/0.57    inference(avatar_split_clause,[],[f67,f145])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.57  fof(f143,plain,(
% 0.21/0.57    spl3_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f63,f141])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    spl3_13),
% 0.21/0.57    inference(avatar_split_clause,[],[f60,f137])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    spl3_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f55,f120])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    spl3_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f56,f116])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    ~spl3_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f49,f111])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f40,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f21])).
% 0.21/0.57  fof(f21,conjecture,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    spl3_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f48,f106])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    spl3_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f47,f101])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    spl3_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f46,f96])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    spl3_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f52,f92])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f51,f88])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    spl3_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f50,f84])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,axiom,(
% 0.21/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (20208)------------------------------
% 0.21/0.57  % (20208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20208)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (20208)Memory used [KB]: 7547
% 0.21/0.57  % (20208)Time elapsed: 0.079 s
% 0.21/0.57  % (20208)------------------------------
% 0.21/0.57  % (20208)------------------------------
% 0.21/0.57  % (20200)Success in time 0.204 s
%------------------------------------------------------------------------------
