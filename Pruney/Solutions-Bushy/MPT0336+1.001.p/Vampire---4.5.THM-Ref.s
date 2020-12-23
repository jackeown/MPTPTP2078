%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0336+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 261 expanded)
%              Number of leaves         :   43 ( 127 expanded)
%              Depth                    :    7
%              Number of atoms          :  372 ( 650 expanded)
%              Number of equality atoms :   84 ( 155 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1552,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f62,f66,f70,f74,f78,f82,f86,f90,f98,f102,f106,f117,f139,f147,f154,f166,f172,f193,f199,f210,f222,f261,f303,f1012,f1117,f1264,f1519,f1551])).

fof(f1551,plain,
    ( ~ spl4_8
    | ~ spl4_155
    | spl4_187 ),
    inference(avatar_contradiction_clause,[],[f1550])).

fof(f1550,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_155
    | spl4_187 ),
    inference(subsumption_resolution,[],[f1547,f1263])).

fof(f1263,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_155 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1261,plain,
    ( spl4_155
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_155])])).

fof(f1547,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | ~ spl4_8
    | spl4_187 ),
    inference(superposition,[],[f1518,f73])).

fof(f73,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1518,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK0)
    | spl4_187 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f1516,plain,
    ( spl4_187
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_187])])).

fof(f1519,plain,
    ( ~ spl4_187
    | spl4_21
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f1502,f1115,f143,f1516])).

fof(f143,plain,
    ( spl4_21
  <=> k1_xboole_0 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1115,plain,
    ( spl4_134
  <=> ! [X32] : k3_xboole_0(sK1,X32) = k3_xboole_0(sK1,k2_xboole_0(X32,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f1502,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK0)
    | spl4_21
    | ~ spl4_134 ),
    inference(superposition,[],[f145,f1116])).

fof(f1116,plain,
    ( ! [X32] : k3_xboole_0(sK1,X32) = k3_xboole_0(sK1,k2_xboole_0(X32,sK2))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f1115])).

fof(f145,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1264,plain,
    ( spl4_155
    | ~ spl4_23
    | ~ spl4_31
    | ~ spl4_41
    | ~ spl4_113 ),
    inference(avatar_split_clause,[],[f1259,f1010,f300,f216,f160,f1261])).

fof(f160,plain,
    ( spl4_23
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f216,plain,
    ( spl4_31
  <=> sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f300,plain,
    ( spl4_41
  <=> ! [X1,X2] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1010,plain,
    ( spl4_113
  <=> ! [X32] : k3_xboole_0(sK1,X32) = k3_xboole_0(sK1,k2_xboole_0(sK2,X32)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).

fof(f1259,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_23
    | ~ spl4_31
    | ~ spl4_41
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f1258,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1258,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK2)
    | ~ spl4_31
    | ~ spl4_41
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f1245,f301])).

fof(f301,plain,
    ( ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f300])).

fof(f1245,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl4_31
    | ~ spl4_113 ),
    inference(superposition,[],[f1011,f218])).

fof(f218,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1011,plain,
    ( ! [X32] : k3_xboole_0(sK1,X32) = k3_xboole_0(sK1,k2_xboole_0(sK2,X32))
    | ~ spl4_113 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f1117,plain,
    ( spl4_134
    | ~ spl4_7
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1113,f160,f112,f100,f68,f1115])).

fof(f68,plain,
    ( spl4_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f100,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f112,plain,
    ( spl4_17
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1113,plain,
    ( ! [X32] : k3_xboole_0(sK1,X32) = k3_xboole_0(sK1,k2_xboole_0(X32,sK2))
    | ~ spl4_7
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f1112,f113])).

fof(f113,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1112,plain,
    ( ! [X32] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X32)) = k3_xboole_0(sK1,k2_xboole_0(X32,sK2))
    | ~ spl4_7
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f932,f69])).

fof(f69,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f932,plain,
    ( ! [X32] : k3_xboole_0(sK1,k2_xboole_0(X32,sK2)) = k2_xboole_0(k3_xboole_0(sK1,X32),k1_xboole_0)
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(superposition,[],[f101,f162])).

fof(f101,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1012,plain,
    ( spl4_113
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1008,f160,f112,f100,f1010])).

fof(f1008,plain,
    ( ! [X32] : k3_xboole_0(sK1,X32) = k3_xboole_0(sK1,k2_xboole_0(sK2,X32))
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f907,f113])).

fof(f907,plain,
    ( ! [X32] : k3_xboole_0(sK1,k2_xboole_0(sK2,X32)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X32))
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(superposition,[],[f101,f162])).

fof(f303,plain,
    ( spl4_41
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f291,f259,f72,f300])).

fof(f259,plain,
    ( spl4_35
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f291,plain,
    ( ! [X4,X3] : k3_xboole_0(X4,X3) = k3_xboole_0(X3,k3_xboole_0(X4,X3))
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(superposition,[],[f260,f73])).

fof(f260,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl4_35
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f246,f96,f64,f259])).

fof(f64,plain,
    ( spl4_6
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f96,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f246,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(superposition,[],[f97,f65])).

fof(f65,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f97,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f222,plain,
    ( spl4_31
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f214,f207,f68,f216])).

fof(f207,plain,
    ( spl4_30
  <=> sK2 = k2_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f214,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(superposition,[],[f69,f209])).

fof(f209,plain,
    ( sK2 = k2_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f207])).

fof(f210,plain,
    ( spl4_30
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f201,f196,f76,f207])).

fof(f76,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f196,plain,
    ( spl4_28
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f201,plain,
    ( sK2 = k2_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(resolution,[],[f198,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f198,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f194,f191,f50,f196])).

fof(f50,plain,
    ( spl4_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f191,plain,
    ( spl4_27
  <=> ! [X0] :
        ( r1_tarski(k3_xboole_0(sK0,sK1),X0)
        | ~ r2_hidden(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f194,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(resolution,[],[f192,f52])).

fof(f52,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | r1_tarski(k3_xboole_0(sK0,sK1),X0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl4_27
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f189,f170,f88,f191])).

fof(f88,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f170,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK3),X0)
        | r1_tarski(k3_xboole_0(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f189,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(sK0,sK1),X0)
        | ~ r2_hidden(sK3,X0) )
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(resolution,[],[f171,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK3),X0)
        | r1_tarski(k3_xboole_0(sK0,sK1),X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( spl4_24
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f167,f104,f55,f170])).

fof(f55,plain,
    ( spl4_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f104,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK3),X0)
        | r1_tarski(k3_xboole_0(sK0,sK1),X0) )
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(resolution,[],[f105,f57])).

fof(f57,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f166,plain,
    ( spl4_23
    | ~ spl4_8
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f158,f151,f72,f160])).

fof(f151,plain,
    ( spl4_22
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f158,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl4_8
    | ~ spl4_22 ),
    inference(superposition,[],[f73,f153])).

fof(f153,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f148,f84,f45,f151])).

fof(f45,plain,
    ( spl4_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f148,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f147,plain,
    ( ~ spl4_21
    | ~ spl4_8
    | spl4_20 ),
    inference(avatar_split_clause,[],[f141,f136,f72,f143])).

fof(f136,plain,
    ( spl4_20
  <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f141,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl4_8
    | spl4_20 ),
    inference(superposition,[],[f138,f73])).

fof(f138,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( ~ spl4_20
    | spl4_1
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f134,f80,f40,f136])).

fof(f40,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f80,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f134,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl4_1
    | ~ spl4_10 ),
    inference(resolution,[],[f81,f42])).

fof(f42,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f117,plain,
    ( spl4_17
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f110,f68,f60,f112])).

fof(f60,plain,
    ( spl4_5
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f110,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f61,f69])).

fof(f61,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f106,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f38,f104])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f102,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f37,f100])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f98,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f36,f96])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f90,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f86,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f32,f84])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f82,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f74,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f66,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f62,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19])).

fof(f19,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f40])).

fof(f26,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
