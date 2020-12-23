%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 196 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 ( 462 expanded)
%              Number of equality atoms :   77 ( 186 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f120,f1317,f1346,f1363,f1369,f1383,f1439])).

fof(f1439,plain,(
    ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f1426])).

fof(f1426,plain,
    ( $false
    | ~ spl5_16 ),
    inference(resolution,[],[f1405,f1404])).

fof(f1404,plain,
    ( ! [X0] : r2_hidden(sK0,X0)
    | ~ spl5_16 ),
    inference(resolution,[],[f1276,f346])).

fof(f346,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | r2_hidden(X6,X5) ) ),
    inference(superposition,[],[f77,f319])).

fof(f319,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    inference(resolution,[],[f306,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f125,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f125,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f91,f92])).

fof(f92,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,k1_xboole_0,X1)) ),
    inference(resolution,[],[f81,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_setfam_1(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_setfam_1(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f81,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X4,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f91,plain,(
    ! [X4,X2,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X3,X4)),X4) ),
    inference(resolution,[],[f79,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f79,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f43])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f306,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X0),X1)
      | r1_tarski(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f101,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f76,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f77,f39])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1276,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1274,plain,
    ( spl5_16
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1405,plain,
    ( ! [X1] : ~ r2_hidden(sK0,X1)
    | ~ spl5_16 ),
    inference(resolution,[],[f1276,f332])).

fof(f332,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_xboole_0)
      | ~ r2_hidden(X8,X7) ) ),
    inference(superposition,[],[f76,f316])).

fof(f316,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(resolution,[],[f305,f128])).

fof(f305,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X2) ) ),
    inference(resolution,[],[f101,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1383,plain,
    ( spl5_16
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f1223,f1211,f1274])).

fof(f1211,plain,
    ( spl5_10
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1223,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_10 ),
    inference(superposition,[],[f79,f1213])).

fof(f1213,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f1369,plain,(
    spl5_25 ),
    inference(avatar_contradiction_clause,[],[f1368])).

fof(f1368,plain,
    ( $false
    | spl5_25 ),
    inference(resolution,[],[f1362,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1362,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f1360,plain,
    ( spl5_25
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1363,plain,
    ( spl5_3
    | spl5_10
    | ~ spl5_25
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1356,f1215,f1360,f1211,f114])).

fof(f114,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1215,plain,
    ( spl5_11
  <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1356,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_11 ),
    inference(superposition,[],[f34,f1217])).

fof(f1217,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f1215])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f1346,plain,
    ( spl5_10
    | spl5_11
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1345,f114,f1215,f1211])).

fof(f1345,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_3 ),
    inference(duplicate_literal_removal,[],[f1344])).

fof(f1344,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | spl5_3 ),
    inference(resolution,[],[f116,f180])).

fof(f180,plain,(
    ! [X14,X15,X13,X16] :
      ( r1_tarski(X16,k1_setfam_1(k2_enumset1(X14,X14,X13,X15)))
      | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X15
      | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X14
      | k1_xboole_0 = k2_enumset1(X14,X14,X13,X15)
      | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X13 ) ),
    inference(resolution,[],[f84,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f43])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f116,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1317,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1313,f86,f110,f114])).

fof(f110,plain,
    ( spl5_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f86,plain,
    ( spl5_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1313,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(extensionality_resolution,[],[f37,f88])).

fof(f88,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f120,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f112,f91])).

fof(f112,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f89,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f60,f86])).

fof(f60,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f25,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (16259)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (16258)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (16259)Refutation not found, incomplete strategy% (16259)------------------------------
% 0.21/0.54  % (16259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16275)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (16259)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16259)Memory used [KB]: 10618
% 0.21/0.54  % (16259)Time elapsed: 0.114 s
% 0.21/0.54  % (16259)------------------------------
% 0.21/0.54  % (16259)------------------------------
% 0.21/0.55  % (16274)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (16267)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (16266)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (16251)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (16251)Refutation not found, incomplete strategy% (16251)------------------------------
% 0.21/0.58  % (16251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (16251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (16251)Memory used [KB]: 1663
% 0.21/0.58  % (16251)Time elapsed: 0.142 s
% 0.21/0.58  % (16251)------------------------------
% 0.21/0.58  % (16251)------------------------------
% 0.21/0.58  % (16254)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (16255)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (16253)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (16256)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.59  % (16253)Refutation not found, incomplete strategy% (16253)------------------------------
% 0.21/0.59  % (16253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (16253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (16253)Memory used [KB]: 10618
% 0.21/0.59  % (16253)Time elapsed: 0.163 s
% 0.21/0.59  % (16253)------------------------------
% 0.21/0.59  % (16253)------------------------------
% 0.21/0.60  % (16264)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.60  % (16277)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.60  % (16276)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.60  % (16268)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.60  % (16270)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.60  % (16271)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.60  % (16273)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.61  % (16269)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.61  % (16271)Refutation not found, incomplete strategy% (16271)------------------------------
% 0.21/0.61  % (16271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (16271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (16271)Memory used [KB]: 10746
% 0.21/0.61  % (16271)Time elapsed: 0.172 s
% 0.21/0.61  % (16271)------------------------------
% 0.21/0.61  % (16271)------------------------------
% 0.21/0.61  % (16261)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.61  % (16257)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.61  % (16280)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.61  % (16260)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.61  % (16265)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.61  % (16261)Refutation not found, incomplete strategy% (16261)------------------------------
% 0.21/0.61  % (16261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (16261)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (16261)Memory used [KB]: 10618
% 0.21/0.61  % (16261)Time elapsed: 0.182 s
% 0.21/0.61  % (16261)------------------------------
% 0.21/0.61  % (16261)------------------------------
% 0.21/0.62  % (16263)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.62  % (16278)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.62  % (16279)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.62  % (16262)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.63  % (16262)Refutation not found, incomplete strategy% (16262)------------------------------
% 0.21/0.63  % (16262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (16262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.63  
% 0.21/0.63  % (16262)Memory used [KB]: 10618
% 0.21/0.63  % (16262)Time elapsed: 0.192 s
% 0.21/0.63  % (16262)------------------------------
% 0.21/0.63  % (16262)------------------------------
% 0.21/0.63  % (16252)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.63  % (16272)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.63  % (16272)Refutation not found, incomplete strategy% (16272)------------------------------
% 0.21/0.63  % (16272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (16272)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.63  
% 0.21/0.63  % (16272)Memory used [KB]: 1663
% 0.21/0.63  % (16272)Time elapsed: 0.202 s
% 0.21/0.63  % (16272)------------------------------
% 0.21/0.63  % (16272)------------------------------
% 0.21/0.69  % (16282)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.69  % (16267)Refutation found. Thanks to Tanya!
% 0.21/0.69  % SZS status Theorem for theBenchmark
% 0.21/0.69  % SZS output start Proof for theBenchmark
% 0.21/0.69  fof(f1440,plain,(
% 0.21/0.69    $false),
% 0.21/0.69    inference(avatar_sat_refutation,[],[f89,f120,f1317,f1346,f1363,f1369,f1383,f1439])).
% 0.21/0.69  fof(f1439,plain,(
% 0.21/0.69    ~spl5_16),
% 0.21/0.69    inference(avatar_contradiction_clause,[],[f1426])).
% 0.21/0.69  fof(f1426,plain,(
% 0.21/0.69    $false | ~spl5_16),
% 0.21/0.69    inference(resolution,[],[f1405,f1404])).
% 0.21/0.69  fof(f1404,plain,(
% 0.21/0.69    ( ! [X0] : (r2_hidden(sK0,X0)) ) | ~spl5_16),
% 0.21/0.69    inference(resolution,[],[f1276,f346])).
% 0.21/0.69  fof(f346,plain,(
% 0.21/0.69    ( ! [X6,X5] : (~r2_hidden(X6,k1_xboole_0) | r2_hidden(X6,X5)) )),
% 0.21/0.69    inference(superposition,[],[f77,f319])).
% 0.21/0.69  fof(f319,plain,(
% 0.21/0.69    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) )),
% 0.21/0.69    inference(resolution,[],[f306,f128])).
% 0.21/0.69  fof(f128,plain,(
% 0.21/0.69    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.69    inference(resolution,[],[f125,f37])).
% 0.21/0.69  fof(f37,plain,(
% 0.21/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.69    inference(cnf_transformation,[],[f3])).
% 0.21/0.69  fof(f3,axiom,(
% 0.21/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.69  fof(f125,plain,(
% 0.21/0.69    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 0.21/0.69    inference(superposition,[],[f91,f92])).
% 0.21/0.69  fof(f92,plain,(
% 0.21/0.69    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,k1_xboole_0,X1))) )),
% 0.21/0.69    inference(resolution,[],[f81,f29])).
% 0.21/0.69  fof(f29,plain,(
% 0.21/0.69    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_setfam_1(X0) = k1_xboole_0) )),
% 0.21/0.69    inference(cnf_transformation,[],[f18])).
% 0.21/0.69  fof(f18,plain,(
% 0.21/0.69    ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0))),
% 0.21/0.69    inference(ennf_transformation,[],[f13])).
% 0.21/0.69  fof(f13,axiom,(
% 0.21/0.69    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_setfam_1(X0) = k1_xboole_0)),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).
% 0.21/0.69  fof(f81,plain,(
% 0.21/0.69    ( ! [X4,X2,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X4,X2))) )),
% 0.21/0.69    inference(equality_resolution,[],[f80])).
% 0.21/0.69  fof(f80,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X4,X2) != X3) )),
% 0.21/0.69    inference(equality_resolution,[],[f66])).
% 0.21/0.69  fof(f66,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.69    inference(definition_unfolding,[],[f56,f43])).
% 0.21/0.69  fof(f43,plain,(
% 0.21/0.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.69    inference(cnf_transformation,[],[f7])).
% 0.21/0.69  fof(f7,axiom,(
% 0.21/0.69    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.69  fof(f56,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.69    inference(cnf_transformation,[],[f24])).
% 0.21/0.69  fof(f24,plain,(
% 0.21/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.69    inference(ennf_transformation,[],[f4])).
% 0.21/0.69  fof(f4,axiom,(
% 0.21/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.69  fof(f91,plain,(
% 0.21/0.69    ( ! [X4,X2,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X3,X4)),X4)) )),
% 0.21/0.69    inference(resolution,[],[f79,f31])).
% 0.21/0.69  fof(f31,plain,(
% 0.21/0.69    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.21/0.69    inference(cnf_transformation,[],[f19])).
% 0.21/0.69  fof(f19,plain,(
% 0.21/0.69    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.69    inference(ennf_transformation,[],[f12])).
% 0.21/0.69  fof(f12,axiom,(
% 0.21/0.69    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.69  fof(f79,plain,(
% 0.21/0.69    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 0.21/0.69    inference(equality_resolution,[],[f78])).
% 0.21/0.69  fof(f78,plain,(
% 0.21/0.69    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 0.21/0.69    inference(equality_resolution,[],[f65])).
% 0.21/0.69  fof(f65,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.69    inference(definition_unfolding,[],[f57,f43])).
% 0.21/0.69  fof(f57,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.69    inference(cnf_transformation,[],[f24])).
% 0.21/0.69  fof(f306,plain,(
% 0.21/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 0.21/0.69    inference(duplicate_literal_removal,[],[f296])).
% 0.21/0.69  fof(f296,plain,(
% 0.21/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1) | r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 0.21/0.69    inference(resolution,[],[f101,f100])).
% 0.21/0.69  fof(f100,plain,(
% 0.21/0.69    ( ! [X2,X0,X1] : (~r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.69    inference(resolution,[],[f76,f39])).
% 0.21/0.69  fof(f39,plain,(
% 0.21/0.69    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.69    inference(cnf_transformation,[],[f23])).
% 0.21/0.69  fof(f23,plain,(
% 0.21/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.69    inference(ennf_transformation,[],[f1])).
% 0.21/0.69  fof(f1,axiom,(
% 0.21/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.69  fof(f76,plain,(
% 0.21/0.69    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.69    inference(equality_resolution,[],[f48])).
% 0.21/0.69  fof(f48,plain,(
% 0.21/0.69    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.69    inference(cnf_transformation,[],[f2])).
% 0.21/0.69  fof(f2,axiom,(
% 0.21/0.69    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.69  fof(f101,plain,(
% 0.21/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.69    inference(resolution,[],[f77,f39])).
% 0.21/0.69  fof(f77,plain,(
% 0.21/0.69    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.21/0.69    inference(equality_resolution,[],[f47])).
% 0.21/0.69  fof(f47,plain,(
% 0.21/0.69    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.69    inference(cnf_transformation,[],[f2])).
% 0.21/0.69  fof(f1276,plain,(
% 0.21/0.69    r2_hidden(sK0,k1_xboole_0) | ~spl5_16),
% 0.21/0.69    inference(avatar_component_clause,[],[f1274])).
% 0.21/0.69  fof(f1274,plain,(
% 0.21/0.69    spl5_16 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.69  fof(f1405,plain,(
% 0.21/0.69    ( ! [X1] : (~r2_hidden(sK0,X1)) ) | ~spl5_16),
% 0.21/0.69    inference(resolution,[],[f1276,f332])).
% 0.21/0.69  fof(f332,plain,(
% 0.21/0.69    ( ! [X8,X7] : (~r2_hidden(X8,k1_xboole_0) | ~r2_hidden(X8,X7)) )),
% 0.21/0.69    inference(superposition,[],[f76,f316])).
% 0.21/0.69  fof(f316,plain,(
% 0.21/0.69    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 0.21/0.69    inference(resolution,[],[f305,f128])).
% 0.21/0.69  fof(f305,plain,(
% 0.21/0.69    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 0.21/0.69    inference(duplicate_literal_removal,[],[f297])).
% 0.21/0.69  fof(f297,plain,(
% 0.21/0.69    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2) | r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 0.21/0.69    inference(resolution,[],[f101,f40])).
% 0.21/0.69  fof(f40,plain,(
% 0.21/0.69    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.69    inference(cnf_transformation,[],[f23])).
% 0.21/0.69  fof(f1383,plain,(
% 0.21/0.69    spl5_16 | ~spl5_10),
% 0.21/0.69    inference(avatar_split_clause,[],[f1223,f1211,f1274])).
% 0.21/0.69  fof(f1211,plain,(
% 0.21/0.69    spl5_10 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.69  fof(f1223,plain,(
% 0.21/0.69    r2_hidden(sK0,k1_xboole_0) | ~spl5_10),
% 0.21/0.69    inference(superposition,[],[f79,f1213])).
% 0.21/0.69  fof(f1213,plain,(
% 0.21/0.69    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_10),
% 0.21/0.69    inference(avatar_component_clause,[],[f1211])).
% 0.21/0.69  fof(f1369,plain,(
% 0.21/0.69    spl5_25),
% 0.21/0.69    inference(avatar_contradiction_clause,[],[f1368])).
% 0.21/0.69  fof(f1368,plain,(
% 0.21/0.69    $false | spl5_25),
% 0.21/0.69    inference(resolution,[],[f1362,f73])).
% 0.21/0.69  fof(f73,plain,(
% 0.21/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.69    inference(equality_resolution,[],[f36])).
% 0.21/0.69  fof(f36,plain,(
% 0.21/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.69    inference(cnf_transformation,[],[f3])).
% 0.21/0.69  fof(f1362,plain,(
% 0.21/0.69    ~r1_tarski(sK0,sK0) | spl5_25),
% 0.21/0.69    inference(avatar_component_clause,[],[f1360])).
% 0.21/0.69  fof(f1360,plain,(
% 0.21/0.69    spl5_25 <=> r1_tarski(sK0,sK0)),
% 0.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.69  fof(f1363,plain,(
% 0.21/0.69    spl5_3 | spl5_10 | ~spl5_25 | ~spl5_11),
% 0.21/0.69    inference(avatar_split_clause,[],[f1356,f1215,f1360,f1211,f114])).
% 0.21/0.69  fof(f114,plain,(
% 0.21/0.69    spl5_3 <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.69  fof(f1215,plain,(
% 0.21/0.69    spl5_11 <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 0.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.69  fof(f1356,plain,(
% 0.21/0.69    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_11),
% 0.21/0.69    inference(superposition,[],[f34,f1217])).
% 0.21/0.69  fof(f1217,plain,(
% 0.21/0.69    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | ~spl5_11),
% 0.21/0.69    inference(avatar_component_clause,[],[f1215])).
% 0.21/0.69  fof(f34,plain,(
% 0.21/0.69    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.69    inference(cnf_transformation,[],[f22])).
% 0.21/0.69  fof(f22,plain,(
% 0.21/0.69    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.69    inference(flattening,[],[f21])).
% 0.21/0.69  fof(f21,plain,(
% 0.21/0.69    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.69    inference(ennf_transformation,[],[f14])).
% 0.21/0.69  fof(f14,axiom,(
% 0.21/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.21/0.69  fof(f1346,plain,(
% 0.21/0.69    spl5_10 | spl5_11 | spl5_3),
% 0.21/0.69    inference(avatar_split_clause,[],[f1345,f114,f1215,f1211])).
% 0.21/0.69  fof(f1345,plain,(
% 0.21/0.69    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | spl5_3),
% 0.21/0.69    inference(duplicate_literal_removal,[],[f1344])).
% 0.21/0.69  fof(f1344,plain,(
% 0.21/0.69    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | spl5_3),
% 0.21/0.69    inference(resolution,[],[f116,f180])).
% 0.21/0.69  fof(f180,plain,(
% 0.21/0.69    ( ! [X14,X15,X13,X16] : (r1_tarski(X16,k1_setfam_1(k2_enumset1(X14,X14,X13,X15))) | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X15 | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X14 | k1_xboole_0 = k2_enumset1(X14,X14,X13,X15) | sK1(k2_enumset1(X14,X14,X13,X15),X16) = X13) )),
% 0.21/0.69    inference(resolution,[],[f84,f33])).
% 0.21/0.69  fof(f33,plain,(
% 0.21/0.69    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.69    inference(cnf_transformation,[],[f22])).
% 0.21/0.69  fof(f84,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.69    inference(equality_resolution,[],[f68])).
% 0.21/0.69  fof(f68,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.69    inference(definition_unfolding,[],[f54,f43])).
% 0.21/0.69  fof(f54,plain,(
% 0.21/0.69    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.69    inference(cnf_transformation,[],[f24])).
% 0.21/0.69  fof(f116,plain,(
% 0.21/0.69    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_3),
% 0.21/0.69    inference(avatar_component_clause,[],[f114])).
% 0.21/0.69  fof(f1317,plain,(
% 0.21/0.69    ~spl5_3 | ~spl5_2 | spl5_1),
% 0.21/0.69    inference(avatar_split_clause,[],[f1313,f86,f110,f114])).
% 0.21/0.69  fof(f110,plain,(
% 0.21/0.69    spl5_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)),
% 0.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.69  fof(f86,plain,(
% 0.21/0.69    spl5_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.69  fof(f1313,plain,(
% 0.21/0.69    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_1),
% 0.21/0.69    inference(extensionality_resolution,[],[f37,f88])).
% 0.21/0.69  fof(f88,plain,(
% 0.21/0.69    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 0.21/0.69    inference(avatar_component_clause,[],[f86])).
% 0.21/0.69  fof(f120,plain,(
% 0.21/0.69    spl5_2),
% 0.21/0.69    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.69  fof(f119,plain,(
% 0.21/0.69    $false | spl5_2),
% 0.21/0.69    inference(resolution,[],[f112,f91])).
% 0.21/0.69  fof(f112,plain,(
% 0.21/0.69    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | spl5_2),
% 0.21/0.69    inference(avatar_component_clause,[],[f110])).
% 0.21/0.69  fof(f89,plain,(
% 0.21/0.69    ~spl5_1),
% 0.21/0.69    inference(avatar_split_clause,[],[f60,f86])).
% 0.21/0.69  fof(f60,plain,(
% 0.21/0.69    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.69    inference(definition_unfolding,[],[f25,f59])).
% 0.21/0.69  fof(f59,plain,(
% 0.21/0.69    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.69    inference(definition_unfolding,[],[f28,f58])).
% 0.21/0.69  fof(f58,plain,(
% 0.21/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.69    inference(definition_unfolding,[],[f30,f43])).
% 0.21/0.69  fof(f30,plain,(
% 0.21/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.69    inference(cnf_transformation,[],[f6])).
% 0.21/0.69  fof(f6,axiom,(
% 0.21/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.69  fof(f28,plain,(
% 0.21/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.69    inference(cnf_transformation,[],[f5])).
% 0.21/0.69  fof(f5,axiom,(
% 0.21/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.69  fof(f25,plain,(
% 0.21/0.69    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 0.21/0.69    inference(cnf_transformation,[],[f17])).
% 0.21/0.69  fof(f17,plain,(
% 0.21/0.69    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 0.21/0.69    inference(ennf_transformation,[],[f16])).
% 0.21/0.69  fof(f16,negated_conjecture,(
% 0.21/0.69    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.69    inference(negated_conjecture,[],[f15])).
% 0.21/0.69  fof(f15,conjecture,(
% 0.21/0.69    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.69  % SZS output end Proof for theBenchmark
% 0.21/0.69  % (16267)------------------------------
% 0.21/0.69  % (16267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.69  % (16267)Termination reason: Refutation
% 0.21/0.69  
% 0.21/0.69  % (16267)Memory used [KB]: 12409
% 0.21/0.69  % (16267)Time elapsed: 0.243 s
% 0.21/0.69  % (16267)------------------------------
% 0.21/0.69  % (16267)------------------------------
% 2.47/0.69  % (16250)Success in time 0.318 s
%------------------------------------------------------------------------------
