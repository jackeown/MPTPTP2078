%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:20 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 276 expanded)
%              Number of leaves         :   24 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 ( 551 expanded)
%              Number of equality atoms :   65 ( 223 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f116,f183,f1307,f1318,f1322,f1328,f1381,f1386,f1388])).

fof(f1388,plain,
    ( ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f1387])).

fof(f1387,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f1380,f114,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f114,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1380,plain,
    ( r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f1378,plain,
    ( spl3_7
  <=> r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1386,plain,
    ( ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f1382])).

fof(f1382,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f105,f1380,f307])).

fof(f307,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f73,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f55,f69,f69])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f105,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_1
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1381,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f1342,f108,f1378])).

fof(f108,plain,
    ( spl3_2
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1342,plain,
    ( r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f84,f110])).

fof(f110,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f84,plain,(
    ! [X2,X1] : r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(superposition,[],[f79,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1328,plain,
    ( spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f1325])).

fof(f1325,plain,
    ( $false
    | spl3_1
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f106,f155,f1317,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1317,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f1315,plain,
    ( spl3_6
  <=> r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f155,plain,(
    ! [X0,X1] : r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(resolution,[],[f75,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f106,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1322,plain,
    ( spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1319])).

fof(f1319,plain,
    ( $false
    | spl3_3
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f115,f156,f1313,f48])).

fof(f1313,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f1311])).

fof(f1311,plain,
    ( spl3_5
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f156,plain,(
    ! [X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f76,f80])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f1318,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f1309,f1304,f1315,f1311])).

fof(f1304,plain,
    ( spl3_4
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1309,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f1308])).

fof(f1308,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_4 ),
    inference(superposition,[],[f1306,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f69,f69])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f1306,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f1304])).

fof(f1307,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f539,f108,f1304])).

fof(f539,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_2 ),
    inference(forward_demodulation,[],[f533,f54])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f533,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl3_2 ),
    inference(superposition,[],[f109,f266])).

fof(f266,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f244,f64])).

fof(f244,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f60,f65])).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f109,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f183,plain,
    ( spl3_3
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f157,f108,f104,f113])).

fof(f157,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f70,f64])).

fof(f70,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f43,f69,f56,f69])).

fof(f43,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f116,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f102,f108,f113])).

fof(f102,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f72,f64])).

fof(f72,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f41,f69,f56,f69])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f101,f108,f104])).

fof(f101,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f71,f64])).

fof(f71,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f42,f69,f56,f69])).

fof(f42,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (1888)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (1874)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (1874)Refutation not found, incomplete strategy% (1874)------------------------------
% 0.21/0.51  % (1874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1874)Memory used [KB]: 6140
% 0.21/0.51  % (1874)Time elapsed: 0.115 s
% 0.21/0.51  % (1874)------------------------------
% 0.21/0.51  % (1874)------------------------------
% 0.21/0.52  % (1870)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (1865)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (1866)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (1864)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (1875)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (1872)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (1864)Refutation not found, incomplete strategy% (1864)------------------------------
% 0.21/0.53  % (1864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1864)Memory used [KB]: 1663
% 0.21/0.53  % (1864)Time elapsed: 0.126 s
% 0.21/0.53  % (1864)------------------------------
% 0.21/0.53  % (1864)------------------------------
% 0.21/0.54  % (1868)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (1891)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (1863)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (1881)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (1891)Refutation not found, incomplete strategy% (1891)------------------------------
% 0.21/0.54  % (1891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1891)Memory used [KB]: 10746
% 0.21/0.54  % (1891)Time elapsed: 0.140 s
% 0.21/0.54  % (1891)------------------------------
% 0.21/0.54  % (1891)------------------------------
% 0.21/0.54  % (1886)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (1882)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.55  % (1867)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.55  % (1873)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.55  % (1890)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.55  % (1879)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.55  % (1884)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.55  % (1878)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.55  % (1887)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.55  % (1873)Refutation not found, incomplete strategy% (1873)------------------------------
% 1.31/0.55  % (1873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (1889)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.56  % (1889)Refutation not found, incomplete strategy% (1889)------------------------------
% 1.31/0.56  % (1889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (1889)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (1889)Memory used [KB]: 6140
% 1.31/0.56  % (1889)Time elapsed: 0.149 s
% 1.31/0.56  % (1889)------------------------------
% 1.31/0.56  % (1889)------------------------------
% 1.31/0.56  % (1871)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.56  % (1873)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (1873)Memory used [KB]: 10746
% 1.31/0.56  % (1873)Time elapsed: 0.151 s
% 1.31/0.56  % (1873)------------------------------
% 1.31/0.56  % (1873)------------------------------
% 1.31/0.56  % (1885)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.57  % (1876)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.61/0.57  % (1879)Refutation not found, incomplete strategy% (1879)------------------------------
% 1.61/0.57  % (1879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (1879)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (1879)Memory used [KB]: 10618
% 1.61/0.57  % (1879)Time elapsed: 0.166 s
% 1.61/0.57  % (1879)------------------------------
% 1.61/0.57  % (1879)------------------------------
% 1.61/0.58  % (1892)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.61/0.58  % (1892)Refutation not found, incomplete strategy% (1892)------------------------------
% 1.61/0.58  % (1892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (1892)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (1892)Memory used [KB]: 1663
% 1.61/0.58  % (1892)Time elapsed: 0.002 s
% 1.61/0.58  % (1892)------------------------------
% 1.61/0.58  % (1892)------------------------------
% 1.61/0.58  % (1883)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.61/0.58  % (1877)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.61/0.59  % (1880)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.61/0.59  % (1880)Refutation not found, incomplete strategy% (1880)------------------------------
% 1.61/0.59  % (1880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (1880)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (1880)Memory used [KB]: 1663
% 1.61/0.59  % (1880)Time elapsed: 0.179 s
% 1.61/0.59  % (1880)------------------------------
% 1.61/0.59  % (1880)------------------------------
% 1.61/0.59  % (1869)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.59  % (1877)Refutation not found, incomplete strategy% (1877)------------------------------
% 1.61/0.59  % (1877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (1877)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (1877)Memory used [KB]: 1663
% 1.61/0.59  % (1877)Time elapsed: 0.092 s
% 1.61/0.59  % (1877)------------------------------
% 1.61/0.59  % (1877)------------------------------
% 1.61/0.64  % (1913)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.10/0.66  % (1914)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.10/0.67  % (1866)Refutation not found, incomplete strategy% (1866)------------------------------
% 2.10/0.67  % (1866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.67  % (1866)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.67  
% 2.10/0.67  % (1866)Memory used [KB]: 6140
% 2.10/0.67  % (1866)Time elapsed: 0.268 s
% 2.10/0.67  % (1866)------------------------------
% 2.10/0.67  % (1866)------------------------------
% 2.29/0.68  % (1916)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.29/0.69  % (1915)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.29/0.69  % (1915)Refutation not found, incomplete strategy% (1915)------------------------------
% 2.29/0.69  % (1915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.69  % (1915)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.69  
% 2.29/0.69  % (1915)Memory used [KB]: 6140
% 2.29/0.69  % (1915)Time elapsed: 0.114 s
% 2.29/0.69  % (1915)------------------------------
% 2.29/0.69  % (1915)------------------------------
% 2.29/0.70  % (1917)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.29/0.70  % (1886)Refutation found. Thanks to Tanya!
% 2.29/0.70  % SZS status Theorem for theBenchmark
% 2.29/0.70  % SZS output start Proof for theBenchmark
% 2.29/0.70  fof(f1389,plain,(
% 2.29/0.70    $false),
% 2.29/0.70    inference(avatar_sat_refutation,[],[f111,f116,f183,f1307,f1318,f1322,f1328,f1381,f1386,f1388])).
% 2.29/0.70  fof(f1388,plain,(
% 2.29/0.70    ~spl3_3 | ~spl3_7),
% 2.29/0.70    inference(avatar_contradiction_clause,[],[f1387])).
% 2.29/0.70  fof(f1387,plain,(
% 2.29/0.70    $false | (~spl3_3 | ~spl3_7)),
% 2.29/0.70    inference(unit_resulting_resolution,[],[f1380,f114,f73])).
% 2.29/0.70  fof(f73,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f44,f69])).
% 2.29/0.70  fof(f69,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f58,f68])).
% 2.29/0.70  fof(f68,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f66,f67])).
% 2.29/0.70  fof(f67,plain,(
% 2.29/0.70    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f16])).
% 2.29/0.70  fof(f16,axiom,(
% 2.29/0.70    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.29/0.70  fof(f66,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f15])).
% 2.29/0.70  fof(f15,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.29/0.70  fof(f58,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f14])).
% 2.29/0.70  fof(f14,axiom,(
% 2.29/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.29/0.70  fof(f44,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f27])).
% 2.29/0.70  fof(f27,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.29/0.70    inference(ennf_transformation,[],[f22])).
% 2.29/0.70  fof(f22,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 2.29/0.70  fof(f114,plain,(
% 2.29/0.70    r2_hidden(sK0,sK2) | ~spl3_3),
% 2.29/0.70    inference(avatar_component_clause,[],[f113])).
% 2.29/0.70  fof(f113,plain,(
% 2.29/0.70    spl3_3 <=> r2_hidden(sK0,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.29/0.70  fof(f1380,plain,(
% 2.29/0.70    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_7),
% 2.29/0.70    inference(avatar_component_clause,[],[f1378])).
% 2.29/0.70  fof(f1378,plain,(
% 2.29/0.70    spl3_7 <=> r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.29/0.70  fof(f1386,plain,(
% 2.29/0.70    ~spl3_1 | ~spl3_7),
% 2.29/0.70    inference(avatar_contradiction_clause,[],[f1382])).
% 2.29/0.70  fof(f1382,plain,(
% 2.29/0.70    $false | (~spl3_1 | ~spl3_7)),
% 2.29/0.70    inference(unit_resulting_resolution,[],[f105,f1380,f307])).
% 2.29/0.70  fof(f307,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),X2) | ~r2_hidden(X0,X2)) )),
% 2.29/0.70    inference(superposition,[],[f73,f78])).
% 2.29/0.70  fof(f78,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f55,f69,f69])).
% 2.29/0.70  fof(f55,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f13])).
% 2.29/0.70  fof(f13,axiom,(
% 2.29/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.29/0.70  fof(f105,plain,(
% 2.29/0.70    r2_hidden(sK1,sK2) | ~spl3_1),
% 2.29/0.70    inference(avatar_component_clause,[],[f104])).
% 2.29/0.70  fof(f104,plain,(
% 2.29/0.70    spl3_1 <=> r2_hidden(sK1,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.29/0.70  fof(f1381,plain,(
% 2.29/0.70    spl3_7 | ~spl3_2),
% 2.29/0.70    inference(avatar_split_clause,[],[f1342,f108,f1378])).
% 2.29/0.70  fof(f108,plain,(
% 2.29/0.70    spl3_2 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.29/0.70  fof(f1342,plain,(
% 2.29/0.70    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_2),
% 2.29/0.70    inference(superposition,[],[f84,f110])).
% 2.29/0.70  fof(f110,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl3_2),
% 2.29/0.70    inference(avatar_component_clause,[],[f108])).
% 2.29/0.70  fof(f84,plain,(
% 2.29/0.70    ( ! [X2,X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)) )),
% 2.29/0.70    inference(superposition,[],[f79,f64])).
% 2.29/0.70  fof(f64,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f1])).
% 2.29/0.70  fof(f1,axiom,(
% 2.29/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.29/0.70  fof(f79,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f57,f56])).
% 2.29/0.70  fof(f56,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f7])).
% 2.29/0.70  fof(f7,axiom,(
% 2.29/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.29/0.70  fof(f57,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f10])).
% 2.29/0.70  fof(f10,axiom,(
% 2.29/0.70    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.29/0.70  fof(f1328,plain,(
% 2.29/0.70    spl3_1 | spl3_6),
% 2.29/0.70    inference(avatar_contradiction_clause,[],[f1325])).
% 2.29/0.70  fof(f1325,plain,(
% 2.29/0.70    $false | (spl3_1 | spl3_6)),
% 2.29/0.70    inference(unit_resulting_resolution,[],[f106,f155,f1317,f48])).
% 2.29/0.70  fof(f48,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f36])).
% 2.29/0.70  fof(f36,plain,(
% 2.29/0.70    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.29/0.70    inference(nnf_transformation,[],[f28])).
% 2.29/0.70  fof(f28,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.29/0.70    inference(ennf_transformation,[],[f5])).
% 2.29/0.70  fof(f5,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.29/0.70  fof(f1317,plain,(
% 2.29/0.70    ~r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_6),
% 2.29/0.70    inference(avatar_component_clause,[],[f1315])).
% 2.29/0.70  fof(f1315,plain,(
% 2.29/0.70    spl3_6 <=> r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.29/0.70  fof(f155,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0))) )),
% 2.29/0.70    inference(resolution,[],[f75,f80])).
% 2.29/0.70  fof(f80,plain,(
% 2.29/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.29/0.70    inference(equality_resolution,[],[f62])).
% 2.29/0.70  fof(f62,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.29/0.70    inference(cnf_transformation,[],[f40])).
% 2.29/0.70  fof(f40,plain,(
% 2.29/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/0.70    inference(flattening,[],[f39])).
% 2.29/0.70  fof(f39,plain,(
% 2.29/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/0.70    inference(nnf_transformation,[],[f6])).
% 2.29/0.70  fof(f6,axiom,(
% 2.29/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.29/0.70  fof(f75,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f50,f69])).
% 2.29/0.70  fof(f50,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f38])).
% 2.29/0.70  fof(f38,plain,(
% 2.29/0.70    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.29/0.70    inference(flattening,[],[f37])).
% 2.29/0.70  fof(f37,plain,(
% 2.29/0.70    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.29/0.70    inference(nnf_transformation,[],[f20])).
% 2.29/0.70  fof(f20,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.29/0.70  fof(f106,plain,(
% 2.29/0.70    ~r2_hidden(sK1,sK2) | spl3_1),
% 2.29/0.70    inference(avatar_component_clause,[],[f104])).
% 2.29/0.70  fof(f1322,plain,(
% 2.29/0.70    spl3_3 | spl3_5),
% 2.29/0.70    inference(avatar_contradiction_clause,[],[f1319])).
% 2.29/0.70  fof(f1319,plain,(
% 2.29/0.70    $false | (spl3_3 | spl3_5)),
% 2.29/0.70    inference(unit_resulting_resolution,[],[f115,f156,f1313,f48])).
% 2.29/0.70  fof(f1313,plain,(
% 2.29/0.70    ~r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_5),
% 2.29/0.70    inference(avatar_component_clause,[],[f1311])).
% 2.29/0.70  fof(f1311,plain,(
% 2.29/0.70    spl3_5 <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.29/0.70  fof(f156,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.29/0.70    inference(resolution,[],[f76,f80])).
% 2.29/0.70  fof(f76,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f49,f69])).
% 2.29/0.70  fof(f49,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f38])).
% 2.29/0.70  fof(f115,plain,(
% 2.29/0.70    ~r2_hidden(sK0,sK2) | spl3_3),
% 2.29/0.70    inference(avatar_component_clause,[],[f113])).
% 2.29/0.70  fof(f1318,plain,(
% 2.29/0.70    ~spl3_5 | ~spl3_6 | spl3_4),
% 2.29/0.70    inference(avatar_split_clause,[],[f1309,f1304,f1315,f1311])).
% 2.29/0.70  fof(f1304,plain,(
% 2.29/0.70    spl3_4 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.29/0.70  fof(f1309,plain,(
% 2.29/0.70    ~r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_4),
% 2.29/0.70    inference(trivial_inequality_removal,[],[f1308])).
% 2.29/0.70  fof(f1308,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_4),
% 2.29/0.70    inference(superposition,[],[f1306,f77])).
% 2.29/0.70  fof(f77,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f52,f69,f69])).
% 2.29/0.70  fof(f52,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f30])).
% 2.29/0.70  fof(f30,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 2.29/0.70    inference(flattening,[],[f29])).
% 2.29/0.70  fof(f29,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 2.29/0.70    inference(ennf_transformation,[],[f21])).
% 2.29/0.70  fof(f21,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 2.29/0.70  fof(f1306,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_4),
% 2.29/0.70    inference(avatar_component_clause,[],[f1304])).
% 2.29/0.70  fof(f1307,plain,(
% 2.29/0.70    ~spl3_4 | spl3_2),
% 2.29/0.70    inference(avatar_split_clause,[],[f539,f108,f1304])).
% 2.29/0.70  fof(f539,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_2),
% 2.29/0.70    inference(forward_demodulation,[],[f533,f54])).
% 2.29/0.70  fof(f54,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f2])).
% 2.29/0.70  fof(f2,axiom,(
% 2.29/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.29/0.70  fof(f533,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl3_2),
% 2.29/0.70    inference(superposition,[],[f109,f266])).
% 2.29/0.70  fof(f266,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.29/0.70    inference(forward_demodulation,[],[f244,f64])).
% 2.29/0.70  fof(f244,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 2.29/0.70    inference(superposition,[],[f60,f65])).
% 2.29/0.70  fof(f65,plain,(
% 2.29/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.29/0.70    inference(cnf_transformation,[],[f25])).
% 2.29/0.70  fof(f25,plain,(
% 2.29/0.70    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.29/0.70    inference(rectify,[],[f3])).
% 2.29/0.70  fof(f3,axiom,(
% 2.29/0.70    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.29/0.70  fof(f60,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f8])).
% 2.29/0.70  fof(f8,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.29/0.70  fof(f109,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_2),
% 2.29/0.70    inference(avatar_component_clause,[],[f108])).
% 2.29/0.70  fof(f183,plain,(
% 2.29/0.70    spl3_3 | spl3_1 | ~spl3_2),
% 2.29/0.70    inference(avatar_split_clause,[],[f157,f108,f104,f113])).
% 2.29/0.70  fof(f157,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 2.29/0.70    inference(forward_demodulation,[],[f70,f64])).
% 2.29/0.70  fof(f70,plain,(
% 2.29/0.70    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.29/0.70    inference(definition_unfolding,[],[f43,f69,f56,f69])).
% 2.29/0.70  fof(f43,plain,(
% 2.29/0.70    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.29/0.70    inference(cnf_transformation,[],[f35])).
% 2.29/0.70  fof(f35,plain,(
% 2.29/0.70    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.29/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).
% 2.29/0.70  fof(f34,plain,(
% 2.29/0.70    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 2.29/0.70    introduced(choice_axiom,[])).
% 2.29/0.70  fof(f33,plain,(
% 2.29/0.70    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.29/0.70    inference(flattening,[],[f32])).
% 2.29/0.70  fof(f32,plain,(
% 2.29/0.70    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.29/0.70    inference(nnf_transformation,[],[f26])).
% 2.29/0.70  fof(f26,plain,(
% 2.29/0.70    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.29/0.70    inference(ennf_transformation,[],[f24])).
% 2.29/0.70  fof(f24,negated_conjecture,(
% 2.29/0.70    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.29/0.70    inference(negated_conjecture,[],[f23])).
% 2.29/0.70  fof(f23,conjecture,(
% 2.29/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.29/0.70  fof(f116,plain,(
% 2.29/0.70    ~spl3_3 | spl3_2),
% 2.29/0.70    inference(avatar_split_clause,[],[f102,f108,f113])).
% 2.29/0.70  fof(f102,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 2.29/0.70    inference(forward_demodulation,[],[f72,f64])).
% 2.29/0.70  fof(f72,plain,(
% 2.29/0.70    ~r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.29/0.70    inference(definition_unfolding,[],[f41,f69,f56,f69])).
% 2.29/0.70  fof(f41,plain,(
% 2.29/0.70    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.29/0.70    inference(cnf_transformation,[],[f35])).
% 2.29/0.70  fof(f111,plain,(
% 2.29/0.70    ~spl3_1 | spl3_2),
% 2.29/0.70    inference(avatar_split_clause,[],[f101,f108,f104])).
% 2.29/0.70  fof(f101,plain,(
% 2.29/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 2.29/0.70    inference(forward_demodulation,[],[f71,f64])).
% 2.29/0.70  fof(f71,plain,(
% 2.29/0.70    ~r2_hidden(sK1,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.29/0.70    inference(definition_unfolding,[],[f42,f69,f56,f69])).
% 2.29/0.70  fof(f42,plain,(
% 2.29/0.70    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.29/0.70    inference(cnf_transformation,[],[f35])).
% 2.29/0.70  % SZS output end Proof for theBenchmark
% 2.29/0.70  % (1886)------------------------------
% 2.29/0.70  % (1886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.70  % (1886)Termination reason: Refutation
% 2.29/0.70  
% 2.29/0.70  % (1886)Memory used [KB]: 12153
% 2.29/0.70  % (1886)Time elapsed: 0.285 s
% 2.29/0.70  % (1886)------------------------------
% 2.29/0.70  % (1886)------------------------------
% 2.29/0.71  % (1860)Success in time 0.337 s
%------------------------------------------------------------------------------
