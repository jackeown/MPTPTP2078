%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:06 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 451 expanded)
%              Number of leaves         :   27 ( 165 expanded)
%              Depth                    :   16
%              Number of atoms          :  331 ( 867 expanded)
%              Number of equality atoms :  100 ( 443 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f434,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f100,f105,f133,f142,f190,f195,f201,f219,f237,f253,f276,f280,f286,f296,f328,f433])).

fof(f433,plain,
    ( ~ spl8_4
    | spl8_7
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl8_4
    | spl8_7
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f200,f141,f426])).

fof(f426,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,X1)
        | ~ r2_hidden(sK0,X1) )
    | ~ spl8_4 ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK1,X1)
        | r1_tarski(sK1,X1) )
    | ~ spl8_4 ),
    inference(superposition,[],[f34,f387])).

fof(f387,plain,
    ( ! [X0] :
        ( sK0 = sK5(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f345,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f345,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | sK0 = X9 )
    | ~ spl8_4 ),
    inference(superposition,[],[f73,f98])).

fof(f98,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_4
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f200,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl8_14
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f328,plain,
    ( ~ spl8_2
    | ~ spl8_5
    | ~ spl8_14
    | spl8_24 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_14
    | spl8_24 ),
    inference(unit_resulting_resolution,[],[f200,f295,f321])).

fof(f321,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ r2_hidden(sK0,X1) )
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(k1_xboole_0,X1)
        | r1_tarski(k1_xboole_0,X1) )
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(superposition,[],[f34,f257])).

fof(f257,plain,
    ( ! [X0] :
        ( sK0 = sK5(k1_xboole_0,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f256,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f256,plain,
    ( ! [X0] :
        ( sK0 = sK5(k1_xboole_0,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f163,f87])).

fof(f163,plain,
    ( ! [X0] :
        ( sK0 = sK5(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f155,f33])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK0 = X0 )
    | ~ spl8_5 ),
    inference(resolution,[],[f127,f73])).

fof(f127,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl8_5 ),
    inference(superposition,[],[f79,f104])).

fof(f104,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_5
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f51])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f295,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl8_24
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f296,plain,
    ( ~ spl8_24
    | ~ spl8_2
    | spl8_7 ),
    inference(avatar_split_clause,[],[f287,f139,f86,f293])).

fof(f287,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl8_2
    | spl8_7 ),
    inference(forward_demodulation,[],[f141,f87])).

fof(f286,plain,
    ( spl8_20
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | spl8_20
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f252,f279])).

fof(f279,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl8_23
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f252,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl8_20
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f280,plain,
    ( spl8_23
    | spl8_22
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f268,f102,f93,f273,f278])).

fof(f273,plain,
    ( spl8_22
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f93,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f268,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k1_xboole_0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k1_xboole_0)
        | r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(superposition,[],[f33,f233])).

fof(f233,plain,
    ( ! [X0] :
        ( sK0 = sK5(k1_xboole_0,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f205,f33])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sK0 = X0 )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f143,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl8_5 ),
    inference(resolution,[],[f126,f73])).

fof(f126,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f78,f104])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f276,plain,
    ( ~ spl8_22
    | ~ spl8_3
    | ~ spl8_5
    | spl8_20 ),
    inference(avatar_split_clause,[],[f269,f250,f102,f93,f273])).

fof(f269,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_5
    | spl8_20 ),
    inference(resolution,[],[f267,f252])).

fof(f267,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ r2_hidden(sK0,X1) )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(k1_xboole_0,X1)
        | r1_tarski(k1_xboole_0,X1) )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(superposition,[],[f34,f233])).

fof(f253,plain,
    ( ~ spl8_20
    | ~ spl8_2
    | spl8_16 ),
    inference(avatar_split_clause,[],[f248,f216,f86,f250])).

fof(f216,plain,
    ( spl8_16
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f248,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_2
    | spl8_16 ),
    inference(backward_demodulation,[],[f218,f87])).

fof(f218,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f216])).

fof(f237,plain,
    ( spl8_2
    | spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl8_2
    | spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f88,f132,f99,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f53,f53])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f99,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f132,plain,
    ( r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_6
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f88,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f219,plain,
    ( ~ spl8_16
    | ~ spl8_3
    | spl8_7 ),
    inference(avatar_split_clause,[],[f204,f139,f93,f216])).

fof(f204,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl8_3
    | spl8_7 ),
    inference(backward_demodulation,[],[f141,f94])).

fof(f201,plain,
    ( spl8_3
    | spl8_14
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f196,f192,f198,f93])).

fof(f192,plain,
    ( spl8_13
  <=> sK0 = sK4(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f196,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_13 ),
    inference(superposition,[],[f27,f194])).

fof(f194,plain,
    ( sK0 = sK4(sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f192])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f195,plain,
    ( spl8_3
    | spl8_13
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f150,f102,f192,f93])).

fof(f150,plain,
    ( sK0 = sK4(sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_5 ),
    inference(resolution,[],[f143,f27])).

fof(f190,plain,
    ( ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f55,f97,f82])).

fof(f82,plain,
    ( spl8_1
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f55,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f53,f53])).

fof(f22,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f142,plain,
    ( ~ spl8_7
    | spl8_1
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f120,f102,f82,f139])).

fof(f120,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl8_5 ),
    inference(superposition,[],[f104,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f133,plain,
    ( spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f121,f102,f130])).

fof(f121,plain,
    ( r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl8_5 ),
    inference(superposition,[],[f58,f104])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f52])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f105,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f54,f102])).

fof(f54,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f23,f53,f52])).

fof(f23,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f57,f97,f93])).

fof(f57,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f20,f53])).

fof(f20,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f56,f86,f82])).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f21,f53])).

fof(f21,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:50:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.47  % (4114)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.47  % (4107)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.48  % (4108)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.49  % (4120)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.49  % (4105)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (4112)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.49  % (4126)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % (4117)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.49  % (4133)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.50  % (4116)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.50  % (4109)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (4115)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (4113)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (4129)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.50  % (4121)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.51  % (4104)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.51  % (4106)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.51  % (4119)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.51  % (4130)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.51  % (4118)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.52  % (4124)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.52  % (4126)Refutation found. Thanks to Tanya!
% 1.27/0.52  % SZS status Theorem for theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f434,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(avatar_sat_refutation,[],[f89,f100,f105,f133,f142,f190,f195,f201,f219,f237,f253,f276,f280,f286,f296,f328,f433])).
% 1.27/0.52  fof(f433,plain,(
% 1.27/0.52    ~spl8_4 | spl8_7 | ~spl8_14),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f428])).
% 1.27/0.52  fof(f428,plain,(
% 1.27/0.52    $false | (~spl8_4 | spl8_7 | ~spl8_14)),
% 1.27/0.52    inference(unit_resulting_resolution,[],[f200,f141,f426])).
% 1.27/0.52  fof(f426,plain,(
% 1.27/0.52    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK0,X1)) ) | ~spl8_4),
% 1.27/0.52    inference(duplicate_literal_removal,[],[f425])).
% 1.27/0.52  fof(f425,plain,(
% 1.27/0.52    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK1,X1) | r1_tarski(sK1,X1)) ) | ~spl8_4),
% 1.27/0.52    inference(superposition,[],[f34,f387])).
% 1.27/0.52  fof(f387,plain,(
% 1.27/0.52    ( ! [X0] : (sK0 = sK5(sK1,X0) | r1_tarski(sK1,X0)) ) | ~spl8_4),
% 1.27/0.52    inference(resolution,[],[f345,f33])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f19])).
% 1.27/0.52  fof(f19,plain,(
% 1.27/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.27/0.52  fof(f345,plain,(
% 1.27/0.52    ( ! [X9] : (~r2_hidden(X9,sK1) | sK0 = X9) ) | ~spl8_4),
% 1.27/0.52    inference(superposition,[],[f73,f98])).
% 1.27/0.52  fof(f98,plain,(
% 1.27/0.52    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl8_4),
% 1.27/0.52    inference(avatar_component_clause,[],[f97])).
% 1.27/0.52  fof(f97,plain,(
% 1.27/0.52    spl8_4 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.27/0.52  fof(f73,plain,(
% 1.27/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.27/0.52    inference(equality_resolution,[],[f62])).
% 1.27/0.52  fof(f62,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.27/0.52    inference(definition_unfolding,[],[f36,f53])).
% 1.27/0.52  fof(f53,plain,(
% 1.27/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f24,f51])).
% 1.27/0.52  fof(f51,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f30,f50])).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f42,f49])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f11])).
% 1.27/0.52  fof(f11,axiom,(
% 1.27/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.27/0.52  fof(f42,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f10])).
% 1.27/0.52  fof(f10,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.27/0.52  fof(f30,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f9])).
% 1.27/0.52  fof(f9,axiom,(
% 1.27/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f8])).
% 1.27/0.52  fof(f8,axiom,(
% 1.27/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.52  fof(f36,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.27/0.52    inference(cnf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f19])).
% 1.27/0.52  fof(f141,plain,(
% 1.27/0.52    ~r1_tarski(sK1,sK2) | spl8_7),
% 1.27/0.52    inference(avatar_component_clause,[],[f139])).
% 1.27/0.52  fof(f139,plain,(
% 1.27/0.52    spl8_7 <=> r1_tarski(sK1,sK2)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.27/0.52  fof(f200,plain,(
% 1.27/0.52    r2_hidden(sK0,sK2) | ~spl8_14),
% 1.27/0.52    inference(avatar_component_clause,[],[f198])).
% 1.27/0.52  fof(f198,plain,(
% 1.27/0.52    spl8_14 <=> r2_hidden(sK0,sK2)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.27/0.52  fof(f328,plain,(
% 1.27/0.52    ~spl8_2 | ~spl8_5 | ~spl8_14 | spl8_24),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f323])).
% 1.27/0.52  fof(f323,plain,(
% 1.27/0.52    $false | (~spl8_2 | ~spl8_5 | ~spl8_14 | spl8_24)),
% 1.27/0.52    inference(unit_resulting_resolution,[],[f200,f295,f321])).
% 1.41/0.53  fof(f321,plain,(
% 1.41/0.53    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~r2_hidden(sK0,X1)) ) | (~spl8_2 | ~spl8_5)),
% 1.41/0.53    inference(duplicate_literal_removal,[],[f320])).
% 1.41/0.53  fof(f320,plain,(
% 1.41/0.53    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(k1_xboole_0,X1) | r1_tarski(k1_xboole_0,X1)) ) | (~spl8_2 | ~spl8_5)),
% 1.41/0.53    inference(superposition,[],[f34,f257])).
% 1.41/0.53  fof(f257,plain,(
% 1.41/0.53    ( ! [X0] : (sK0 = sK5(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) ) | (~spl8_2 | ~spl8_5)),
% 1.41/0.53    inference(forward_demodulation,[],[f256,f87])).
% 1.41/0.53  fof(f87,plain,(
% 1.41/0.53    k1_xboole_0 = sK1 | ~spl8_2),
% 1.41/0.53    inference(avatar_component_clause,[],[f86])).
% 1.41/0.53  fof(f86,plain,(
% 1.41/0.53    spl8_2 <=> k1_xboole_0 = sK1),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.41/0.53  fof(f256,plain,(
% 1.41/0.53    ( ! [X0] : (sK0 = sK5(k1_xboole_0,X0) | r1_tarski(sK1,X0)) ) | (~spl8_2 | ~spl8_5)),
% 1.41/0.53    inference(forward_demodulation,[],[f163,f87])).
% 1.41/0.53  fof(f163,plain,(
% 1.41/0.53    ( ! [X0] : (sK0 = sK5(sK1,X0) | r1_tarski(sK1,X0)) ) | ~spl8_5),
% 1.41/0.53    inference(resolution,[],[f155,f33])).
% 1.41/0.53  fof(f155,plain,(
% 1.41/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) ) | ~spl8_5),
% 1.41/0.53    inference(resolution,[],[f127,f73])).
% 1.41/0.53  fof(f127,plain,(
% 1.41/0.53    ( ! [X4] : (r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X4,sK1)) ) | ~spl8_5),
% 1.41/0.53    inference(superposition,[],[f79,f104])).
% 1.41/0.53  fof(f104,plain,(
% 1.41/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl8_5),
% 1.41/0.53    inference(avatar_component_clause,[],[f102])).
% 1.41/0.53  fof(f102,plain,(
% 1.41/0.53    spl8_5 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.41/0.53  fof(f79,plain,(
% 1.41/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X3,X0)) )),
% 1.41/0.53    inference(equality_resolution,[],[f68])).
% 1.41/0.53  fof(f68,plain,(
% 1.41/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 1.41/0.53    inference(definition_unfolding,[],[f47,f52])).
% 1.41/0.53  fof(f52,plain,(
% 1.41/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.41/0.53    inference(definition_unfolding,[],[f29,f51])).
% 1.41/0.53  fof(f29,plain,(
% 1.41/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f13])).
% 1.41/0.53  fof(f13,axiom,(
% 1.41/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.41/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.41/0.53  fof(f47,plain,(
% 1.41/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.41/0.53    inference(cnf_transformation,[],[f3])).
% 1.41/0.53  fof(f3,axiom,(
% 1.41/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.41/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.41/0.53  fof(f295,plain,(
% 1.41/0.53    ~r1_tarski(k1_xboole_0,sK2) | spl8_24),
% 1.41/0.53    inference(avatar_component_clause,[],[f293])).
% 1.41/0.53  fof(f293,plain,(
% 1.41/0.53    spl8_24 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.41/0.53  fof(f296,plain,(
% 1.41/0.53    ~spl8_24 | ~spl8_2 | spl8_7),
% 1.41/0.53    inference(avatar_split_clause,[],[f287,f139,f86,f293])).
% 1.41/0.53  fof(f287,plain,(
% 1.41/0.53    ~r1_tarski(k1_xboole_0,sK2) | (~spl8_2 | spl8_7)),
% 1.41/0.53    inference(forward_demodulation,[],[f141,f87])).
% 1.41/0.53  fof(f286,plain,(
% 1.41/0.53    spl8_20 | ~spl8_23),
% 1.41/0.53    inference(avatar_contradiction_clause,[],[f281])).
% 1.41/0.53  fof(f281,plain,(
% 1.41/0.53    $false | (spl8_20 | ~spl8_23)),
% 1.41/0.53    inference(unit_resulting_resolution,[],[f252,f279])).
% 1.41/0.53  fof(f279,plain,(
% 1.41/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl8_23),
% 1.41/0.53    inference(avatar_component_clause,[],[f278])).
% 1.41/0.53  fof(f278,plain,(
% 1.41/0.53    spl8_23 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.41/0.53  fof(f252,plain,(
% 1.41/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl8_20),
% 1.41/0.53    inference(avatar_component_clause,[],[f250])).
% 1.41/0.53  fof(f250,plain,(
% 1.41/0.53    spl8_20 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.41/0.53  fof(f280,plain,(
% 1.41/0.53    spl8_23 | spl8_22 | ~spl8_3 | ~spl8_5),
% 1.41/0.53    inference(avatar_split_clause,[],[f268,f102,f93,f273,f278])).
% 1.41/0.53  fof(f273,plain,(
% 1.41/0.53    spl8_22 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.41/0.53  fof(f93,plain,(
% 1.41/0.53    spl8_3 <=> k1_xboole_0 = sK2),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.41/0.53  fof(f268,plain,(
% 1.41/0.53    ( ! [X0] : (r2_hidden(sK0,k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) ) | (~spl8_3 | ~spl8_5)),
% 1.41/0.53    inference(duplicate_literal_removal,[],[f265])).
% 1.41/0.53  fof(f265,plain,(
% 1.41/0.53    ( ! [X0] : (r2_hidden(sK0,k1_xboole_0) | r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) ) | (~spl8_3 | ~spl8_5)),
% 1.41/0.53    inference(superposition,[],[f33,f233])).
% 1.41/0.53  fof(f233,plain,(
% 1.41/0.53    ( ! [X0] : (sK0 = sK5(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) ) | (~spl8_3 | ~spl8_5)),
% 1.41/0.53    inference(resolution,[],[f205,f33])).
% 1.41/0.53  fof(f205,plain,(
% 1.41/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) ) | (~spl8_3 | ~spl8_5)),
% 1.41/0.53    inference(backward_demodulation,[],[f143,f94])).
% 1.41/0.53  fof(f94,plain,(
% 1.41/0.53    k1_xboole_0 = sK2 | ~spl8_3),
% 1.41/0.53    inference(avatar_component_clause,[],[f93])).
% 1.41/0.53  fof(f143,plain,(
% 1.41/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl8_5),
% 1.41/0.53    inference(resolution,[],[f126,f73])).
% 1.41/0.53  fof(f126,plain,(
% 1.41/0.53    ( ! [X3] : (r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X3,sK2)) ) | ~spl8_5),
% 1.41/0.53    inference(superposition,[],[f78,f104])).
% 1.41/0.53  fof(f78,plain,(
% 1.41/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.41/0.53    inference(equality_resolution,[],[f67])).
% 1.41/0.53  fof(f67,plain,(
% 1.41/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 1.41/0.53    inference(definition_unfolding,[],[f48,f52])).
% 1.41/0.53  fof(f48,plain,(
% 1.41/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.41/0.53    inference(cnf_transformation,[],[f3])).
% 1.41/0.53  fof(f276,plain,(
% 1.41/0.53    ~spl8_22 | ~spl8_3 | ~spl8_5 | spl8_20),
% 1.41/0.53    inference(avatar_split_clause,[],[f269,f250,f102,f93,f273])).
% 1.41/0.53  fof(f269,plain,(
% 1.41/0.53    ~r2_hidden(sK0,k1_xboole_0) | (~spl8_3 | ~spl8_5 | spl8_20)),
% 1.41/0.53    inference(resolution,[],[f267,f252])).
% 1.41/0.53  fof(f267,plain,(
% 1.41/0.53    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~r2_hidden(sK0,X1)) ) | (~spl8_3 | ~spl8_5)),
% 1.41/0.53    inference(duplicate_literal_removal,[],[f266])).
% 1.41/0.53  fof(f266,plain,(
% 1.41/0.53    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(k1_xboole_0,X1) | r1_tarski(k1_xboole_0,X1)) ) | (~spl8_3 | ~spl8_5)),
% 1.41/0.53    inference(superposition,[],[f34,f233])).
% 1.41/0.53  fof(f253,plain,(
% 1.41/0.53    ~spl8_20 | ~spl8_2 | spl8_16),
% 1.41/0.53    inference(avatar_split_clause,[],[f248,f216,f86,f250])).
% 1.41/0.53  fof(f216,plain,(
% 1.41/0.53    spl8_16 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.41/0.53  fof(f248,plain,(
% 1.41/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl8_2 | spl8_16)),
% 1.41/0.53    inference(backward_demodulation,[],[f218,f87])).
% 1.41/0.53  fof(f218,plain,(
% 1.41/0.53    ~r1_tarski(sK1,k1_xboole_0) | spl8_16),
% 1.41/0.53    inference(avatar_component_clause,[],[f216])).
% 1.41/0.53  fof(f237,plain,(
% 1.41/0.53    spl8_2 | spl8_4 | ~spl8_6),
% 1.41/0.53    inference(avatar_contradiction_clause,[],[f234])).
% 1.41/0.53  fof(f234,plain,(
% 1.41/0.53    $false | (spl8_2 | spl8_4 | ~spl8_6)),
% 1.41/0.53    inference(unit_resulting_resolution,[],[f88,f132,f99,f66])).
% 1.41/0.53  fof(f66,plain,(
% 1.41/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.41/0.53    inference(definition_unfolding,[],[f39,f53,f53])).
% 1.41/0.53  fof(f39,plain,(
% 1.41/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f12])).
% 1.41/0.53  fof(f12,axiom,(
% 1.41/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.41/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.41/0.53  fof(f99,plain,(
% 1.41/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl8_4),
% 1.41/0.53    inference(avatar_component_clause,[],[f97])).
% 1.41/0.53  fof(f132,plain,(
% 1.41/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl8_6),
% 1.41/0.53    inference(avatar_component_clause,[],[f130])).
% 1.41/0.53  fof(f130,plain,(
% 1.41/0.53    spl8_6 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.41/0.53  fof(f88,plain,(
% 1.41/0.53    k1_xboole_0 != sK1 | spl8_2),
% 1.41/0.53    inference(avatar_component_clause,[],[f86])).
% 1.41/0.53  fof(f219,plain,(
% 1.41/0.53    ~spl8_16 | ~spl8_3 | spl8_7),
% 1.41/0.53    inference(avatar_split_clause,[],[f204,f139,f93,f216])).
% 1.41/0.53  fof(f204,plain,(
% 1.41/0.53    ~r1_tarski(sK1,k1_xboole_0) | (~spl8_3 | spl8_7)),
% 1.41/0.53    inference(backward_demodulation,[],[f141,f94])).
% 1.41/0.53  fof(f201,plain,(
% 1.41/0.53    spl8_3 | spl8_14 | ~spl8_13),
% 1.41/0.53    inference(avatar_split_clause,[],[f196,f192,f198,f93])).
% 1.41/0.53  fof(f192,plain,(
% 1.41/0.53    spl8_13 <=> sK0 = sK4(sK2)),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.41/0.53  fof(f196,plain,(
% 1.41/0.53    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl8_13),
% 1.41/0.53    inference(superposition,[],[f27,f194])).
% 1.41/0.53  fof(f194,plain,(
% 1.41/0.53    sK0 = sK4(sK2) | ~spl8_13),
% 1.41/0.53    inference(avatar_component_clause,[],[f192])).
% 1.41/0.53  fof(f27,plain,(
% 1.41/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.41/0.53    inference(cnf_transformation,[],[f17])).
% 1.41/0.53  fof(f17,plain,(
% 1.41/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.41/0.53    inference(ennf_transformation,[],[f4])).
% 1.41/0.53  fof(f4,axiom,(
% 1.41/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.41/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.41/0.53  fof(f195,plain,(
% 1.41/0.53    spl8_3 | spl8_13 | ~spl8_5),
% 1.41/0.53    inference(avatar_split_clause,[],[f150,f102,f192,f93])).
% 1.41/0.53  fof(f150,plain,(
% 1.41/0.53    sK0 = sK4(sK2) | k1_xboole_0 = sK2 | ~spl8_5),
% 1.41/0.53    inference(resolution,[],[f143,f27])).
% 1.41/0.53  fof(f190,plain,(
% 1.41/0.53    ~spl8_1 | ~spl8_4),
% 1.41/0.53    inference(avatar_split_clause,[],[f55,f97,f82])).
% 1.41/0.53  fof(f82,plain,(
% 1.41/0.53    spl8_1 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.41/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.41/0.53  fof(f55,plain,(
% 1.41/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.41/0.53    inference(definition_unfolding,[],[f22,f53,f53])).
% 1.41/0.53  fof(f22,plain,(
% 1.41/0.53    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.41/0.53    inference(cnf_transformation,[],[f16])).
% 1.41/0.53  fof(f16,plain,(
% 1.41/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.41/0.53    inference(ennf_transformation,[],[f15])).
% 1.41/0.53  fof(f15,negated_conjecture,(
% 1.41/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.41/0.53    inference(negated_conjecture,[],[f14])).
% 1.41/0.53  fof(f14,conjecture,(
% 1.41/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.41/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.41/0.53  fof(f142,plain,(
% 1.41/0.53    ~spl8_7 | spl8_1 | ~spl8_5),
% 1.41/0.53    inference(avatar_split_clause,[],[f120,f102,f82,f139])).
% 1.41/0.53  fof(f120,plain,(
% 1.41/0.53    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl8_5),
% 1.41/0.53    inference(superposition,[],[f104,f59])).
% 1.41/0.53  fof(f59,plain,(
% 1.41/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.41/0.53    inference(definition_unfolding,[],[f31,f52])).
% 1.41/0.53  fof(f31,plain,(
% 1.41/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.41/0.53    inference(cnf_transformation,[],[f18])).
% 1.41/0.53  fof(f18,plain,(
% 1.41/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.41/0.53    inference(ennf_transformation,[],[f5])).
% 1.41/0.53  fof(f5,axiom,(
% 1.41/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.41/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.41/0.53  fof(f133,plain,(
% 1.41/0.53    spl8_6 | ~spl8_5),
% 1.41/0.53    inference(avatar_split_clause,[],[f121,f102,f130])).
% 1.41/0.53  fof(f121,plain,(
% 1.41/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl8_5),
% 1.41/0.53    inference(superposition,[],[f58,f104])).
% 1.41/0.53  fof(f58,plain,(
% 1.41/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.41/0.53    inference(definition_unfolding,[],[f28,f52])).
% 1.41/0.53  fof(f28,plain,(
% 1.41/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f6])).
% 1.41/0.53  fof(f6,axiom,(
% 1.41/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.41/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.41/0.53  fof(f105,plain,(
% 1.41/0.53    spl8_5),
% 1.41/0.53    inference(avatar_split_clause,[],[f54,f102])).
% 1.41/0.53  fof(f54,plain,(
% 1.41/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.41/0.53    inference(definition_unfolding,[],[f23,f53,f52])).
% 1.41/0.53  fof(f23,plain,(
% 1.41/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.41/0.53    inference(cnf_transformation,[],[f16])).
% 1.41/0.53  fof(f100,plain,(
% 1.41/0.53    ~spl8_3 | ~spl8_4),
% 1.41/0.53    inference(avatar_split_clause,[],[f57,f97,f93])).
% 1.41/0.53  fof(f57,plain,(
% 1.41/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.41/0.53    inference(definition_unfolding,[],[f20,f53])).
% 1.41/0.53  fof(f20,plain,(
% 1.41/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.41/0.53    inference(cnf_transformation,[],[f16])).
% 1.41/0.53  fof(f89,plain,(
% 1.41/0.53    ~spl8_1 | ~spl8_2),
% 1.41/0.53    inference(avatar_split_clause,[],[f56,f86,f82])).
% 1.41/0.53  fof(f56,plain,(
% 1.41/0.53    k1_xboole_0 != sK1 | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.41/0.53    inference(definition_unfolding,[],[f21,f53])).
% 1.41/0.53  fof(f21,plain,(
% 1.41/0.53    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.41/0.53    inference(cnf_transformation,[],[f16])).
% 1.41/0.53  % SZS output end Proof for theBenchmark
% 1.41/0.53  % (4126)------------------------------
% 1.41/0.53  % (4126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.53  % (4126)Termination reason: Refutation
% 1.41/0.53  
% 1.41/0.53  % (4126)Memory used [KB]: 10874
% 1.41/0.53  % (4126)Time elapsed: 0.075 s
% 1.41/0.53  % (4126)------------------------------
% 1.41/0.53  % (4126)------------------------------
% 1.41/0.53  % (4099)Success in time 0.186 s
%------------------------------------------------------------------------------
