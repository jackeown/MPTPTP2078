%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:59 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  152 (1462 expanded)
%              Number of leaves         :   24 ( 456 expanded)
%              Depth                    :   19
%              Number of atoms          :  353 (3011 expanded)
%              Number of equality atoms :  128 (2147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1738,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f119,f186,f233,f1149,f1521,f1614,f1627,f1686,f1692,f1737])).

fof(f1737,plain,
    ( ~ spl5_1
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1732])).

fof(f1732,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f232,f1714])).

fof(f1714,plain,
    ( sK1 = sK2
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f97,f1696])).

fof(f1696,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f63,f1158])).

fof(f1158,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f63,f184])).

fof(f184,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_7
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f63,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f97,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_1
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f232,plain,
    ( sK1 != sK2
    | spl5_8 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl5_8
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1692,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1688])).

fof(f1688,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f180,f1681])).

fof(f1681,plain,
    ( k1_xboole_0 != sK2
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f98,f1639])).

fof(f1639,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(backward_demodulation,[],[f1584,f180])).

fof(f1584,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_4
    | spl5_7 ),
    inference(backward_demodulation,[],[f1523,f1574])).

fof(f1574,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f118,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f118,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_4
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1523,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | spl5_7 ),
    inference(backward_demodulation,[],[f63,f546])).

fof(f546,plain,
    ( k1_xboole_0 = sK1
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f261,f40,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f69,f63])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f62,f62])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f261,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | spl5_7 ),
    inference(superposition,[],[f185,f63])).

fof(f185,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f183])).

fof(f98,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f180,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1686,plain,
    ( ~ spl5_6
    | spl5_7
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1682])).

fof(f1682,plain,
    ( $false
    | ~ spl5_6
    | spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f180,f1540])).

fof(f1540,plain,
    ( k1_xboole_0 != sK2
    | spl5_7
    | spl5_8 ),
    inference(backward_demodulation,[],[f232,f546])).

fof(f1627,plain,
    ( spl5_2
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1623])).

fof(f1623,plain,
    ( $false
    | spl5_2
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f102,f546])).

fof(f102,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1614,plain,
    ( spl5_1
    | ~ spl5_4
    | spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1607])).

fof(f1607,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | spl5_6
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f81,f1580])).

fof(f1580,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl5_1
    | ~ spl5_4
    | spl5_6
    | spl5_7 ),
    inference(backward_demodulation,[],[f571,f1574])).

fof(f571,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2))
    | spl5_1
    | spl5_6
    | spl5_7 ),
    inference(backward_demodulation,[],[f202,f546])).

fof(f202,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl5_1
    | spl5_6 ),
    inference(forward_demodulation,[],[f187,f63])).

fof(f187,plain,
    ( ~ r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f98,f181,f69])).

fof(f181,plain,
    ( k1_xboole_0 != sK2
    | spl5_6 ),
    inference(avatar_component_clause,[],[f179])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1521,plain,
    ( spl5_1
    | spl5_6
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1515])).

fof(f1515,plain,
    ( $false
    | spl5_1
    | spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f1379,f1185,f1506,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1506,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f1453,f1505])).

fof(f1505,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1488,f1154])).

fof(f1154,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f1153,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1153,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f71,f41])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1488,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f50,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1453,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1436,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1436,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | ~ spl5_7 ),
    inference(superposition,[],[f1152,f1158])).

fof(f1152,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),X0) ),
    inference(backward_demodulation,[],[f70,f50])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f39])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1185,plain,
    ( r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_1
    | spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f203,f1158])).

fof(f203,plain,
    ( r2_hidden(sK3(sK2,k2_xboole_0(sK1,sK2)),sK2)
    | spl5_1
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f202,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1379,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK1)
    | spl5_1
    | spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f1186,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1186,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_1
    | spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f202,f1158])).

fof(f1149,plain,
    ( spl5_3
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1144])).

fof(f1144,plain,
    ( $false
    | spl5_3
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f985,f937,f1045,f43])).

fof(f1045,plain,
    ( ~ r2_hidden(k1_xboole_0,sK0)
    | spl5_3
    | spl5_7 ),
    inference(forward_demodulation,[],[f893,f834])).

fof(f834,plain,
    ( ! [X0] : sK0 = X0
    | spl5_3
    | spl5_7 ),
    inference(duplicate_literal_removal,[],[f832])).

fof(f832,plain,
    ( ! [X0] :
        ( sK0 = X0
        | sK0 = X0 )
    | spl5_3
    | spl5_7 ),
    inference(resolution,[],[f661,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f661,plain,
    ( ! [X0] : r2_hidden(sK0,k2_enumset1(X0,X0,X0,X0))
    | spl5_3
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f79,f590,f43])).

fof(f590,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | spl5_3
    | spl5_7 ),
    inference(backward_demodulation,[],[f329,f546])).

fof(f329,plain,
    ( r2_hidden(sK0,sK1)
    | spl5_3 ),
    inference(backward_demodulation,[],[f120,f323])).

fof(f323,plain,
    ( sK0 = sK3(sK1,sK2)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f122,f94])).

fof(f94,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(sK1,sK2))
      | sK0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(sK1,sK2))
      | sK0 = X1
      | sK0 = X1 ) ),
    inference(superposition,[],[f86,f63])).

fof(f122,plain,
    ( ! [X0] : r2_hidden(sK3(sK1,sK2),k2_xboole_0(sK1,X0))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f40,f120,f43])).

fof(f120,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f114,f44])).

fof(f114,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f79,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f35,f62])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f893,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3
    | spl5_7 ),
    inference(backward_demodulation,[],[f579,f834])).

fof(f579,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k2_xboole_0(k1_xboole_0,sK2),k2_xboole_0(k1_xboole_0,sK2),k2_xboole_0(k1_xboole_0,sK2),k2_xboole_0(k1_xboole_0,sK2)))
    | spl5_7 ),
    inference(backward_demodulation,[],[f262,f546])).

fof(f262,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)))
    | spl5_7 ),
    inference(forward_demodulation,[],[f259,f63])).

fof(f259,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f185,f185,f86])).

fof(f937,plain,
    ( ! [X3] : r2_hidden(X3,sK0)
    | spl5_3
    | spl5_7 ),
    inference(backward_demodulation,[],[f83,f834])).

fof(f83,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_enumset1(X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f985,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | spl5_3
    | spl5_7 ),
    inference(forward_demodulation,[],[f984,f834])).

fof(f984,plain,
    ( ! [X0,X1] : r1_tarski(k2_xboole_0(X0,X1),X0)
    | spl5_3
    | spl5_7 ),
    inference(forward_demodulation,[],[f838,f981])).

fof(f981,plain,
    ( ! [X0] : k5_xboole_0(sK0,X0) = X0
    | spl5_3
    | spl5_7 ),
    inference(forward_demodulation,[],[f835,f41])).

fof(f835,plain,
    ( ! [X0] : k5_xboole_0(sK0,k2_xboole_0(X0,X0)) = X0
    | spl5_3
    | spl5_7 ),
    inference(backward_demodulation,[],[f71,f834])).

fof(f838,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(sK0,k2_xboole_0(X0,X1)),X0)
    | spl5_3
    | spl5_7 ),
    inference(backward_demodulation,[],[f70,f834])).

fof(f233,plain,
    ( ~ spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f87,f183,f230])).

fof(f87,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f64])).

fof(f64,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f32,f62,f62])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f186,plain,
    ( ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f66,f183,f179])).

fof(f66,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f30,f62])).

fof(f30,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f106,f116,f112])).

fof(f106,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f89,f38])).

fof(f89,plain,(
    r1_tarski(k1_xboole_0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f79,f63])).

fof(f103,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f65,f100,f96])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f31,f62])).

fof(f31,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:14:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.07/0.51  % (29096)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.07/0.51  % (29099)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.07/0.52  % (29093)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.07/0.52  % (29092)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.07/0.52  % (29100)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.07/0.52  % (29100)Refutation not found, incomplete strategy% (29100)------------------------------
% 1.07/0.52  % (29100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.07/0.52  % (29100)Termination reason: Refutation not found, incomplete strategy
% 1.07/0.52  
% 1.07/0.52  % (29100)Memory used [KB]: 10618
% 1.07/0.52  % (29100)Time elapsed: 0.099 s
% 1.07/0.52  % (29100)------------------------------
% 1.07/0.52  % (29100)------------------------------
% 1.07/0.52  % (29110)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.07/0.52  % (29095)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.07/0.52  % (29094)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.07/0.52  % (29109)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.07/0.52  % (29101)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.07/0.53  % (29104)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.07/0.53  % (29116)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.07/0.53  % (29115)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.21/0.53  % (29106)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.21/0.53  % (29101)Refutation not found, incomplete strategy% (29101)------------------------------
% 1.21/0.53  % (29101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (29113)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.53  % (29112)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.53  % (29111)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.21/0.53  % (29101)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (29101)Memory used [KB]: 10746
% 1.21/0.53  % (29101)Time elapsed: 0.116 s
% 1.21/0.53  % (29101)------------------------------
% 1.21/0.53  % (29101)------------------------------
% 1.21/0.53  % (29107)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.21/0.53  % (29108)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.21/0.53  % (29098)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.54  % (29102)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.54  % (29114)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.21/0.54  % (29090)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.54  % (29119)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.21/0.54  % (29097)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.54  % (29091)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.54  % (29118)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.21/0.54  % (29117)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.21/0.54  % (29107)Refutation not found, incomplete strategy% (29107)------------------------------
% 1.21/0.54  % (29107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (29107)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.54  
% 1.21/0.54  % (29107)Memory used [KB]: 10618
% 1.21/0.54  % (29107)Time elapsed: 0.118 s
% 1.21/0.54  % (29107)------------------------------
% 1.21/0.54  % (29107)------------------------------
% 1.21/0.55  % (29105)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.55  % (29103)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.59  % (29094)Refutation found. Thanks to Tanya!
% 1.21/0.59  % SZS status Theorem for theBenchmark
% 1.21/0.59  % SZS output start Proof for theBenchmark
% 1.21/0.59  fof(f1738,plain,(
% 1.21/0.59    $false),
% 1.21/0.59    inference(avatar_sat_refutation,[],[f103,f119,f186,f233,f1149,f1521,f1614,f1627,f1686,f1692,f1737])).
% 1.21/0.59  fof(f1737,plain,(
% 1.21/0.59    ~spl5_1 | ~spl5_7 | spl5_8),
% 1.21/0.59    inference(avatar_contradiction_clause,[],[f1732])).
% 1.21/0.59  fof(f1732,plain,(
% 1.21/0.59    $false | (~spl5_1 | ~spl5_7 | spl5_8)),
% 1.21/0.59    inference(unit_resulting_resolution,[],[f232,f1714])).
% 1.21/0.59  fof(f1714,plain,(
% 1.21/0.59    sK1 = sK2 | (~spl5_1 | ~spl5_7)),
% 1.21/0.59    inference(forward_demodulation,[],[f97,f1696])).
% 1.21/0.59  fof(f1696,plain,(
% 1.21/0.59    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_7),
% 1.21/0.59    inference(backward_demodulation,[],[f63,f1158])).
% 1.21/0.59  fof(f1158,plain,(
% 1.21/0.59    sK1 = k2_xboole_0(sK1,sK2) | ~spl5_7),
% 1.21/0.59    inference(backward_demodulation,[],[f63,f184])).
% 1.21/0.59  fof(f184,plain,(
% 1.21/0.59    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_7),
% 1.21/0.59    inference(avatar_component_clause,[],[f183])).
% 1.21/0.59  fof(f183,plain,(
% 1.21/0.59    spl5_7 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.21/0.59  fof(f63,plain,(
% 1.21/0.59    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.21/0.59    inference(definition_unfolding,[],[f33,f62])).
% 1.21/0.59  fof(f62,plain,(
% 1.21/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.21/0.59    inference(definition_unfolding,[],[f42,f61])).
% 1.21/0.59  fof(f61,plain,(
% 1.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.21/0.59    inference(definition_unfolding,[],[f59,f60])).
% 1.21/0.59  fof(f60,plain,(
% 1.21/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.21/0.59    inference(cnf_transformation,[],[f16])).
% 1.21/0.59  fof(f16,axiom,(
% 1.21/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.21/0.59  fof(f59,plain,(
% 1.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.21/0.59    inference(cnf_transformation,[],[f15])).
% 1.21/0.59  fof(f15,axiom,(
% 1.21/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.21/0.59  fof(f42,plain,(
% 1.21/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.21/0.59    inference(cnf_transformation,[],[f14])).
% 1.21/0.59  fof(f14,axiom,(
% 1.21/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.21/0.59  fof(f33,plain,(
% 1.21/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.21/0.59    inference(cnf_transformation,[],[f27])).
% 1.21/0.59  fof(f27,plain,(
% 1.21/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.21/0.59    inference(ennf_transformation,[],[f24])).
% 1.21/0.59  fof(f24,negated_conjecture,(
% 1.21/0.59    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.21/0.59    inference(negated_conjecture,[],[f23])).
% 1.21/0.59  fof(f23,conjecture,(
% 1.21/0.59    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.21/0.59  fof(f97,plain,(
% 1.21/0.59    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_1),
% 1.21/0.59    inference(avatar_component_clause,[],[f96])).
% 1.21/0.59  fof(f96,plain,(
% 1.21/0.59    spl5_1 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.21/0.59  fof(f232,plain,(
% 1.21/0.59    sK1 != sK2 | spl5_8),
% 1.21/0.59    inference(avatar_component_clause,[],[f230])).
% 1.21/0.59  fof(f230,plain,(
% 1.21/0.59    spl5_8 <=> sK1 = sK2),
% 1.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.21/0.59  fof(f1692,plain,(
% 1.21/0.59    spl5_1 | ~spl5_4 | ~spl5_6 | spl5_7),
% 1.21/0.59    inference(avatar_contradiction_clause,[],[f1688])).
% 1.21/0.59  fof(f1688,plain,(
% 1.21/0.59    $false | (spl5_1 | ~spl5_4 | ~spl5_6 | spl5_7)),
% 1.21/0.59    inference(unit_resulting_resolution,[],[f180,f1681])).
% 1.21/0.59  fof(f1681,plain,(
% 1.21/0.59    k1_xboole_0 != sK2 | (spl5_1 | ~spl5_4 | ~spl5_6 | spl5_7)),
% 1.21/0.59    inference(forward_demodulation,[],[f98,f1639])).
% 1.21/0.59  fof(f1639,plain,(
% 1.21/0.59    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 1.21/0.59    inference(backward_demodulation,[],[f1584,f180])).
% 1.21/0.61  fof(f1584,plain,(
% 1.21/0.61    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl5_4 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f1523,f1574])).
% 1.21/0.61  fof(f1574,plain,(
% 1.21/0.61    sK2 = k2_xboole_0(k1_xboole_0,sK2) | ~spl5_4),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f118,f38])).
% 1.21/0.61  fof(f38,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.21/0.61    inference(cnf_transformation,[],[f28])).
% 1.21/0.61  fof(f28,plain,(
% 1.21/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.21/0.61    inference(ennf_transformation,[],[f7])).
% 1.21/0.61  fof(f7,axiom,(
% 1.21/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.21/0.61  fof(f118,plain,(
% 1.21/0.61    r1_tarski(k1_xboole_0,sK2) | ~spl5_4),
% 1.21/0.61    inference(avatar_component_clause,[],[f116])).
% 1.21/0.61  fof(f116,plain,(
% 1.21/0.61    spl5_4 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.21/0.61  fof(f1523,plain,(
% 1.21/0.61    k2_enumset1(sK0,sK0,sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) | spl5_7),
% 1.21/0.61    inference(backward_demodulation,[],[f63,f546])).
% 1.21/0.61  fof(f546,plain,(
% 1.21/0.61    k1_xboole_0 = sK1 | spl5_7),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f261,f40,f88])).
% 1.21/0.61  fof(f88,plain,(
% 1.21/0.61    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) )),
% 1.21/0.61    inference(superposition,[],[f69,f63])).
% 1.21/0.61  fof(f69,plain,(
% 1.21/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.21/0.61    inference(definition_unfolding,[],[f34,f62,f62])).
% 1.21/0.61  fof(f34,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.21/0.61    inference(cnf_transformation,[],[f21])).
% 1.21/0.61  fof(f21,axiom,(
% 1.21/0.61    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.21/0.61  fof(f40,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.21/0.61    inference(cnf_transformation,[],[f9])).
% 1.21/0.61  fof(f9,axiom,(
% 1.21/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.21/0.61  fof(f261,plain,(
% 1.21/0.61    sK1 != k2_xboole_0(sK1,sK2) | spl5_7),
% 1.21/0.61    inference(superposition,[],[f185,f63])).
% 1.21/0.61  fof(f185,plain,(
% 1.21/0.61    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl5_7),
% 1.21/0.61    inference(avatar_component_clause,[],[f183])).
% 1.21/0.61  fof(f98,plain,(
% 1.21/0.61    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl5_1),
% 1.21/0.61    inference(avatar_component_clause,[],[f96])).
% 1.21/0.61  fof(f180,plain,(
% 1.21/0.61    k1_xboole_0 = sK2 | ~spl5_6),
% 1.21/0.61    inference(avatar_component_clause,[],[f179])).
% 1.21/0.61  fof(f179,plain,(
% 1.21/0.61    spl5_6 <=> k1_xboole_0 = sK2),
% 1.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.21/0.61  fof(f1686,plain,(
% 1.21/0.61    ~spl5_6 | spl5_7 | spl5_8),
% 1.21/0.61    inference(avatar_contradiction_clause,[],[f1682])).
% 1.21/0.61  fof(f1682,plain,(
% 1.21/0.61    $false | (~spl5_6 | spl5_7 | spl5_8)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f180,f1540])).
% 1.21/0.61  fof(f1540,plain,(
% 1.21/0.61    k1_xboole_0 != sK2 | (spl5_7 | spl5_8)),
% 1.21/0.61    inference(backward_demodulation,[],[f232,f546])).
% 1.21/0.61  fof(f1627,plain,(
% 1.21/0.61    spl5_2 | spl5_7),
% 1.21/0.61    inference(avatar_contradiction_clause,[],[f1623])).
% 1.21/0.61  fof(f1623,plain,(
% 1.21/0.61    $false | (spl5_2 | spl5_7)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f102,f546])).
% 1.21/0.61  fof(f102,plain,(
% 1.21/0.61    k1_xboole_0 != sK1 | spl5_2),
% 1.21/0.61    inference(avatar_component_clause,[],[f100])).
% 1.21/0.61  fof(f100,plain,(
% 1.21/0.61    spl5_2 <=> k1_xboole_0 = sK1),
% 1.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.21/0.61  fof(f1614,plain,(
% 1.21/0.61    spl5_1 | ~spl5_4 | spl5_6 | spl5_7),
% 1.21/0.61    inference(avatar_contradiction_clause,[],[f1607])).
% 1.21/0.61  fof(f1607,plain,(
% 1.21/0.61    $false | (spl5_1 | ~spl5_4 | spl5_6 | spl5_7)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f81,f1580])).
% 1.21/0.61  fof(f1580,plain,(
% 1.21/0.61    ~r1_tarski(sK2,sK2) | (spl5_1 | ~spl5_4 | spl5_6 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f571,f1574])).
% 1.21/0.61  fof(f571,plain,(
% 1.21/0.61    ~r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2)) | (spl5_1 | spl5_6 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f202,f546])).
% 1.21/0.61  fof(f202,plain,(
% 1.21/0.61    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (spl5_1 | spl5_6)),
% 1.21/0.61    inference(forward_demodulation,[],[f187,f63])).
% 1.21/0.61  fof(f187,plain,(
% 1.21/0.61    ~r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_1 | spl5_6)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f98,f181,f69])).
% 1.21/0.61  fof(f181,plain,(
% 1.21/0.61    k1_xboole_0 != sK2 | spl5_6),
% 1.21/0.61    inference(avatar_component_clause,[],[f179])).
% 1.21/0.61  fof(f81,plain,(
% 1.21/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.21/0.61    inference(equality_resolution,[],[f46])).
% 1.21/0.61  fof(f46,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.21/0.61    inference(cnf_transformation,[],[f6])).
% 1.21/0.61  fof(f6,axiom,(
% 1.21/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.21/0.61  fof(f1521,plain,(
% 1.21/0.61    spl5_1 | spl5_6 | ~spl5_7),
% 1.21/0.61    inference(avatar_contradiction_clause,[],[f1515])).
% 1.21/0.61  fof(f1515,plain,(
% 1.21/0.61    $false | (spl5_1 | spl5_6 | ~spl5_7)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f1379,f1185,f1506,f43])).
% 1.21/0.61  fof(f43,plain,(
% 1.21/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.21/0.61    inference(cnf_transformation,[],[f29])).
% 1.21/0.61  fof(f29,plain,(
% 1.21/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.21/0.61    inference(ennf_transformation,[],[f3])).
% 1.21/0.61  fof(f3,axiom,(
% 1.21/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.21/0.61  fof(f1506,plain,(
% 1.21/0.61    r1_tarski(sK2,sK1) | ~spl5_7),
% 1.21/0.61    inference(backward_demodulation,[],[f1453,f1505])).
% 1.21/0.61  fof(f1505,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.21/0.61    inference(forward_demodulation,[],[f1488,f1154])).
% 1.21/0.61  fof(f1154,plain,(
% 1.21/0.61    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.21/0.61    inference(forward_demodulation,[],[f1153,f37])).
% 1.21/0.61  fof(f37,plain,(
% 1.21/0.61    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.21/0.61    inference(cnf_transformation,[],[f11])).
% 1.21/0.61  fof(f11,axiom,(
% 1.21/0.61    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.21/0.61  fof(f1153,plain,(
% 1.21/0.61    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 1.21/0.61    inference(forward_demodulation,[],[f71,f41])).
% 1.21/0.61  fof(f41,plain,(
% 1.21/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.21/0.61    inference(cnf_transformation,[],[f25])).
% 1.21/0.61  fof(f25,plain,(
% 1.21/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.21/0.61    inference(rectify,[],[f4])).
% 1.21/0.61  fof(f4,axiom,(
% 1.21/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.21/0.61  fof(f71,plain,(
% 1.21/0.61    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0) )),
% 1.21/0.61    inference(definition_unfolding,[],[f52,f39])).
% 1.21/0.61  fof(f39,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.21/0.61    inference(cnf_transformation,[],[f12])).
% 1.21/0.61  fof(f12,axiom,(
% 1.21/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.21/0.61  fof(f52,plain,(
% 1.21/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.21/0.61    inference(cnf_transformation,[],[f26])).
% 1.21/0.61  fof(f26,plain,(
% 1.21/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.21/0.61    inference(rectify,[],[f5])).
% 1.21/0.61  fof(f5,axiom,(
% 1.21/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.21/0.61  fof(f1488,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.21/0.61    inference(superposition,[],[f50,f37])).
% 1.21/0.61  fof(f50,plain,(
% 1.21/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.21/0.61    inference(cnf_transformation,[],[f10])).
% 1.21/0.61  fof(f10,axiom,(
% 1.21/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.21/0.61  fof(f1453,plain,(
% 1.21/0.61    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | ~spl5_7),
% 1.21/0.61    inference(forward_demodulation,[],[f1436,f51])).
% 1.21/0.61  fof(f51,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.21/0.61    inference(cnf_transformation,[],[f1])).
% 1.21/0.61  fof(f1,axiom,(
% 1.21/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.21/0.61  fof(f1436,plain,(
% 1.21/0.61    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | ~spl5_7),
% 1.21/0.61    inference(superposition,[],[f1152,f1158])).
% 1.21/0.61  fof(f1152,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),X0)) )),
% 1.21/0.61    inference(backward_demodulation,[],[f70,f50])).
% 1.21/0.61  fof(f70,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0)) )),
% 1.21/0.61    inference(definition_unfolding,[],[f49,f39])).
% 1.21/0.61  fof(f49,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.21/0.61    inference(cnf_transformation,[],[f8])).
% 1.21/0.61  fof(f8,axiom,(
% 1.21/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.21/0.61  fof(f1185,plain,(
% 1.21/0.61    r2_hidden(sK3(sK2,sK1),sK2) | (spl5_1 | spl5_6 | ~spl5_7)),
% 1.21/0.61    inference(forward_demodulation,[],[f203,f1158])).
% 1.21/0.61  fof(f203,plain,(
% 1.21/0.61    r2_hidden(sK3(sK2,k2_xboole_0(sK1,sK2)),sK2) | (spl5_1 | spl5_6)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f202,f44])).
% 1.21/0.61  fof(f44,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.21/0.61    inference(cnf_transformation,[],[f29])).
% 1.21/0.61  fof(f1379,plain,(
% 1.21/0.61    ~r2_hidden(sK3(sK2,sK1),sK1) | (spl5_1 | spl5_6 | ~spl5_7)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f1186,f45])).
% 1.21/0.61  fof(f45,plain,(
% 1.21/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.21/0.61    inference(cnf_transformation,[],[f29])).
% 1.21/0.61  fof(f1186,plain,(
% 1.21/0.61    ~r1_tarski(sK2,sK1) | (spl5_1 | spl5_6 | ~spl5_7)),
% 1.21/0.61    inference(forward_demodulation,[],[f202,f1158])).
% 1.21/0.61  fof(f1149,plain,(
% 1.21/0.61    spl5_3 | spl5_7),
% 1.21/0.61    inference(avatar_contradiction_clause,[],[f1144])).
% 1.21/0.61  fof(f1144,plain,(
% 1.21/0.61    $false | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f985,f937,f1045,f43])).
% 1.21/0.61  fof(f1045,plain,(
% 1.21/0.61    ~r2_hidden(k1_xboole_0,sK0) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(forward_demodulation,[],[f893,f834])).
% 1.21/0.61  fof(f834,plain,(
% 1.21/0.61    ( ! [X0] : (sK0 = X0) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(duplicate_literal_removal,[],[f832])).
% 1.21/0.61  fof(f832,plain,(
% 1.21/0.61    ( ! [X0] : (sK0 = X0 | sK0 = X0) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(resolution,[],[f661,f86])).
% 1.21/0.61  fof(f86,plain,(
% 1.21/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.21/0.61    inference(equality_resolution,[],[f74])).
% 1.21/0.61  fof(f74,plain,(
% 1.21/0.61    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.21/0.61    inference(definition_unfolding,[],[f56,f61])).
% 1.21/0.61  fof(f56,plain,(
% 1.21/0.61    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.21/0.61    inference(cnf_transformation,[],[f13])).
% 1.21/0.61  fof(f13,axiom,(
% 1.21/0.61    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.21/0.61  fof(f661,plain,(
% 1.21/0.61    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(X0,X0,X0,X0))) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f79,f590,f43])).
% 1.21/0.61  fof(f590,plain,(
% 1.21/0.61    r2_hidden(sK0,k1_xboole_0) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f329,f546])).
% 1.21/0.61  fof(f329,plain,(
% 1.21/0.61    r2_hidden(sK0,sK1) | spl5_3),
% 1.21/0.61    inference(backward_demodulation,[],[f120,f323])).
% 1.21/0.61  fof(f323,plain,(
% 1.21/0.61    sK0 = sK3(sK1,sK2) | spl5_3),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f122,f94])).
% 1.21/0.61  fof(f94,plain,(
% 1.21/0.61    ( ! [X1] : (~r2_hidden(X1,k2_xboole_0(sK1,sK2)) | sK0 = X1) )),
% 1.21/0.61    inference(duplicate_literal_removal,[],[f91])).
% 1.21/0.61  fof(f91,plain,(
% 1.21/0.61    ( ! [X1] : (~r2_hidden(X1,k2_xboole_0(sK1,sK2)) | sK0 = X1 | sK0 = X1) )),
% 1.21/0.61    inference(superposition,[],[f86,f63])).
% 1.21/0.61  fof(f122,plain,(
% 1.21/0.61    ( ! [X0] : (r2_hidden(sK3(sK1,sK2),k2_xboole_0(sK1,X0))) ) | spl5_3),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f40,f120,f43])).
% 1.21/0.61  fof(f120,plain,(
% 1.21/0.61    r2_hidden(sK3(sK1,sK2),sK1) | spl5_3),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f114,f44])).
% 1.21/0.61  fof(f114,plain,(
% 1.21/0.61    ~r1_tarski(sK1,sK2) | spl5_3),
% 1.21/0.61    inference(avatar_component_clause,[],[f112])).
% 1.21/0.61  fof(f112,plain,(
% 1.21/0.61    spl5_3 <=> r1_tarski(sK1,sK2)),
% 1.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.21/0.61  fof(f79,plain,(
% 1.21/0.61    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.21/0.61    inference(equality_resolution,[],[f68])).
% 1.21/0.61  fof(f68,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.21/0.61    inference(definition_unfolding,[],[f35,f62])).
% 1.21/0.61  fof(f35,plain,(
% 1.21/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.21/0.61    inference(cnf_transformation,[],[f21])).
% 1.21/0.61  fof(f893,plain,(
% 1.21/0.61    ~r2_hidden(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f579,f834])).
% 1.21/0.61  fof(f579,plain,(
% 1.21/0.61    ~r2_hidden(k1_xboole_0,k2_enumset1(k2_xboole_0(k1_xboole_0,sK2),k2_xboole_0(k1_xboole_0,sK2),k2_xboole_0(k1_xboole_0,sK2),k2_xboole_0(k1_xboole_0,sK2))) | spl5_7),
% 1.21/0.61    inference(backward_demodulation,[],[f262,f546])).
% 1.21/0.61  fof(f262,plain,(
% 1.21/0.61    ~r2_hidden(sK1,k2_enumset1(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))) | spl5_7),
% 1.21/0.61    inference(forward_demodulation,[],[f259,f63])).
% 1.21/0.61  fof(f259,plain,(
% 1.21/0.61    ~r2_hidden(sK1,k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_7),
% 1.21/0.61    inference(unit_resulting_resolution,[],[f185,f185,f86])).
% 1.21/0.61  fof(f937,plain,(
% 1.21/0.61    ( ! [X3] : (r2_hidden(X3,sK0)) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f83,f834])).
% 1.21/0.61  fof(f83,plain,(
% 1.21/0.61    ( ! [X0,X3] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X3))) )),
% 1.21/0.61    inference(equality_resolution,[],[f82])).
% 1.21/0.61  fof(f82,plain,(
% 1.21/0.61    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X3) != X2) )),
% 1.21/0.61    inference(equality_resolution,[],[f72])).
% 1.21/0.61  fof(f72,plain,(
% 1.21/0.61    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.21/0.61    inference(definition_unfolding,[],[f58,f61])).
% 1.21/0.61  fof(f58,plain,(
% 1.21/0.61    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.21/0.61    inference(cnf_transformation,[],[f13])).
% 1.21/0.61  fof(f985,plain,(
% 1.21/0.61    ( ! [X0] : (r1_tarski(sK0,X0)) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(forward_demodulation,[],[f984,f834])).
% 1.21/0.61  fof(f984,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X0,X1),X0)) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(forward_demodulation,[],[f838,f981])).
% 1.21/0.61  fof(f981,plain,(
% 1.21/0.61    ( ! [X0] : (k5_xboole_0(sK0,X0) = X0) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(forward_demodulation,[],[f835,f41])).
% 1.21/0.61  fof(f835,plain,(
% 1.21/0.61    ( ! [X0] : (k5_xboole_0(sK0,k2_xboole_0(X0,X0)) = X0) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f71,f834])).
% 1.21/0.61  fof(f838,plain,(
% 1.21/0.61    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(sK0,k2_xboole_0(X0,X1)),X0)) ) | (spl5_3 | spl5_7)),
% 1.21/0.61    inference(backward_demodulation,[],[f70,f834])).
% 1.21/0.61  fof(f233,plain,(
% 1.21/0.61    ~spl5_8 | ~spl5_7),
% 1.21/0.61    inference(avatar_split_clause,[],[f87,f183,f230])).
% 1.21/0.61  fof(f87,plain,(
% 1.21/0.61    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.21/0.61    inference(inner_rewriting,[],[f64])).
% 1.21/0.61  fof(f64,plain,(
% 1.21/0.61    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.21/0.61    inference(definition_unfolding,[],[f32,f62,f62])).
% 1.21/0.61  fof(f32,plain,(
% 1.21/0.61    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.21/0.61    inference(cnf_transformation,[],[f27])).
% 1.21/0.61  fof(f186,plain,(
% 1.21/0.61    ~spl5_6 | ~spl5_7),
% 1.21/0.61    inference(avatar_split_clause,[],[f66,f183,f179])).
% 1.21/0.61  fof(f66,plain,(
% 1.21/0.61    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.21/0.61    inference(definition_unfolding,[],[f30,f62])).
% 1.21/0.61  fof(f30,plain,(
% 1.21/0.61    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.21/0.61    inference(cnf_transformation,[],[f27])).
% 1.21/0.61  fof(f119,plain,(
% 1.21/0.61    ~spl5_3 | spl5_4),
% 1.21/0.61    inference(avatar_split_clause,[],[f106,f116,f112])).
% 1.21/0.61  fof(f106,plain,(
% 1.21/0.61    r1_tarski(k1_xboole_0,sK2) | ~r1_tarski(sK1,sK2)),
% 1.21/0.61    inference(superposition,[],[f89,f38])).
% 1.21/0.61  fof(f89,plain,(
% 1.21/0.61    r1_tarski(k1_xboole_0,k2_xboole_0(sK1,sK2))),
% 1.21/0.61    inference(superposition,[],[f79,f63])).
% 1.21/0.61  fof(f103,plain,(
% 1.21/0.61    ~spl5_1 | ~spl5_2),
% 1.21/0.61    inference(avatar_split_clause,[],[f65,f100,f96])).
% 1.21/0.61  fof(f65,plain,(
% 1.21/0.61    k1_xboole_0 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.21/0.61    inference(definition_unfolding,[],[f31,f62])).
% 1.21/0.61  fof(f31,plain,(
% 1.21/0.61    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.21/0.61    inference(cnf_transformation,[],[f27])).
% 1.21/0.61  % SZS output end Proof for theBenchmark
% 1.21/0.61  % (29094)------------------------------
% 1.21/0.61  % (29094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.61  % (29094)Termination reason: Refutation
% 1.21/0.61  
% 1.21/0.61  % (29094)Memory used [KB]: 6780
% 1.21/0.61  % (29094)Time elapsed: 0.167 s
% 1.21/0.61  % (29094)------------------------------
% 1.21/0.61  % (29094)------------------------------
% 1.21/0.61  % (29089)Success in time 0.239 s
%------------------------------------------------------------------------------
