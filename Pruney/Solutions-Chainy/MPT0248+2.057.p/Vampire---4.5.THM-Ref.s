%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:57 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 531 expanded)
%              Number of leaves         :   47 ( 201 expanded)
%              Depth                    :   14
%              Number of atoms          :  332 ( 828 expanded)
%              Number of equality atoms :  116 ( 499 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f109,f114,f119,f598,f956,f976,f1041,f1125,f1146,f1309,f1327,f1337,f1350,f1395,f1760,f2376,f2385,f2386,f2395,f2400,f2461])).

fof(f2461,plain,
    ( spl5_2
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f2460,f111,f97,f102])).

fof(f102,plain,
    ( spl5_2
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f97,plain,
    ( spl5_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f111,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2460,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f2401,f217])).

fof(f217,plain,(
    ! [X0] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(resolution,[],[f90,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f62,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2401,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f99,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f99,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f2400,plain,
    ( spl5_4
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f2399,f692,f111])).

fof(f692,plain,
    ( spl5_29
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f2399,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_29 ),
    inference(resolution,[],[f694,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f694,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f692])).

fof(f2395,plain,
    ( spl5_29
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f1789,f1742,f692])).

fof(f1742,plain,
    ( spl5_120
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f1789,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_120 ),
    inference(resolution,[],[f1743,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1743,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f1742])).

fof(f2386,plain,
    ( sK1 != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2385,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK1 != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2376,plain,
    ( spl5_30
    | spl5_123 ),
    inference(avatar_split_clause,[],[f2374,f1757,f696])).

fof(f696,plain,
    ( spl5_30
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1757,plain,
    ( spl5_123
  <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f2374,plain,
    ( r2_hidden(sK0,sK1)
    | spl5_123 ),
    inference(resolution,[],[f1759,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1759,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl5_123 ),
    inference(avatar_component_clause,[],[f1757])).

fof(f1760,plain,
    ( ~ spl5_123
    | spl5_120
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f1725,f284,f1742,f1757])).

fof(f284,plain,
    ( spl5_13
  <=> sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1725,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) )
    | ~ spl5_13 ),
    inference(superposition,[],[f130,f286])).

fof(f286,plain,
    ( sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f284])).

fof(f130,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f58,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1395,plain,
    ( spl5_13
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1392,f97,f284])).

fof(f1392,plain,
    ( sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_1 ),
    inference(superposition,[],[f188,f99])).

fof(f188,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))) = X5 ),
    inference(resolution,[],[f86,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1350,plain,
    ( spl5_91
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f705,f696,f1345])).

fof(f1345,plain,
    ( spl5_91
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f705,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_30 ),
    inference(resolution,[],[f698,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(definition_unfolding,[],[f61,f81,f81])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f698,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f696])).

fof(f1337,plain,
    ( spl5_61
    | ~ spl5_3
    | ~ spl5_89 ),
    inference(avatar_split_clause,[],[f1336,f1324,f106,f1049])).

fof(f1049,plain,
    ( spl5_61
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f106,plain,
    ( spl5_3
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1324,plain,
    ( spl5_89
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f1336,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_3
    | ~ spl5_89 ),
    inference(forward_demodulation,[],[f1332,f107])).

fof(f107,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1332,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)
    | ~ spl5_89 ),
    inference(resolution,[],[f1326,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f64,f81])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1326,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f1324])).

fof(f1327,plain,
    ( spl5_89
    | ~ spl5_3
    | spl5_59 ),
    inference(avatar_split_clause,[],[f1316,f1038,f106,f1324])).

fof(f1038,plain,
    ( spl5_59
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f1316,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3
    | spl5_59 ),
    inference(resolution,[],[f593,f1040])).

fof(f1040,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_59 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f593,plain,
    ( ! [X2] :
        ( r1_xboole_0(sK1,X2)
        | r2_hidden(sK0,X2) )
    | ~ spl5_3 ),
    inference(superposition,[],[f88,f107])).

fof(f1309,plain,
    ( spl5_23
    | ~ spl5_26
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f1308,f1049,f641,f595])).

fof(f595,plain,
    ( spl5_23
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f641,plain,
    ( spl5_26
  <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1308,plain,
    ( sK1 = sK2
    | ~ spl5_26
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f1298,f643])).

fof(f643,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f641])).

fof(f1298,plain,
    ( sK2 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_61 ),
    inference(resolution,[],[f1051,f90])).

fof(f1051,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1146,plain,
    ( spl5_5
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f1145,f1122,f116])).

fof(f116,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1122,plain,
    ( spl5_68
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f1145,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_68 ),
    inference(resolution,[],[f1124,f50])).

fof(f1124,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1125,plain,
    ( spl5_68
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f1119,f1023,f1122])).

fof(f1023,plain,
    ( spl5_56
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1119,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_56 ),
    inference(resolution,[],[f1024,f51])).

fof(f1024,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f1041,plain,
    ( ~ spl5_59
    | spl5_56
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f998,f973,f1023,f1038])).

fof(f973,plain,
    ( spl5_51
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f998,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r1_xboole_0(sK1,sK2) )
    | ~ spl5_51 ),
    inference(superposition,[],[f130,f975])).

fof(f975,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f973])).

fof(f976,plain,
    ( spl5_51
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f965,f953,f973])).

fof(f953,plain,
    ( spl5_49
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f965,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_49 ),
    inference(resolution,[],[f955,f63])).

fof(f955,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f953])).

fof(f956,plain,
    ( spl5_49
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f951,f641,f953])).

fof(f951,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f947,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f947,plain,
    ( r1_tarski(k5_xboole_0(sK2,k1_xboole_0),sK1)
    | ~ spl5_26 ),
    inference(superposition,[],[f655,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f655,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1)
    | ~ spl5_26 ),
    inference(superposition,[],[f225,f643])).

fof(f225,plain,(
    ! [X4,X2,X3] : r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))) ),
    inference(resolution,[],[f95,f87])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ) ),
    inference(definition_unfolding,[],[f69,f80])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f598,plain,
    ( ~ spl5_23
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f588,f106,f102,f595])).

fof(f588,plain,
    ( sK1 != sK2
    | spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f104,f107])).

fof(f104,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f119,plain,
    ( ~ spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f85,f106,f116])).

fof(f85,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f42,f81])).

fof(f42,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f114,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f84,f111,f102])).

fof(f84,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f43,f81])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f83,f106,f102])).

fof(f83,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f81,f81])).

fof(f44,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f100,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f82,f97])).

fof(f82,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f45,f81,f80])).

fof(f45,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (7825)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (7838)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (7849)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (7842)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (7830)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (7833)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (7835)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (7827)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (7844)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (7829)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (7845)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (7837)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (7839)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (7824)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7846)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (7850)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (7821)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (7831)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (7841)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (7823)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (7832)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (7822)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (7826)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (7847)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (7843)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (7840)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (7836)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (7836)Refutation not found, incomplete strategy% (7836)------------------------------
% 0.20/0.56  % (7836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (7836)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (7836)Memory used [KB]: 6140
% 0.20/0.56  % (7836)Time elapsed: 0.002 s
% 0.20/0.56  % (7836)------------------------------
% 0.20/0.56  % (7836)------------------------------
% 0.20/0.56  % (7848)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (7828)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % (7834)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.99/0.61  % (7837)Refutation found. Thanks to Tanya!
% 1.99/0.61  % SZS status Theorem for theBenchmark
% 2.08/0.63  % SZS output start Proof for theBenchmark
% 2.08/0.63  fof(f2656,plain,(
% 2.08/0.63    $false),
% 2.08/0.63    inference(avatar_sat_refutation,[],[f100,f109,f114,f119,f598,f956,f976,f1041,f1125,f1146,f1309,f1327,f1337,f1350,f1395,f1760,f2376,f2385,f2386,f2395,f2400,f2461])).
% 2.08/0.63  fof(f2461,plain,(
% 2.08/0.63    spl5_2 | ~spl5_1 | ~spl5_4),
% 2.08/0.63    inference(avatar_split_clause,[],[f2460,f111,f97,f102])).
% 2.08/0.63  fof(f102,plain,(
% 2.08/0.63    spl5_2 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.08/0.63  fof(f97,plain,(
% 2.08/0.63    spl5_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.08/0.63  fof(f111,plain,(
% 2.08/0.63    spl5_4 <=> k1_xboole_0 = sK1),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.08/0.63  fof(f2460,plain,(
% 2.08/0.63    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl5_1 | ~spl5_4)),
% 2.08/0.63    inference(forward_demodulation,[],[f2401,f217])).
% 2.08/0.63  fof(f217,plain,(
% 2.08/0.63    ( ! [X0] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 2.08/0.63    inference(resolution,[],[f90,f46])).
% 2.08/0.63  fof(f46,plain,(
% 2.08/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f12])).
% 2.08/0.63  fof(f12,axiom,(
% 2.08/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.08/0.63  fof(f90,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 2.08/0.63    inference(definition_unfolding,[],[f62,f80])).
% 2.08/0.63  fof(f80,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.08/0.63    inference(definition_unfolding,[],[f55,f79])).
% 2.08/0.63  fof(f79,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f56,f78])).
% 2.08/0.63  fof(f78,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f68,f77])).
% 2.08/0.63  fof(f77,plain,(
% 2.08/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f71,f76])).
% 2.08/0.63  fof(f76,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f72,f75])).
% 2.08/0.63  fof(f75,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f73,f74])).
% 2.08/0.63  fof(f74,plain,(
% 2.08/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f22])).
% 2.08/0.63  fof(f22,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.08/0.63  fof(f73,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f21])).
% 2.08/0.63  fof(f21,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.08/0.63  fof(f72,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f20])).
% 2.08/0.63  fof(f20,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.08/0.63  fof(f71,plain,(
% 2.08/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f19])).
% 2.08/0.63  fof(f19,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.08/0.63  fof(f68,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f18])).
% 2.08/0.63  fof(f18,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.08/0.63  fof(f56,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f17])).
% 2.08/0.63  fof(f17,axiom,(
% 2.08/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.08/0.63  fof(f55,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f26])).
% 2.08/0.63  fof(f26,axiom,(
% 2.08/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.08/0.63  fof(f62,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.08/0.63    inference(cnf_transformation,[],[f37])).
% 2.08/0.63  fof(f37,plain,(
% 2.08/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f8])).
% 2.08/0.63  fof(f8,axiom,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.08/0.63  fof(f2401,plain,(
% 2.08/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | (~spl5_1 | ~spl5_4)),
% 2.08/0.63    inference(backward_demodulation,[],[f99,f112])).
% 2.08/0.63  fof(f112,plain,(
% 2.08/0.63    k1_xboole_0 = sK1 | ~spl5_4),
% 2.08/0.63    inference(avatar_component_clause,[],[f111])).
% 2.08/0.63  fof(f99,plain,(
% 2.08/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_1),
% 2.08/0.63    inference(avatar_component_clause,[],[f97])).
% 2.08/0.63  fof(f2400,plain,(
% 2.08/0.63    spl5_4 | ~spl5_29),
% 2.08/0.63    inference(avatar_split_clause,[],[f2399,f692,f111])).
% 2.08/0.63  fof(f692,plain,(
% 2.08/0.63    spl5_29 <=> v1_xboole_0(sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.08/0.63  fof(f2399,plain,(
% 2.08/0.63    k1_xboole_0 = sK1 | ~spl5_29),
% 2.08/0.63    inference(resolution,[],[f694,f50])).
% 2.08/0.63  fof(f50,plain,(
% 2.08/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.08/0.63    inference(cnf_transformation,[],[f32])).
% 2.08/0.63  fof(f32,plain,(
% 2.08/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f3])).
% 2.08/0.63  fof(f3,axiom,(
% 2.08/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.08/0.63  fof(f694,plain,(
% 2.08/0.63    v1_xboole_0(sK1) | ~spl5_29),
% 2.08/0.63    inference(avatar_component_clause,[],[f692])).
% 2.08/0.63  fof(f2395,plain,(
% 2.08/0.63    spl5_29 | ~spl5_120),
% 2.08/0.63    inference(avatar_split_clause,[],[f1789,f1742,f692])).
% 2.08/0.63  fof(f1742,plain,(
% 2.08/0.63    spl5_120 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).
% 2.08/0.63  fof(f1789,plain,(
% 2.08/0.63    v1_xboole_0(sK1) | ~spl5_120),
% 2.08/0.63    inference(resolution,[],[f1743,f51])).
% 2.08/0.63  fof(f51,plain,(
% 2.08/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f33])).
% 2.08/0.63  fof(f33,plain,(
% 2.08/0.63    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f30])).
% 2.08/0.63  fof(f30,plain,(
% 2.08/0.63    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 2.08/0.63    inference(unused_predicate_definition_removal,[],[f2])).
% 2.08/0.63  fof(f2,axiom,(
% 2.08/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.08/0.63  fof(f1743,plain,(
% 2.08/0.63    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl5_120),
% 2.08/0.63    inference(avatar_component_clause,[],[f1742])).
% 2.08/0.63  fof(f2386,plain,(
% 2.08/0.63    sK1 != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.08/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.08/0.63  fof(f2385,plain,(
% 2.08/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK1 != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.08/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.08/0.63  fof(f2376,plain,(
% 2.08/0.63    spl5_30 | spl5_123),
% 2.08/0.63    inference(avatar_split_clause,[],[f2374,f1757,f696])).
% 2.08/0.63  fof(f696,plain,(
% 2.08/0.63    spl5_30 <=> r2_hidden(sK0,sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.08/0.63  fof(f1757,plain,(
% 2.08/0.63    spl5_123 <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 2.08/0.63  fof(f2374,plain,(
% 2.08/0.63    r2_hidden(sK0,sK1) | spl5_123),
% 2.08/0.63    inference(resolution,[],[f1759,f88])).
% 2.08/0.63  fof(f88,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f60,f81])).
% 2.08/0.63  fof(f81,plain,(
% 2.08/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f49,f79])).
% 2.08/0.63  fof(f49,plain,(
% 2.08/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f16])).
% 2.08/0.63  fof(f16,axiom,(
% 2.08/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.08/0.63  fof(f60,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f35])).
% 2.08/0.63  fof(f35,plain,(
% 2.08/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f24])).
% 2.08/0.63  fof(f24,axiom,(
% 2.08/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.08/0.63  fof(f1759,plain,(
% 2.08/0.63    ~r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl5_123),
% 2.08/0.63    inference(avatar_component_clause,[],[f1757])).
% 2.08/0.63  fof(f1760,plain,(
% 2.08/0.63    ~spl5_123 | spl5_120 | ~spl5_13),
% 2.08/0.63    inference(avatar_split_clause,[],[f1725,f284,f1742,f1757])).
% 2.08/0.63  fof(f284,plain,(
% 2.08/0.63    spl5_13 <=> sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.08/0.63  fof(f1725,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ) | ~spl5_13),
% 2.08/0.63    inference(superposition,[],[f130,f286])).
% 2.08/0.63  fof(f286,plain,(
% 2.08/0.63    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_13),
% 2.08/0.63    inference(avatar_component_clause,[],[f284])).
% 2.08/0.63  fof(f130,plain,(
% 2.08/0.63    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 2.08/0.63    inference(superposition,[],[f58,f54])).
% 2.08/0.63  fof(f54,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f1])).
% 2.08/0.63  fof(f1,axiom,(
% 2.08/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.08/0.63  fof(f58,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f34])).
% 2.08/0.63  fof(f34,plain,(
% 2.08/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.08/0.63    inference(ennf_transformation,[],[f29])).
% 2.08/0.63  fof(f29,plain,(
% 2.08/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.08/0.63    inference(rectify,[],[f4])).
% 2.08/0.63  fof(f4,axiom,(
% 2.08/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.08/0.63  fof(f1395,plain,(
% 2.08/0.63    spl5_13 | ~spl5_1),
% 2.08/0.63    inference(avatar_split_clause,[],[f1392,f97,f284])).
% 2.08/0.63  fof(f1392,plain,(
% 2.08/0.63    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_1),
% 2.08/0.63    inference(superposition,[],[f188,f99])).
% 2.08/0.63  fof(f188,plain,(
% 2.08/0.63    ( ! [X6,X5] : (k3_xboole_0(X5,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))) = X5) )),
% 2.08/0.63    inference(resolution,[],[f86,f63])).
% 2.08/0.63  fof(f63,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.08/0.63    inference(cnf_transformation,[],[f38])).
% 2.08/0.63  fof(f38,plain,(
% 2.08/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f10])).
% 2.08/0.63  fof(f10,axiom,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.08/0.63  fof(f86,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.08/0.63    inference(definition_unfolding,[],[f52,f80])).
% 2.08/0.63  fof(f52,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f15])).
% 2.08/0.63  fof(f15,axiom,(
% 2.08/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.08/0.63  fof(f1350,plain,(
% 2.08/0.63    spl5_91 | ~spl5_30),
% 2.08/0.63    inference(avatar_split_clause,[],[f705,f696,f1345])).
% 2.08/0.63  fof(f1345,plain,(
% 2.08/0.63    spl5_91 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 2.08/0.63  fof(f705,plain,(
% 2.08/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_30),
% 2.08/0.63    inference(resolution,[],[f698,f89])).
% 2.08/0.63  fof(f89,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 2.08/0.63    inference(definition_unfolding,[],[f61,f81,f81])).
% 2.08/0.63  fof(f61,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f36])).
% 2.08/0.63  fof(f36,plain,(
% 2.08/0.63    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f25])).
% 2.08/0.63  fof(f25,axiom,(
% 2.08/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 2.08/0.63  fof(f698,plain,(
% 2.08/0.63    r2_hidden(sK0,sK1) | ~spl5_30),
% 2.08/0.63    inference(avatar_component_clause,[],[f696])).
% 2.08/0.63  fof(f1337,plain,(
% 2.08/0.63    spl5_61 | ~spl5_3 | ~spl5_89),
% 2.08/0.63    inference(avatar_split_clause,[],[f1336,f1324,f106,f1049])).
% 2.08/0.63  fof(f1049,plain,(
% 2.08/0.63    spl5_61 <=> r1_tarski(sK1,sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 2.08/0.63  fof(f106,plain,(
% 2.08/0.63    spl5_3 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.08/0.63  fof(f1324,plain,(
% 2.08/0.63    spl5_89 <=> r2_hidden(sK0,sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 2.08/0.63  fof(f1336,plain,(
% 2.08/0.63    r1_tarski(sK1,sK2) | (~spl5_3 | ~spl5_89)),
% 2.08/0.63    inference(forward_demodulation,[],[f1332,f107])).
% 2.08/0.63  fof(f107,plain,(
% 2.08/0.63    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_3),
% 2.08/0.63    inference(avatar_component_clause,[],[f106])).
% 2.08/0.63  fof(f1332,plain,(
% 2.08/0.63    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) | ~spl5_89),
% 2.08/0.63    inference(resolution,[],[f1326,f92])).
% 2.08/0.63  fof(f92,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f64,f81])).
% 2.08/0.63  fof(f64,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f23])).
% 2.08/0.63  fof(f23,axiom,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.08/0.63  fof(f1326,plain,(
% 2.08/0.63    r2_hidden(sK0,sK2) | ~spl5_89),
% 2.08/0.63    inference(avatar_component_clause,[],[f1324])).
% 2.08/0.63  fof(f1327,plain,(
% 2.08/0.63    spl5_89 | ~spl5_3 | spl5_59),
% 2.08/0.63    inference(avatar_split_clause,[],[f1316,f1038,f106,f1324])).
% 2.08/0.63  fof(f1038,plain,(
% 2.08/0.63    spl5_59 <=> r1_xboole_0(sK1,sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 2.08/0.63  fof(f1316,plain,(
% 2.08/0.63    r2_hidden(sK0,sK2) | (~spl5_3 | spl5_59)),
% 2.08/0.63    inference(resolution,[],[f593,f1040])).
% 2.08/0.63  fof(f1040,plain,(
% 2.08/0.63    ~r1_xboole_0(sK1,sK2) | spl5_59),
% 2.08/0.63    inference(avatar_component_clause,[],[f1038])).
% 2.08/0.63  fof(f593,plain,(
% 2.08/0.63    ( ! [X2] : (r1_xboole_0(sK1,X2) | r2_hidden(sK0,X2)) ) | ~spl5_3),
% 2.08/0.63    inference(superposition,[],[f88,f107])).
% 2.08/0.63  fof(f1309,plain,(
% 2.08/0.63    spl5_23 | ~spl5_26 | ~spl5_61),
% 2.08/0.63    inference(avatar_split_clause,[],[f1308,f1049,f641,f595])).
% 2.08/0.63  fof(f595,plain,(
% 2.08/0.63    spl5_23 <=> sK1 = sK2),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.08/0.63  fof(f641,plain,(
% 2.08/0.63    spl5_26 <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.08/0.63  fof(f1308,plain,(
% 2.08/0.63    sK1 = sK2 | (~spl5_26 | ~spl5_61)),
% 2.08/0.63    inference(forward_demodulation,[],[f1298,f643])).
% 2.08/0.63  fof(f643,plain,(
% 2.08/0.63    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_26),
% 2.08/0.63    inference(avatar_component_clause,[],[f641])).
% 2.08/0.63  fof(f1298,plain,(
% 2.08/0.63    sK2 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_61),
% 2.08/0.63    inference(resolution,[],[f1051,f90])).
% 2.08/0.63  fof(f1051,plain,(
% 2.08/0.63    r1_tarski(sK1,sK2) | ~spl5_61),
% 2.08/0.63    inference(avatar_component_clause,[],[f1049])).
% 2.08/0.63  fof(f1146,plain,(
% 2.08/0.63    spl5_5 | ~spl5_68),
% 2.08/0.63    inference(avatar_split_clause,[],[f1145,f1122,f116])).
% 2.08/0.63  fof(f116,plain,(
% 2.08/0.63    spl5_5 <=> k1_xboole_0 = sK2),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.08/0.63  fof(f1122,plain,(
% 2.08/0.63    spl5_68 <=> v1_xboole_0(sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 2.08/0.63  fof(f1145,plain,(
% 2.08/0.63    k1_xboole_0 = sK2 | ~spl5_68),
% 2.08/0.63    inference(resolution,[],[f1124,f50])).
% 2.08/0.63  fof(f1124,plain,(
% 2.08/0.63    v1_xboole_0(sK2) | ~spl5_68),
% 2.08/0.63    inference(avatar_component_clause,[],[f1122])).
% 2.08/0.63  fof(f1125,plain,(
% 2.08/0.63    spl5_68 | ~spl5_56),
% 2.08/0.63    inference(avatar_split_clause,[],[f1119,f1023,f1122])).
% 2.08/0.63  fof(f1023,plain,(
% 2.08/0.63    spl5_56 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 2.08/0.63  fof(f1119,plain,(
% 2.08/0.63    v1_xboole_0(sK2) | ~spl5_56),
% 2.08/0.63    inference(resolution,[],[f1024,f51])).
% 2.08/0.63  fof(f1024,plain,(
% 2.08/0.63    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_56),
% 2.08/0.63    inference(avatar_component_clause,[],[f1023])).
% 2.08/0.63  fof(f1041,plain,(
% 2.08/0.63    ~spl5_59 | spl5_56 | ~spl5_51),
% 2.08/0.63    inference(avatar_split_clause,[],[f998,f973,f1023,f1038])).
% 2.08/0.63  fof(f973,plain,(
% 2.08/0.63    spl5_51 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.08/0.63  fof(f998,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r1_xboole_0(sK1,sK2)) ) | ~spl5_51),
% 2.08/0.63    inference(superposition,[],[f130,f975])).
% 2.08/0.63  fof(f975,plain,(
% 2.08/0.63    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_51),
% 2.08/0.63    inference(avatar_component_clause,[],[f973])).
% 2.08/0.63  fof(f976,plain,(
% 2.08/0.63    spl5_51 | ~spl5_49),
% 2.08/0.63    inference(avatar_split_clause,[],[f965,f953,f973])).
% 2.08/0.63  fof(f953,plain,(
% 2.08/0.63    spl5_49 <=> r1_tarski(sK2,sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 2.08/0.63  fof(f965,plain,(
% 2.08/0.63    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_49),
% 2.08/0.63    inference(resolution,[],[f955,f63])).
% 2.08/0.63  fof(f955,plain,(
% 2.08/0.63    r1_tarski(sK2,sK1) | ~spl5_49),
% 2.08/0.63    inference(avatar_component_clause,[],[f953])).
% 2.08/0.63  fof(f956,plain,(
% 2.08/0.63    spl5_49 | ~spl5_26),
% 2.08/0.63    inference(avatar_split_clause,[],[f951,f641,f953])).
% 2.08/0.63  fof(f951,plain,(
% 2.08/0.63    r1_tarski(sK2,sK1) | ~spl5_26),
% 2.08/0.63    inference(forward_demodulation,[],[f947,f48])).
% 2.08/0.63  fof(f48,plain,(
% 2.08/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.63    inference(cnf_transformation,[],[f14])).
% 2.08/0.63  fof(f14,axiom,(
% 2.08/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.08/0.63  fof(f947,plain,(
% 2.08/0.63    r1_tarski(k5_xboole_0(sK2,k1_xboole_0),sK1) | ~spl5_26),
% 2.08/0.63    inference(superposition,[],[f655,f47])).
% 2.08/0.63  fof(f47,plain,(
% 2.08/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f11])).
% 2.08/0.63  fof(f11,axiom,(
% 2.08/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.08/0.63  fof(f655,plain,(
% 2.08/0.63    ( ! [X0] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1)) ) | ~spl5_26),
% 2.08/0.63    inference(superposition,[],[f225,f643])).
% 2.08/0.63  fof(f225,plain,(
% 2.08/0.63    ( ! [X4,X2,X3] : (r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))) )),
% 2.08/0.63    inference(resolution,[],[f95,f87])).
% 2.08/0.63  fof(f87,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f53,f57])).
% 2.08/0.63  fof(f57,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f6])).
% 2.08/0.63  fof(f6,axiom,(
% 2.08/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.08/0.63  fof(f53,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f13])).
% 2.08/0.63  fof(f13,axiom,(
% 2.08/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.08/0.63  fof(f95,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) )),
% 2.08/0.63    inference(definition_unfolding,[],[f69,f80])).
% 2.08/0.63  fof(f69,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f39])).
% 2.08/0.63  fof(f39,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f7])).
% 2.08/0.63  fof(f7,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.08/0.63  fof(f598,plain,(
% 2.08/0.63    ~spl5_23 | spl5_2 | ~spl5_3),
% 2.08/0.63    inference(avatar_split_clause,[],[f588,f106,f102,f595])).
% 2.08/0.63  fof(f588,plain,(
% 2.08/0.63    sK1 != sK2 | (spl5_2 | ~spl5_3)),
% 2.08/0.63    inference(backward_demodulation,[],[f104,f107])).
% 2.08/0.63  fof(f104,plain,(
% 2.08/0.63    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_2),
% 2.08/0.63    inference(avatar_component_clause,[],[f102])).
% 2.08/0.63  fof(f119,plain,(
% 2.08/0.63    ~spl5_5 | ~spl5_3),
% 2.08/0.63    inference(avatar_split_clause,[],[f85,f106,f116])).
% 2.08/0.63  fof(f85,plain,(
% 2.08/0.63    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 2.08/0.63    inference(definition_unfolding,[],[f42,f81])).
% 2.08/0.63  fof(f42,plain,(
% 2.08/0.63    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.08/0.63    inference(cnf_transformation,[],[f31])).
% 2.08/0.63  fof(f31,plain,(
% 2.08/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.08/0.63    inference(ennf_transformation,[],[f28])).
% 2.08/0.63  fof(f28,negated_conjecture,(
% 2.08/0.63    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.08/0.63    inference(negated_conjecture,[],[f27])).
% 2.08/0.63  fof(f27,conjecture,(
% 2.08/0.63    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.08/0.63  fof(f114,plain,(
% 2.08/0.63    ~spl5_2 | ~spl5_4),
% 2.08/0.63    inference(avatar_split_clause,[],[f84,f111,f102])).
% 2.08/0.63  fof(f84,plain,(
% 2.08/0.63    k1_xboole_0 != sK1 | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.08/0.63    inference(definition_unfolding,[],[f43,f81])).
% 2.08/0.63  fof(f43,plain,(
% 2.08/0.63    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.08/0.63    inference(cnf_transformation,[],[f31])).
% 2.08/0.63  fof(f109,plain,(
% 2.08/0.63    ~spl5_2 | ~spl5_3),
% 2.08/0.63    inference(avatar_split_clause,[],[f83,f106,f102])).
% 2.08/0.63  fof(f83,plain,(
% 2.08/0.63    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.08/0.63    inference(definition_unfolding,[],[f44,f81,f81])).
% 2.08/0.63  fof(f44,plain,(
% 2.08/0.63    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.08/0.63    inference(cnf_transformation,[],[f31])).
% 2.08/0.63  fof(f100,plain,(
% 2.08/0.63    spl5_1),
% 2.08/0.63    inference(avatar_split_clause,[],[f82,f97])).
% 2.08/0.63  fof(f82,plain,(
% 2.08/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.08/0.63    inference(definition_unfolding,[],[f45,f81,f80])).
% 2.08/0.63  fof(f45,plain,(
% 2.08/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f31])).
% 2.08/0.63  % SZS output end Proof for theBenchmark
% 2.08/0.63  % (7837)------------------------------
% 2.08/0.63  % (7837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (7837)Termination reason: Refutation
% 2.08/0.63  
% 2.08/0.63  % (7837)Memory used [KB]: 12537
% 2.08/0.63  % (7837)Time elapsed: 0.198 s
% 2.08/0.63  % (7837)------------------------------
% 2.08/0.63  % (7837)------------------------------
% 2.08/0.63  % (7820)Success in time 0.278 s
%------------------------------------------------------------------------------
