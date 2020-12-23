%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:45 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 198 expanded)
%              Number of leaves         :   33 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 ( 357 expanded)
%              Number of equality atoms :  111 ( 190 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f82,f1460,f1537,f1646,f1647,f1660,f1663,f1667,f1670,f2051,f2102,f2260])).

fof(f2260,plain,
    ( spl4_3
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f2252,f2048,f75])).

fof(f75,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2048,plain,
    ( spl4_33
  <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f2252,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_33 ),
    inference(trivial_inequality_removal,[],[f2251])).

fof(f2251,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl4_33 ),
    inference(superposition,[],[f57,f2050])).

fof(f2050,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f2048])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2102,plain,
    ( sK0 != k3_xboole_0(sK0,sK2)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 != k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2051,plain,
    ( spl4_32
    | spl4_33
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f2041,f1624,f2048,f2044])).

fof(f2044,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1624,plain,
    ( spl4_24
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f2041,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ spl4_24 ),
    inference(trivial_inequality_removal,[],[f2010])).

fof(f2010,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ spl4_24 ),
    inference(superposition,[],[f36,f1626])).

fof(f1626,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f1624])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1670,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f1669])).

fof(f1669,plain,
    ( $false
    | spl4_20 ),
    inference(trivial_inequality_removal,[],[f1668])).

fof(f1668,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_20 ),
    inference(superposition,[],[f1527,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1527,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f1525])).

fof(f1525,plain,
    ( spl4_20
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1667,plain,
    ( spl4_22
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1665,f79,f1556])).

fof(f1556,plain,
    ( spl4_22
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f79,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1665,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f80,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f80,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f1663,plain,
    ( spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f1544,f1453,f79])).

fof(f1453,plain,
    ( spl4_11
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1544,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f1543])).

fof(f1543,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f57,f1455])).

fof(f1455,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f1453])).

fof(f1660,plain,
    ( spl4_24
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f1622,f1556,f85,f1624])).

fof(f85,plain,
    ( spl4_5
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1622,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f1621,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1621,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f1593,f1558])).

fof(f1558,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f1556])).

fof(f1593,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f203,f87])).

fof(f87,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f203,plain,(
    ! [X6,X4,X7,X5] : k2_zfmisc_1(k3_xboole_0(X4,X5),k5_xboole_0(X6,k3_xboole_0(X6,X7))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X4,X5),X6),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))) ),
    inference(superposition,[],[f162,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f162,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f59,f115])).

fof(f115,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f45,f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f43,f34,f34])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f1647,plain,
    ( ~ spl4_20
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f1510,f1457,f65,f1525])).

fof(f65,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1457,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1510,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f67,f1459])).

fof(f1459,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f1457])).

fof(f67,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f1646,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f1610,f85,f1386])).

fof(f1386,plain,
    ( spl4_10
  <=> k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1610,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1609,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1609,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1591,f29])).

fof(f1591,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(superposition,[],[f398,f87])).

fof(f398,plain,(
    ! [X6,X4,X7,X5] : k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)))) ),
    inference(superposition,[],[f56,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))))) ),
    inference(definition_unfolding,[],[f46,f34,f55,f34,f34])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f31,f55])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f1537,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f1535,f70,f85])).

fof(f70,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1535,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f72,f35])).

fof(f72,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f1460,plain,
    ( spl4_11
    | spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f1450,f1386,f1457,f1453])).

fof(f1450,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f1422])).

fof(f1422,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl4_10 ),
    inference(superposition,[],[f36,f1388])).

fof(f1388,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f82,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f25,f79,f75])).

fof(f25,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (28673)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (28690)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (28674)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (28682)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (28681)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (28670)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (28672)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (28669)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (28676)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (28666)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (28693)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (28683)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (28688)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (28667)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (28688)Refutation not found, incomplete strategy% (28688)------------------------------
% 0.22/0.55  % (28688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28688)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28688)Memory used [KB]: 10746
% 0.22/0.55  % (28688)Time elapsed: 0.129 s
% 0.22/0.55  % (28688)------------------------------
% 0.22/0.55  % (28688)------------------------------
% 0.22/0.55  % (28675)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (28686)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (28683)Refutation not found, incomplete strategy% (28683)------------------------------
% 0.22/0.56  % (28683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28683)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (28683)Memory used [KB]: 10618
% 0.22/0.56  % (28683)Time elapsed: 0.091 s
% 0.22/0.56  % (28683)------------------------------
% 0.22/0.56  % (28683)------------------------------
% 0.22/0.56  % (28680)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (28685)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (28691)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (28678)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (28677)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (28694)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (28689)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (28695)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (28668)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (28671)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (28687)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (28692)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.59  % (28679)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.77/0.60  % (28684)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.04/0.63  % (28682)Refutation found. Thanks to Tanya!
% 2.04/0.63  % SZS status Theorem for theBenchmark
% 2.04/0.64  % SZS output start Proof for theBenchmark
% 2.04/0.64  fof(f2261,plain,(
% 2.04/0.64    $false),
% 2.04/0.64    inference(avatar_sat_refutation,[],[f68,f73,f82,f1460,f1537,f1646,f1647,f1660,f1663,f1667,f1670,f2051,f2102,f2260])).
% 2.04/0.64  fof(f2260,plain,(
% 2.04/0.64    spl4_3 | ~spl4_33),
% 2.04/0.64    inference(avatar_split_clause,[],[f2252,f2048,f75])).
% 2.04/0.64  fof(f75,plain,(
% 2.04/0.64    spl4_3 <=> r1_tarski(sK1,sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.04/0.64  fof(f2048,plain,(
% 2.04/0.64    spl4_33 <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.04/0.64  fof(f2252,plain,(
% 2.04/0.64    r1_tarski(sK1,sK3) | ~spl4_33),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f2251])).
% 2.04/0.64  fof(f2251,plain,(
% 2.04/0.64    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | ~spl4_33),
% 2.04/0.64    inference(superposition,[],[f57,f2050])).
% 2.04/0.64  fof(f2050,plain,(
% 2.04/0.64    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl4_33),
% 2.04/0.64    inference(avatar_component_clause,[],[f2048])).
% 2.04/0.64  fof(f57,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f40,f34])).
% 2.04/0.64  fof(f34,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f3])).
% 2.04/0.64  fof(f3,axiom,(
% 2.04/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.04/0.64  fof(f40,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f2])).
% 2.04/0.64  fof(f2,axiom,(
% 2.04/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.04/0.64  fof(f2102,plain,(
% 2.04/0.64    sK0 != k3_xboole_0(sK0,sK2) | k1_xboole_0 != sK0 | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 != k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.04/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.64  fof(f2051,plain,(
% 2.04/0.64    spl4_32 | spl4_33 | ~spl4_24),
% 2.04/0.64    inference(avatar_split_clause,[],[f2041,f1624,f2048,f2044])).
% 2.04/0.64  fof(f2044,plain,(
% 2.04/0.64    spl4_32 <=> k1_xboole_0 = sK0),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.04/0.64  fof(f1624,plain,(
% 2.04/0.64    spl4_24 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.04/0.64  fof(f2041,plain,(
% 2.04/0.64    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK0 | ~spl4_24),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f2010])).
% 2.04/0.64  fof(f2010,plain,(
% 2.04/0.64    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK0 | ~spl4_24),
% 2.04/0.64    inference(superposition,[],[f36,f1626])).
% 2.04/0.64  fof(f1626,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~spl4_24),
% 2.04/0.64    inference(avatar_component_clause,[],[f1624])).
% 2.04/0.64  fof(f36,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f15])).
% 2.04/0.64  fof(f15,axiom,(
% 2.04/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.04/0.64  fof(f1670,plain,(
% 2.04/0.64    spl4_20),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f1669])).
% 2.04/0.64  fof(f1669,plain,(
% 2.04/0.64    $false | spl4_20),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f1668])).
% 2.04/0.64  fof(f1668,plain,(
% 2.04/0.64    k1_xboole_0 != k1_xboole_0 | spl4_20),
% 2.04/0.64    inference(superposition,[],[f1527,f62])).
% 2.04/0.64  fof(f62,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.04/0.64    inference(equality_resolution,[],[f38])).
% 2.04/0.64  fof(f38,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f15])).
% 2.04/0.64  fof(f1527,plain,(
% 2.04/0.64    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl4_20),
% 2.04/0.64    inference(avatar_component_clause,[],[f1525])).
% 2.04/0.64  fof(f1525,plain,(
% 2.04/0.64    spl4_20 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.04/0.64  fof(f1667,plain,(
% 2.04/0.64    spl4_22 | ~spl4_4),
% 2.04/0.64    inference(avatar_split_clause,[],[f1665,f79,f1556])).
% 2.04/0.64  fof(f1556,plain,(
% 2.04/0.64    spl4_22 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.04/0.64  fof(f79,plain,(
% 2.04/0.64    spl4_4 <=> r1_tarski(sK0,sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.04/0.64  fof(f1665,plain,(
% 2.04/0.64    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_4),
% 2.04/0.64    inference(resolution,[],[f80,f35])).
% 2.04/0.64  fof(f35,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f24])).
% 2.04/0.64  fof(f24,plain,(
% 2.04/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.04/0.64    inference(ennf_transformation,[],[f5])).
% 2.04/0.64  fof(f5,axiom,(
% 2.04/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.04/0.64  fof(f80,plain,(
% 2.04/0.64    r1_tarski(sK0,sK2) | ~spl4_4),
% 2.04/0.64    inference(avatar_component_clause,[],[f79])).
% 2.04/0.64  fof(f1663,plain,(
% 2.04/0.64    spl4_4 | ~spl4_11),
% 2.04/0.64    inference(avatar_split_clause,[],[f1544,f1453,f79])).
% 2.04/0.64  fof(f1453,plain,(
% 2.04/0.64    spl4_11 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.04/0.64  fof(f1544,plain,(
% 2.04/0.64    r1_tarski(sK0,sK2) | ~spl4_11),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f1543])).
% 2.04/0.64  fof(f1543,plain,(
% 2.04/0.64    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | ~spl4_11),
% 2.04/0.64    inference(superposition,[],[f57,f1455])).
% 2.04/0.64  fof(f1455,plain,(
% 2.04/0.64    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl4_11),
% 2.04/0.64    inference(avatar_component_clause,[],[f1453])).
% 2.04/0.64  fof(f1660,plain,(
% 2.04/0.64    spl4_24 | ~spl4_5 | ~spl4_22),
% 2.04/0.64    inference(avatar_split_clause,[],[f1622,f1556,f85,f1624])).
% 2.04/0.64  fof(f85,plain,(
% 2.04/0.64    spl4_5 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.04/0.64  fof(f1622,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | (~spl4_5 | ~spl4_22)),
% 2.04/0.64    inference(forward_demodulation,[],[f1621,f29])).
% 2.04/0.64  fof(f29,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f7])).
% 2.04/0.64  fof(f7,axiom,(
% 2.04/0.64    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.04/0.64  fof(f1621,plain,(
% 2.04/0.64    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | (~spl4_5 | ~spl4_22)),
% 2.04/0.64    inference(forward_demodulation,[],[f1593,f1558])).
% 2.04/0.64  fof(f1558,plain,(
% 2.04/0.64    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_22),
% 2.04/0.64    inference(avatar_component_clause,[],[f1556])).
% 2.04/0.64  fof(f1593,plain,(
% 2.04/0.64    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 2.04/0.64    inference(superposition,[],[f203,f87])).
% 2.04/0.64  fof(f87,plain,(
% 2.04/0.64    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_5),
% 2.04/0.64    inference(avatar_component_clause,[],[f85])).
% 2.04/0.64  fof(f203,plain,(
% 2.04/0.64    ( ! [X6,X4,X7,X5] : (k2_zfmisc_1(k3_xboole_0(X4,X5),k5_xboole_0(X6,k3_xboole_0(X6,X7))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X4,X5),X6),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)))) )),
% 2.04/0.64    inference(superposition,[],[f162,f45])).
% 2.04/0.64  fof(f45,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f16])).
% 2.04/0.64  fof(f16,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.04/0.64  fof(f162,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))) )),
% 2.04/0.64    inference(forward_demodulation,[],[f59,f115])).
% 2.04/0.64  fof(f115,plain,(
% 2.04/0.64    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5))) )),
% 2.04/0.64    inference(superposition,[],[f45,f30])).
% 2.04/0.64  fof(f30,plain,(
% 2.04/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f21])).
% 2.04/0.64  fof(f21,plain,(
% 2.04/0.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.04/0.64    inference(rectify,[],[f1])).
% 2.04/0.64  fof(f1,axiom,(
% 2.04/0.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.04/0.64  fof(f59,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 2.04/0.64    inference(definition_unfolding,[],[f43,f34,f34])).
% 2.04/0.64  fof(f43,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f17])).
% 2.04/0.64  fof(f17,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 2.04/0.64  fof(f1647,plain,(
% 2.04/0.64    ~spl4_20 | spl4_1 | ~spl4_12),
% 2.04/0.64    inference(avatar_split_clause,[],[f1510,f1457,f65,f1525])).
% 2.04/0.64  fof(f65,plain,(
% 2.04/0.64    spl4_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.04/0.64  fof(f1457,plain,(
% 2.04/0.64    spl4_12 <=> k1_xboole_0 = sK1),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.04/0.64  fof(f1510,plain,(
% 2.04/0.64    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl4_1 | ~spl4_12)),
% 2.04/0.64    inference(backward_demodulation,[],[f67,f1459])).
% 2.04/0.64  fof(f1459,plain,(
% 2.04/0.64    k1_xboole_0 = sK1 | ~spl4_12),
% 2.04/0.64    inference(avatar_component_clause,[],[f1457])).
% 2.04/0.64  fof(f67,plain,(
% 2.04/0.64    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl4_1),
% 2.04/0.64    inference(avatar_component_clause,[],[f65])).
% 2.04/0.64  fof(f1646,plain,(
% 2.04/0.64    spl4_10 | ~spl4_5),
% 2.04/0.64    inference(avatar_split_clause,[],[f1610,f85,f1386])).
% 2.04/0.64  fof(f1386,plain,(
% 2.04/0.64    spl4_10 <=> k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.04/0.64  fof(f1610,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl4_5),
% 2.04/0.64    inference(forward_demodulation,[],[f1609,f28])).
% 2.04/0.64  fof(f28,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f6])).
% 2.04/0.64  fof(f6,axiom,(
% 2.04/0.64    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.04/0.64  fof(f1609,plain,(
% 2.04/0.64    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k1_xboole_0) | ~spl4_5),
% 2.04/0.64    inference(forward_demodulation,[],[f1591,f29])).
% 2.04/0.64  fof(f1591,plain,(
% 2.04/0.64    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 2.04/0.64    inference(superposition,[],[f398,f87])).
% 2.04/0.64  fof(f398,plain,(
% 2.04/0.64    ( ! [X6,X4,X7,X5] : (k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))))) )),
% 2.04/0.64    inference(superposition,[],[f56,f61])).
% 2.04/0.64  fof(f61,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))))) )),
% 2.04/0.64    inference(definition_unfolding,[],[f46,f34,f55,f34,f34])).
% 2.04/0.64  fof(f55,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.04/0.64    inference(definition_unfolding,[],[f32,f54])).
% 2.04/0.64  fof(f54,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f33,f53])).
% 2.04/0.64  fof(f53,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f41,f52])).
% 2.04/0.64  fof(f52,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f44,f51])).
% 2.04/0.64  fof(f51,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f47,f50])).
% 2.04/0.64  fof(f50,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f48,f49])).
% 2.04/0.64  fof(f49,plain,(
% 2.04/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f13])).
% 2.04/0.64  fof(f13,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.04/0.64  fof(f48,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f12])).
% 2.04/0.64  fof(f12,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.04/0.64  fof(f47,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f11])).
% 2.04/0.64  fof(f11,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.04/0.64  fof(f44,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f10])).
% 2.04/0.64  fof(f10,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.04/0.64  fof(f41,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f9])).
% 2.04/0.64  fof(f9,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.04/0.64  fof(f33,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f8])).
% 2.04/0.64  fof(f8,axiom,(
% 2.04/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.04/0.64  fof(f32,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f14])).
% 2.04/0.64  fof(f14,axiom,(
% 2.04/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.04/0.64  fof(f46,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f18])).
% 2.04/0.64  fof(f18,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_zfmisc_1)).
% 2.04/0.64  fof(f56,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 2.04/0.64    inference(definition_unfolding,[],[f31,f55])).
% 2.04/0.64  fof(f31,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f4])).
% 2.04/0.64  fof(f4,axiom,(
% 2.04/0.64    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.04/0.64  fof(f1537,plain,(
% 2.04/0.64    spl4_5 | ~spl4_2),
% 2.04/0.64    inference(avatar_split_clause,[],[f1535,f70,f85])).
% 2.04/0.64  fof(f70,plain,(
% 2.04/0.64    spl4_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.04/0.64  fof(f1535,plain,(
% 2.04/0.64    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 2.04/0.64    inference(resolution,[],[f72,f35])).
% 2.04/0.64  fof(f72,plain,(
% 2.04/0.64    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 2.04/0.64    inference(avatar_component_clause,[],[f70])).
% 2.04/0.64  fof(f1460,plain,(
% 2.04/0.64    spl4_11 | spl4_12 | ~spl4_10),
% 2.04/0.64    inference(avatar_split_clause,[],[f1450,f1386,f1457,f1453])).
% 2.04/0.64  fof(f1450,plain,(
% 2.04/0.64    k1_xboole_0 = sK1 | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl4_10),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f1422])).
% 2.04/0.64  fof(f1422,plain,(
% 2.04/0.64    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl4_10),
% 2.04/0.64    inference(superposition,[],[f36,f1388])).
% 2.04/0.64  fof(f1388,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl4_10),
% 2.04/0.64    inference(avatar_component_clause,[],[f1386])).
% 2.04/0.64  fof(f82,plain,(
% 2.04/0.64    ~spl4_3 | ~spl4_4),
% 2.04/0.64    inference(avatar_split_clause,[],[f25,f79,f75])).
% 2.04/0.64  fof(f25,plain,(
% 2.04/0.64    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 2.04/0.64    inference(cnf_transformation,[],[f23])).
% 2.04/0.64  fof(f23,plain,(
% 2.04/0.64    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.04/0.64    inference(flattening,[],[f22])).
% 2.04/0.64  fof(f22,plain,(
% 2.04/0.64    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.04/0.64    inference(ennf_transformation,[],[f20])).
% 2.04/0.64  fof(f20,negated_conjecture,(
% 2.04/0.64    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.04/0.64    inference(negated_conjecture,[],[f19])).
% 2.04/0.64  fof(f19,conjecture,(
% 2.04/0.64    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.04/0.64  fof(f73,plain,(
% 2.04/0.64    spl4_2),
% 2.04/0.64    inference(avatar_split_clause,[],[f26,f70])).
% 2.04/0.64  fof(f26,plain,(
% 2.04/0.64    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.04/0.64    inference(cnf_transformation,[],[f23])).
% 2.04/0.64  fof(f68,plain,(
% 2.04/0.64    ~spl4_1),
% 2.04/0.64    inference(avatar_split_clause,[],[f27,f65])).
% 2.04/0.64  fof(f27,plain,(
% 2.04/0.64    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.04/0.64    inference(cnf_transformation,[],[f23])).
% 2.04/0.64  % SZS output end Proof for theBenchmark
% 2.04/0.64  % (28682)------------------------------
% 2.04/0.64  % (28682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.64  % (28682)Termination reason: Refutation
% 2.04/0.64  
% 2.04/0.64  % (28682)Memory used [KB]: 12537
% 2.04/0.64  % (28682)Time elapsed: 0.194 s
% 2.04/0.64  % (28682)------------------------------
% 2.04/0.64  % (28682)------------------------------
% 2.04/0.65  % (28665)Success in time 0.274 s
%------------------------------------------------------------------------------
