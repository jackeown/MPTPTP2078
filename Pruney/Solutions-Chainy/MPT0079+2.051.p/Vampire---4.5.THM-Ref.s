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
% DateTime   : Thu Dec  3 12:30:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 198 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 ( 432 expanded)
%              Number of equality atoms :   92 ( 191 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1414,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f84,f99,f110,f120,f175,f416,f547,f1249,f1265,f1276,f1337,f1409])).

fof(f1409,plain,
    ( spl4_1
    | ~ spl4_61 ),
    inference(avatar_contradiction_clause,[],[f1408])).

fof(f1408,plain,
    ( $false
    | spl4_1
    | ~ spl4_61 ),
    inference(subsumption_resolution,[],[f1381,f52])).

fof(f52,plain,
    ( sK1 != sK2
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1381,plain,
    ( sK1 = sK2
    | ~ spl4_61 ),
    inference(superposition,[],[f30,f1336])).

fof(f1336,plain,
    ( sK1 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1334,plain,
    ( spl4_61
  <=> sK1 = k2_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1337,plain,
    ( spl4_61
    | ~ spl4_4
    | ~ spl4_33
    | ~ spl4_41
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f1332,f1272,f544,f413,f65,f1334])).

fof(f65,plain,
    ( spl4_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f413,plain,
    ( spl4_33
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f544,plain,
    ( spl4_41
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1272,plain,
    ( spl4_57
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1332,plain,
    ( sK1 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_33
    | ~ spl4_41
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f1331,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1331,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_33
    | ~ spl4_41
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f1330,f546])).

fof(f546,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f544])).

fof(f1330,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl4_4
    | ~ spl4_33
    | ~ spl4_41
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f1329,f415])).

fof(f415,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1329,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
    | ~ spl4_4
    | ~ spl4_41
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f1317,f566])).

fof(f566,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X2,sK1))
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f562,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f562,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK1,X2),k4_xboole_0(k4_xboole_0(sK1,X2),k1_xboole_0)) = k4_xboole_0(sK1,k2_xboole_0(X2,sK1))
    | ~ spl4_41 ),
    inference(superposition,[],[f48,f546])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f42,f33])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f1317,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_57 ),
    inference(superposition,[],[f112,f1274])).

fof(f1274,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f112,plain,
    ( ! [X0] : k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f47,f67])).

fof(f67,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f41,f33,f33])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f1276,plain,
    ( spl4_57
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f1270,f1262,f1272])).

fof(f1262,plain,
    ( spl4_56
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f1270,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl4_56 ),
    inference(resolution,[],[f1264,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1264,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f1262])).

fof(f1265,plain,
    ( spl4_56
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f1253,f1245,f1262])).

fof(f1245,plain,
    ( spl4_55
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f1253,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_55 ),
    inference(unit_resulting_resolution,[],[f1247,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f1247,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f1249,plain,
    ( spl4_55
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f1233,f172,f117,f1245])).

fof(f117,plain,
    ( spl4_10
  <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f172,plain,
    ( spl4_15
  <=> sK2 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1233,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(superposition,[],[f119,f318])).

fof(f318,plain,
    ( ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)
    | ~ spl4_15 ),
    inference(superposition,[],[f40,f174])).

fof(f174,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f172])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f119,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f547,plain,
    ( spl4_41
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f530,f413,f106,f544])).

fof(f106,plain,
    ( spl4_9
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f530,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(backward_demodulation,[],[f108,f415])).

fof(f108,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f416,plain,
    ( spl4_33
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f411,f106,f413])).

fof(f411,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f398,f31])).

fof(f398,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_9 ),
    inference(superposition,[],[f44,f108])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f175,plain,
    ( spl4_15
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f170,f95,f172])).

fof(f95,plain,
    ( spl4_8
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f170,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f157,f31])).

fof(f157,plain,
    ( k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_8 ),
    inference(superposition,[],[f44,f97])).

fof(f97,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f120,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f115,f65,f117])).

fof(f115,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f32,f67])).

fof(f32,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f110,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f103,f74,f106])).

fof(f74,plain,
    ( spl4_5
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f103,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f76,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f99,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f87,f60,f95])).

fof(f60,plain,
    ( spl4_3
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f87,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f84,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f72,f55,f74])).

fof(f55,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f72,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f57,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f68,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (12736)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (12744)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (12744)Refutation not found, incomplete strategy% (12744)------------------------------
% 0.21/0.51  % (12744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12741)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (12731)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12749)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (12752)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (12744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12744)Memory used [KB]: 10618
% 0.21/0.51  % (12744)Time elapsed: 0.095 s
% 0.21/0.51  % (12744)------------------------------
% 0.21/0.51  % (12744)------------------------------
% 0.21/0.51  % (12733)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (12734)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (12729)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12728)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (12745)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (12730)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (12732)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (12727)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (12737)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (12743)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (12754)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (12755)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (12756)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (12735)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (12746)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (12742)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (12742)Refutation not found, incomplete strategy% (12742)------------------------------
% 0.21/0.55  % (12742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12742)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12742)Memory used [KB]: 6140
% 0.21/0.55  % (12742)Time elapsed: 0.001 s
% 0.21/0.55  % (12742)------------------------------
% 0.21/0.55  % (12742)------------------------------
% 0.21/0.55  % (12747)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (12748)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (12750)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (12751)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (12753)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (12738)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (12739)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (12740)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (12752)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1414,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f84,f99,f110,f120,f175,f416,f547,f1249,f1265,f1276,f1337,f1409])).
% 0.21/0.57  fof(f1409,plain,(
% 0.21/0.57    spl4_1 | ~spl4_61),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1408])).
% 0.21/0.57  fof(f1408,plain,(
% 0.21/0.57    $false | (spl4_1 | ~spl4_61)),
% 0.21/0.57    inference(subsumption_resolution,[],[f1381,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    sK1 != sK2 | spl4_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    spl4_1 <=> sK1 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.57  fof(f1381,plain,(
% 0.21/0.57    sK1 = sK2 | ~spl4_61),
% 0.21/0.57    inference(superposition,[],[f30,f1336])).
% 0.21/0.57  fof(f1336,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(sK2,k1_xboole_0) | ~spl4_61),
% 0.21/0.57    inference(avatar_component_clause,[],[f1334])).
% 0.21/0.57  fof(f1334,plain,(
% 0.21/0.57    spl4_61 <=> sK1 = k2_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.57  fof(f1337,plain,(
% 0.21/0.57    spl4_61 | ~spl4_4 | ~spl4_33 | ~spl4_41 | ~spl4_57),
% 0.21/0.57    inference(avatar_split_clause,[],[f1332,f1272,f544,f413,f65,f1334])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    spl4_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.57  fof(f413,plain,(
% 0.21/0.57    spl4_33 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.57  fof(f544,plain,(
% 0.21/0.57    spl4_41 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.57  fof(f1272,plain,(
% 0.21/0.57    spl4_57 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.21/0.57  fof(f1332,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(sK2,k1_xboole_0) | (~spl4_4 | ~spl4_33 | ~spl4_41 | ~spl4_57)),
% 0.21/0.57    inference(forward_demodulation,[],[f1331,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.57  fof(f1331,plain,(
% 0.21/0.57    k2_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) | (~spl4_4 | ~spl4_33 | ~spl4_41 | ~spl4_57)),
% 0.21/0.57    inference(forward_demodulation,[],[f1330,f546])).
% 0.21/0.57  fof(f546,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl4_41),
% 0.21/0.57    inference(avatar_component_clause,[],[f544])).
% 0.21/0.57  fof(f1330,plain,(
% 0.21/0.57    k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | (~spl4_4 | ~spl4_33 | ~spl4_41 | ~spl4_57)),
% 0.21/0.57    inference(forward_demodulation,[],[f1329,f415])).
% 0.21/0.57  fof(f415,plain,(
% 0.21/0.57    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_33),
% 0.21/0.57    inference(avatar_component_clause,[],[f413])).
% 0.21/0.57  fof(f1329,plain,(
% 0.21/0.57    k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) | (~spl4_4 | ~spl4_41 | ~spl4_57)),
% 0.21/0.57    inference(forward_demodulation,[],[f1317,f566])).
% 0.21/0.57  fof(f566,plain,(
% 0.21/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X2,sK1))) ) | ~spl4_41),
% 0.21/0.57    inference(forward_demodulation,[],[f562,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f29,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.57  fof(f562,plain,(
% 0.21/0.57    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,X2),k4_xboole_0(k4_xboole_0(sK1,X2),k1_xboole_0)) = k4_xboole_0(sK1,k2_xboole_0(X2,sK1))) ) | ~spl4_41),
% 0.21/0.57    inference(superposition,[],[f48,f546])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f42,f33])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.21/0.57  fof(f1317,plain,(
% 0.21/0.57    k2_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))) | (~spl4_4 | ~spl4_57)),
% 0.21/0.57    inference(superposition,[],[f112,f1274])).
% 0.21/0.57  fof(f1274,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(sK2,sK1) | ~spl4_57),
% 0.21/0.57    inference(avatar_component_clause,[],[f1272])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ( ! [X0] : (k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK0,sK1)))) ) | ~spl4_4),
% 0.21/0.57    inference(superposition,[],[f47,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) | ~spl4_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f65])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f41,f33,f33])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 0.21/0.57  fof(f1276,plain,(
% 0.21/0.57    spl4_57 | ~spl4_56),
% 0.21/0.57    inference(avatar_split_clause,[],[f1270,f1262,f1272])).
% 0.21/0.57  fof(f1262,plain,(
% 0.21/0.57    spl4_56 <=> r1_tarski(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.57  fof(f1270,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(sK2,sK1) | ~spl4_56),
% 0.21/0.57    inference(resolution,[],[f1264,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.61/0.57  fof(f1264,plain,(
% 1.61/0.57    r1_tarski(sK2,sK1) | ~spl4_56),
% 1.61/0.57    inference(avatar_component_clause,[],[f1262])).
% 1.61/0.57  fof(f1265,plain,(
% 1.61/0.57    spl4_56 | ~spl4_55),
% 1.61/0.57    inference(avatar_split_clause,[],[f1253,f1245,f1262])).
% 1.61/0.57  fof(f1245,plain,(
% 1.61/0.57    spl4_55 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.61/0.57  fof(f1253,plain,(
% 1.61/0.57    r1_tarski(sK2,sK1) | ~spl4_55),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f1247,f39])).
% 1.61/0.57  fof(f39,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f16])).
% 1.61/0.57  fof(f16,plain,(
% 1.61/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) => r1_tarski(X0,X1))),
% 1.61/0.57    inference(unused_predicate_definition_removal,[],[f7])).
% 1.61/0.57  fof(f7,axiom,(
% 1.61/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.61/0.57  fof(f1247,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl4_55),
% 1.61/0.57    inference(avatar_component_clause,[],[f1245])).
% 1.61/0.57  fof(f1249,plain,(
% 1.61/0.57    spl4_55 | ~spl4_10 | ~spl4_15),
% 1.61/0.57    inference(avatar_split_clause,[],[f1233,f172,f117,f1245])).
% 1.61/0.57  fof(f117,plain,(
% 1.61/0.57    spl4_10 <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.61/0.57  fof(f172,plain,(
% 1.61/0.57    spl4_15 <=> sK2 = k4_xboole_0(sK2,sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.61/0.57  fof(f1233,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl4_10 | ~spl4_15)),
% 1.61/0.57    inference(superposition,[],[f119,f318])).
% 1.61/0.57  fof(f318,plain,(
% 1.61/0.57    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) ) | ~spl4_15),
% 1.61/0.57    inference(superposition,[],[f40,f174])).
% 1.61/0.57  fof(f174,plain,(
% 1.61/0.57    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_15),
% 1.61/0.57    inference(avatar_component_clause,[],[f172])).
% 1.61/0.57  fof(f40,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f9])).
% 1.61/0.57  fof(f9,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.61/0.57  fof(f119,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_10),
% 1.61/0.57    inference(avatar_component_clause,[],[f117])).
% 1.61/0.57  fof(f547,plain,(
% 1.61/0.57    spl4_41 | ~spl4_9 | ~spl4_33),
% 1.61/0.57    inference(avatar_split_clause,[],[f530,f413,f106,f544])).
% 1.61/0.57  fof(f106,plain,(
% 1.61/0.57    spl4_9 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.61/0.57  fof(f530,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK1) | (~spl4_9 | ~spl4_33)),
% 1.61/0.57    inference(backward_demodulation,[],[f108,f415])).
% 1.61/0.57  fof(f108,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl4_9),
% 1.61/0.57    inference(avatar_component_clause,[],[f106])).
% 1.61/0.57  fof(f416,plain,(
% 1.61/0.57    spl4_33 | ~spl4_9),
% 1.61/0.57    inference(avatar_split_clause,[],[f411,f106,f413])).
% 1.61/0.57  fof(f411,plain,(
% 1.61/0.57    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_9),
% 1.61/0.57    inference(forward_demodulation,[],[f398,f31])).
% 1.61/0.57  fof(f398,plain,(
% 1.61/0.57    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) | ~spl4_9),
% 1.61/0.57    inference(superposition,[],[f44,f108])).
% 1.61/0.57  fof(f44,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.61/0.57    inference(definition_unfolding,[],[f34,f33])).
% 1.61/0.57  fof(f34,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f11])).
% 1.61/0.57  fof(f11,axiom,(
% 1.61/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.61/0.57  fof(f175,plain,(
% 1.61/0.57    spl4_15 | ~spl4_8),
% 1.61/0.57    inference(avatar_split_clause,[],[f170,f95,f172])).
% 1.61/0.57  fof(f95,plain,(
% 1.61/0.57    spl4_8 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.61/0.57  fof(f170,plain,(
% 1.61/0.57    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_8),
% 1.61/0.57    inference(forward_demodulation,[],[f157,f31])).
% 1.61/0.57  fof(f157,plain,(
% 1.61/0.57    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) | ~spl4_8),
% 1.61/0.57    inference(superposition,[],[f44,f97])).
% 1.61/0.57  fof(f97,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_8),
% 1.61/0.57    inference(avatar_component_clause,[],[f95])).
% 1.61/0.57  fof(f120,plain,(
% 1.61/0.57    spl4_10 | ~spl4_4),
% 1.61/0.57    inference(avatar_split_clause,[],[f115,f65,f117])).
% 1.61/0.57  fof(f115,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_4),
% 1.61/0.57    inference(superposition,[],[f32,f67])).
% 1.61/0.57  fof(f32,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f10])).
% 1.61/0.57  fof(f10,axiom,(
% 1.61/0.57    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.61/0.57  fof(f110,plain,(
% 1.61/0.57    spl4_9 | ~spl4_5),
% 1.61/0.57    inference(avatar_split_clause,[],[f103,f74,f106])).
% 1.61/0.57  fof(f74,plain,(
% 1.61/0.57    spl4_5 <=> r1_xboole_0(sK1,sK3)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.61/0.57  fof(f103,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl4_5),
% 1.61/0.57    inference(resolution,[],[f76,f46])).
% 1.61/0.57  fof(f46,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.57    inference(definition_unfolding,[],[f37,f33])).
% 1.61/0.57  fof(f37,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f24])).
% 1.61/0.57  fof(f24,plain,(
% 1.61/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.61/0.57    inference(nnf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.61/0.57  fof(f76,plain,(
% 1.61/0.57    r1_xboole_0(sK1,sK3) | ~spl4_5),
% 1.61/0.57    inference(avatar_component_clause,[],[f74])).
% 1.61/0.57  fof(f99,plain,(
% 1.61/0.57    spl4_8 | ~spl4_3),
% 1.61/0.57    inference(avatar_split_clause,[],[f87,f60,f95])).
% 1.61/0.57  fof(f60,plain,(
% 1.61/0.57    spl4_3 <=> r1_xboole_0(sK2,sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.61/0.57  fof(f87,plain,(
% 1.61/0.57    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_3),
% 1.61/0.57    inference(resolution,[],[f62,f46])).
% 1.61/0.57  fof(f62,plain,(
% 1.61/0.57    r1_xboole_0(sK2,sK0) | ~spl4_3),
% 1.61/0.57    inference(avatar_component_clause,[],[f60])).
% 1.61/0.57  fof(f84,plain,(
% 1.61/0.57    spl4_5 | ~spl4_2),
% 1.61/0.57    inference(avatar_split_clause,[],[f72,f55,f74])).
% 1.61/0.57  fof(f55,plain,(
% 1.61/0.57    spl4_2 <=> r1_xboole_0(sK3,sK1)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.61/0.57  fof(f72,plain,(
% 1.61/0.57    r1_xboole_0(sK1,sK3) | ~spl4_2),
% 1.61/0.57    inference(resolution,[],[f57,f36])).
% 1.61/0.57  fof(f36,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f20])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.61/0.57  fof(f57,plain,(
% 1.61/0.57    r1_xboole_0(sK3,sK1) | ~spl4_2),
% 1.61/0.57    inference(avatar_component_clause,[],[f55])).
% 1.61/0.57  fof(f68,plain,(
% 1.61/0.57    spl4_4),
% 1.61/0.57    inference(avatar_split_clause,[],[f25,f65])).
% 1.61/0.57  fof(f25,plain,(
% 1.61/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.61/0.57    inference(cnf_transformation,[],[f23])).
% 1.61/0.57  fof(f23,plain,(
% 1.61/0.57    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).
% 1.61/0.57  fof(f22,plain,(
% 1.61/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.61/0.57    inference(flattening,[],[f17])).
% 1.61/0.57  fof(f17,plain,(
% 1.61/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.61/0.57    inference(ennf_transformation,[],[f15])).
% 1.61/0.57  fof(f15,negated_conjecture,(
% 1.61/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.61/0.57    inference(negated_conjecture,[],[f14])).
% 1.61/0.57  fof(f14,conjecture,(
% 1.61/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.61/0.57  fof(f63,plain,(
% 1.61/0.57    spl4_3),
% 1.61/0.57    inference(avatar_split_clause,[],[f26,f60])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    r1_xboole_0(sK2,sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f23])).
% 1.61/0.57  fof(f58,plain,(
% 1.61/0.57    spl4_2),
% 1.61/0.57    inference(avatar_split_clause,[],[f27,f55])).
% 1.61/0.57  fof(f27,plain,(
% 1.61/0.57    r1_xboole_0(sK3,sK1)),
% 1.61/0.57    inference(cnf_transformation,[],[f23])).
% 1.61/0.57  fof(f53,plain,(
% 1.61/0.57    ~spl4_1),
% 1.61/0.57    inference(avatar_split_clause,[],[f28,f50])).
% 1.61/0.57  fof(f28,plain,(
% 1.61/0.57    sK1 != sK2),
% 1.61/0.57    inference(cnf_transformation,[],[f23])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (12752)------------------------------
% 1.61/0.57  % (12752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (12752)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (12752)Memory used [KB]: 7164
% 1.61/0.57  % (12752)Time elapsed: 0.154 s
% 1.61/0.57  % (12752)------------------------------
% 1.61/0.57  % (12752)------------------------------
% 1.61/0.57  % (12726)Success in time 0.214 s
%------------------------------------------------------------------------------
