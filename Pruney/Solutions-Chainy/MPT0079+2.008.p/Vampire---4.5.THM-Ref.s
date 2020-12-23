%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:52 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 383 expanded)
%              Number of leaves         :   45 ( 161 expanded)
%              Depth                    :   11
%              Number of atoms          :  375 ( 725 expanded)
%              Number of equality atoms :  158 ( 362 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f133,f145,f178,f195,f205,f280,f284,f296,f310,f320,f332,f457,f515,f538,f619,f683,f993,f1019,f1071,f1142,f1165,f1199,f1226,f1227])).

fof(f1227,plain,
    ( k4_xboole_0(sK2,sK3) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | sK1 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | sK2 != k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0)
    | sK2 = k2_xboole_0(sK1,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1226,plain,
    ( spl4_1
    | ~ spl4_67 ),
    inference(avatar_split_clause,[],[f1224,f1213,f51])).

fof(f51,plain,
    ( spl4_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1213,plain,
    ( spl4_67
  <=> sK2 = k2_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f1224,plain,
    ( sK1 = sK2
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f1214,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1214,plain,
    ( sK2 = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f1213])).

fof(f1199,plain,
    ( spl4_62
    | ~ spl4_53
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f1195,f1163,f1069,f1197])).

fof(f1197,plain,
    ( spl4_62
  <=> sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1069,plain,
    ( spl4_53
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1163,plain,
    ( spl4_59
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f1195,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl4_53
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f1186,f1070])).

fof(f1070,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f1186,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)
    | ~ spl4_59 ),
    inference(superposition,[],[f39,f1164])).

fof(f1164,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1165,plain,
    ( spl4_59
    | ~ spl4_4
    | ~ spl4_23
    | ~ spl4_39
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1161,f673,f536,f318,f63,f1163])).

fof(f63,plain,
    ( spl4_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f318,plain,
    ( spl4_23
  <=> k2_xboole_0(sK1,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f536,plain,
    ( spl4_39
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f673,plain,
    ( spl4_41
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1161,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)
    | ~ spl4_4
    | ~ spl4_23
    | ~ spl4_39
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f1160,f674])).

fof(f674,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f673])).

fof(f1160,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))
    | ~ spl4_4
    | ~ spl4_23
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f1159,f626])).

fof(f626,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f46,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1159,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3)))
    | ~ spl4_4
    | ~ spl4_23
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f1158,f638])).

fof(f638,plain,
    ( ! [X28] : k2_xboole_0(sK1,k2_xboole_0(sK2,X28)) = k2_xboole_0(sK1,X28)
    | ~ spl4_39 ),
    inference(superposition,[],[f46,f537])).

fof(f537,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f536])).

fof(f1158,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f1157,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1157,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK2))
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f1145,f646])).

fof(f646,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f46,f37])).

fof(f1145,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3))) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(superposition,[],[f668,f319])).

fof(f319,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK3))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f318])).

fof(f668,plain,
    ( ! [X29] : k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X29))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f639,f46])).

fof(f639,plain,
    ( ! [X29] : k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X29)
    | ~ spl4_4 ),
    inference(superposition,[],[f46,f64])).

fof(f64,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f1142,plain,
    ( spl4_58
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f1138,f965,f1140])).

fof(f1140,plain,
    ( spl4_58
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f965,plain,
    ( spl4_49
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f1138,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0)
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f1137,f86])).

fof(f86,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f77,f37])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1137,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f1131,f37])).

fof(f1131,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2)
    | ~ spl4_49 ),
    inference(superposition,[],[f40,f966])).

fof(f966,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f965])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1071,plain,
    ( spl4_53
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f1067,f960,f1069])).

fof(f960,plain,
    ( spl4_48
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f1067,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f1066,f77])).

fof(f1066,plain,
    ( k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f1059,f33])).

fof(f1059,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)
    | ~ spl4_48 ),
    inference(superposition,[],[f40,f961])).

fof(f961,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f960])).

fof(f1019,plain,
    ( spl4_48
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f928,f278,f960])).

fof(f278,plain,
    ( spl4_17
  <=> k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f928,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl4_17 ),
    inference(superposition,[],[f279,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f279,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f278])).

fof(f993,plain,
    ( spl4_49
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f992,f617,f965])).

fof(f617,plain,
    ( spl4_40
  <=> sK3 = k4_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f992,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f886,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f47,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f886,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | ~ spl4_40 ),
    inference(superposition,[],[f48,f618])).

fof(f618,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f617])).

fof(f683,plain,
    ( spl4_41
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f651,f203,f673])).

fof(f203,plain,
    ( spl4_12
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f651,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(superposition,[],[f204,f46])).

fof(f204,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f203])).

fof(f619,plain,
    ( spl4_40
    | ~ spl4_19
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f615,f536,f294,f617])).

fof(f294,plain,
    ( spl4_19
  <=> sK3 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f615,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_19
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f600,f295])).

fof(f295,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f294])).

fof(f600,plain,
    ( k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2)
    | ~ spl4_19
    | ~ spl4_39 ),
    inference(superposition,[],[f403,f537])).

fof(f403,plain,
    ( ! [X27] : k4_xboole_0(sK3,k2_xboole_0(sK1,X27)) = k4_xboole_0(sK3,X27)
    | ~ spl4_19 ),
    inference(superposition,[],[f45,f295])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f538,plain,
    ( spl4_39
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f534,f512,f536])).

fof(f512,plain,
    ( spl4_36
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f534,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f528,f33])).

fof(f528,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_36 ),
    inference(superposition,[],[f40,f513])).

fof(f513,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f512])).

fof(f515,plain,
    ( spl4_36
    | ~ spl4_24
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f497,f448,f330,f512])).

fof(f330,plain,
    ( spl4_24
  <=> sK2 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f448,plain,
    ( spl4_31
  <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f497,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl4_24
    | ~ spl4_31 ),
    inference(superposition,[],[f449,f398])).

fof(f398,plain,
    ( ! [X22] : k4_xboole_0(sK2,k2_xboole_0(sK0,X22)) = k4_xboole_0(sK2,X22)
    | ~ spl4_24 ),
    inference(superposition,[],[f45,f331])).

fof(f331,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f330])).

fof(f449,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f448])).

fof(f457,plain,
    ( spl4_31
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f456,f176,f143,f448])).

fof(f143,plain,
    ( spl4_6
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK3),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f176,plain,
    ( spl4_10
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f456,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f411,f177])).

fof(f177,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f411,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f144,f45])).

fof(f144,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK3),k2_xboole_0(sK0,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f332,plain,
    ( spl4_24
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f328,f282,f330])).

fof(f282,plain,
    ( spl4_18
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f328,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f327,f77])).

fof(f327,plain,
    ( k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f322,f33])).

fof(f322,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)
    | ~ spl4_18 ),
    inference(superposition,[],[f40,f283])).

fof(f283,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f282])).

fof(f320,plain,
    ( spl4_23
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f312,f308,f318])).

fof(f308,plain,
    ( spl4_21
  <=> r1_tarski(sK3,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f312,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK3))
    | ~ spl4_21 ),
    inference(resolution,[],[f309,f41])).

fof(f309,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK1,sK3))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f308])).

fof(f310,plain,
    ( spl4_21
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f306,f294,f308])).

fof(f306,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK1,sK3))
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f301,f37])).

fof(f301,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK3,sK1))
    | ~ spl4_19 ),
    inference(superposition,[],[f125,f295])).

fof(f125,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f35,f39])).

fof(f296,plain,
    ( spl4_19
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f292,f278,f294])).

fof(f292,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f291,f77])).

fof(f291,plain,
    ( k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f286,f33])).

fof(f286,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)
    | ~ spl4_17 ),
    inference(superposition,[],[f40,f279])).

fof(f284,plain,
    ( spl4_18
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f276,f59,f282])).

fof(f59,plain,
    ( spl4_3
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f276,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f49,f60])).

fof(f60,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f280,plain,
    ( spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f275,f55,f278])).

fof(f55,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f275,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f49,f56])).

fof(f56,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f205,plain,
    ( spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f201,f193,f203])).

fof(f193,plain,
    ( spl4_11
  <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f201,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f196,f33])).

fof(f196,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f40,f194])).

fof(f194,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f191,f176,f193])).

fof(f191,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f190,f75])).

fof(f190,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | ~ spl4_10 ),
    inference(superposition,[],[f39,f177])).

fof(f178,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f174,f131,f63,f176])).

fof(f131,plain,
    ( spl4_5
  <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f174,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f173,f64])).

fof(f173,plain,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f172,f37])).

fof(f172,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f161,f40])).

fof(f161,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f40,f132])).

fof(f132,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f145,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f138,f131,f143])).

fof(f138,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK3),k2_xboole_0(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f101,f132])).

fof(f101,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f44,f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f133,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f120,f63,f131])).

fof(f120,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl4_4 ),
    inference(superposition,[],[f39,f64])).

fof(f65,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f24])).

fof(f24,plain,
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

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f61,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:07:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (25838)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (25859)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (25850)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (25851)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.57  % (25851)Refutation not found, incomplete strategy% (25851)------------------------------
% 0.22/0.57  % (25851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (25858)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (25851)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (25851)Memory used [KB]: 6140
% 0.22/0.57  % (25851)Time elapsed: 0.005 s
% 0.22/0.57  % (25851)------------------------------
% 0.22/0.57  % (25851)------------------------------
% 0.22/0.57  % (25843)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.58  % (25847)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.59  % (25836)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.59  % (25837)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.59  % (25840)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (25845)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.60  % (25841)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.60  % (25842)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.60  % (25846)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.61  % (25839)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.94/0.61  % (25856)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.94/0.61  % (25863)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.94/0.61  % (25861)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.94/0.62  % (25848)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.94/0.62  % (25855)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.94/0.62  % (25853)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.94/0.62  % (25864)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.94/0.62  % (25865)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.94/0.62  % (25860)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.94/0.62  % (25857)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.94/0.63  % (25852)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.08/0.63  % (25862)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.08/0.63  % (25849)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.08/0.63  % (25844)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.08/0.64  % (25854)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.21/0.65  % (25853)Refutation not found, incomplete strategy% (25853)------------------------------
% 2.21/0.65  % (25853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (25853)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.65  
% 2.21/0.65  % (25853)Memory used [KB]: 10618
% 2.21/0.65  % (25853)Time elapsed: 0.220 s
% 2.21/0.65  % (25853)------------------------------
% 2.21/0.65  % (25853)------------------------------
% 2.21/0.70  % (25855)Refutation found. Thanks to Tanya!
% 2.21/0.70  % SZS status Theorem for theBenchmark
% 2.21/0.71  % SZS output start Proof for theBenchmark
% 2.21/0.71  fof(f1228,plain,(
% 2.21/0.71    $false),
% 2.21/0.71    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f133,f145,f178,f195,f205,f280,f284,f296,f310,f320,f332,f457,f515,f538,f619,f683,f993,f1019,f1071,f1142,f1165,f1199,f1226,f1227])).
% 2.21/0.71  fof(f1227,plain,(
% 2.21/0.71    k4_xboole_0(sK2,sK3) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | sK1 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | sK2 != k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) | sK2 = k2_xboole_0(sK1,k1_xboole_0)),
% 2.21/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.21/0.71  fof(f1226,plain,(
% 2.21/0.71    spl4_1 | ~spl4_67),
% 2.21/0.71    inference(avatar_split_clause,[],[f1224,f1213,f51])).
% 2.21/0.71  fof(f51,plain,(
% 2.21/0.71    spl4_1 <=> sK1 = sK2),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.21/0.71  fof(f1213,plain,(
% 2.21/0.71    spl4_67 <=> sK2 = k2_xboole_0(sK1,k1_xboole_0)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 2.21/0.71  fof(f1224,plain,(
% 2.21/0.71    sK1 = sK2 | ~spl4_67),
% 2.21/0.71    inference(forward_demodulation,[],[f1214,f33])).
% 2.21/0.71  fof(f33,plain,(
% 2.21/0.71    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.71    inference(cnf_transformation,[],[f7])).
% 2.21/0.71  fof(f7,axiom,(
% 2.21/0.71    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.21/0.71  fof(f1214,plain,(
% 2.21/0.71    sK2 = k2_xboole_0(sK1,k1_xboole_0) | ~spl4_67),
% 2.21/0.71    inference(avatar_component_clause,[],[f1213])).
% 2.21/0.71  fof(f1199,plain,(
% 2.21/0.71    spl4_62 | ~spl4_53 | ~spl4_59),
% 2.21/0.71    inference(avatar_split_clause,[],[f1195,f1163,f1069,f1197])).
% 2.21/0.71  fof(f1197,plain,(
% 2.21/0.71    spl4_62 <=> sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 2.21/0.71  fof(f1069,plain,(
% 2.21/0.71    spl4_53 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.21/0.71  fof(f1163,plain,(
% 2.21/0.71    spl4_59 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 2.21/0.71  fof(f1195,plain,(
% 2.21/0.71    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | (~spl4_53 | ~spl4_59)),
% 2.21/0.71    inference(forward_demodulation,[],[f1186,f1070])).
% 2.21/0.71  fof(f1070,plain,(
% 2.21/0.71    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_53),
% 2.21/0.71    inference(avatar_component_clause,[],[f1069])).
% 2.21/0.71  fof(f1186,plain,(
% 2.21/0.71    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) | ~spl4_59),
% 2.21/0.71    inference(superposition,[],[f39,f1164])).
% 2.21/0.71  fof(f1164,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) | ~spl4_59),
% 2.21/0.71    inference(avatar_component_clause,[],[f1163])).
% 2.21/0.71  fof(f39,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.21/0.71    inference(cnf_transformation,[],[f12])).
% 2.21/0.71  fof(f12,axiom,(
% 2.21/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.21/0.71  fof(f1165,plain,(
% 2.21/0.71    spl4_59 | ~spl4_4 | ~spl4_23 | ~spl4_39 | ~spl4_41),
% 2.21/0.71    inference(avatar_split_clause,[],[f1161,f673,f536,f318,f63,f1163])).
% 2.21/0.71  fof(f63,plain,(
% 2.21/0.71    spl4_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.21/0.71  fof(f318,plain,(
% 2.21/0.71    spl4_23 <=> k2_xboole_0(sK1,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK3))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.21/0.71  fof(f536,plain,(
% 2.21/0.71    spl4_39 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.21/0.71  fof(f673,plain,(
% 2.21/0.71    spl4_41 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.21/0.71  fof(f1161,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) | (~spl4_4 | ~spl4_23 | ~spl4_39 | ~spl4_41)),
% 2.21/0.71    inference(forward_demodulation,[],[f1160,f674])).
% 2.21/0.71  fof(f674,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) | ~spl4_41),
% 2.21/0.71    inference(avatar_component_clause,[],[f673])).
% 2.21/0.71  fof(f1160,plain,(
% 2.21/0.71    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) | (~spl4_4 | ~spl4_23 | ~spl4_39)),
% 2.21/0.71    inference(forward_demodulation,[],[f1159,f626])).
% 2.21/0.71  fof(f626,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.21/0.71    inference(superposition,[],[f46,f34])).
% 2.21/0.71  fof(f34,plain,(
% 2.21/0.71    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.21/0.71    inference(cnf_transformation,[],[f18])).
% 2.21/0.71  fof(f18,plain,(
% 2.21/0.71    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.21/0.71    inference(rectify,[],[f4])).
% 2.21/0.71  fof(f4,axiom,(
% 2.21/0.71    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.21/0.71  fof(f46,plain,(
% 2.21/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.71    inference(cnf_transformation,[],[f15])).
% 2.21/0.71  fof(f15,axiom,(
% 2.21/0.71    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.21/0.71  fof(f1159,plain,(
% 2.21/0.71    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3))) | (~spl4_4 | ~spl4_23 | ~spl4_39)),
% 2.21/0.71    inference(forward_demodulation,[],[f1158,f638])).
% 2.21/0.71  fof(f638,plain,(
% 2.21/0.71    ( ! [X28] : (k2_xboole_0(sK1,k2_xboole_0(sK2,X28)) = k2_xboole_0(sK1,X28)) ) | ~spl4_39),
% 2.21/0.71    inference(superposition,[],[f46,f537])).
% 2.21/0.71  fof(f537,plain,(
% 2.21/0.71    sK1 = k2_xboole_0(sK1,sK2) | ~spl4_39),
% 2.21/0.71    inference(avatar_component_clause,[],[f536])).
% 2.21/0.71  fof(f1158,plain,(
% 2.21/0.71    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | (~spl4_4 | ~spl4_23)),
% 2.21/0.71    inference(forward_demodulation,[],[f1157,f37])).
% 2.21/0.71  fof(f37,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.21/0.71    inference(cnf_transformation,[],[f1])).
% 2.21/0.71  fof(f1,axiom,(
% 2.21/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.21/0.71  fof(f1157,plain,(
% 2.21/0.71    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK2)) | (~spl4_4 | ~spl4_23)),
% 2.21/0.71    inference(forward_demodulation,[],[f1145,f646])).
% 2.21/0.71  fof(f646,plain,(
% 2.21/0.71    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 2.21/0.71    inference(superposition,[],[f46,f37])).
% 2.21/0.71  fof(f1145,plain,(
% 2.21/0.71    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3))) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK3)) | (~spl4_4 | ~spl4_23)),
% 2.21/0.71    inference(superposition,[],[f668,f319])).
% 2.21/0.71  fof(f319,plain,(
% 2.21/0.71    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK3)) | ~spl4_23),
% 2.21/0.71    inference(avatar_component_clause,[],[f318])).
% 2.21/0.71  fof(f668,plain,(
% 2.21/0.71    ( ! [X29] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X29))) ) | ~spl4_4),
% 2.21/0.71    inference(forward_demodulation,[],[f639,f46])).
% 2.21/0.71  fof(f639,plain,(
% 2.21/0.71    ( ! [X29] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X29)) ) | ~spl4_4),
% 2.21/0.71    inference(superposition,[],[f46,f64])).
% 2.21/0.71  fof(f64,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) | ~spl4_4),
% 2.21/0.71    inference(avatar_component_clause,[],[f63])).
% 2.21/0.71  fof(f1142,plain,(
% 2.21/0.71    spl4_58 | ~spl4_49),
% 2.21/0.71    inference(avatar_split_clause,[],[f1138,f965,f1140])).
% 2.21/0.71  fof(f1140,plain,(
% 2.21/0.71    spl4_58 <=> sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.21/0.71  fof(f965,plain,(
% 2.21/0.71    spl4_49 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.21/0.71  fof(f1138,plain,(
% 2.21/0.71    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) | ~spl4_49),
% 2.21/0.71    inference(forward_demodulation,[],[f1137,f86])).
% 2.21/0.71  fof(f86,plain,(
% 2.21/0.71    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 2.21/0.71    inference(superposition,[],[f77,f37])).
% 2.21/0.71  fof(f77,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 2.21/0.71    inference(resolution,[],[f41,f35])).
% 2.21/0.71  fof(f35,plain,(
% 2.21/0.71    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.21/0.71    inference(cnf_transformation,[],[f9])).
% 2.21/0.71  fof(f9,axiom,(
% 2.21/0.71    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.21/0.71  fof(f41,plain,(
% 2.21/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.21/0.71    inference(cnf_transformation,[],[f22])).
% 2.21/0.71  fof(f22,plain,(
% 2.21/0.71    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.21/0.71    inference(ennf_transformation,[],[f6])).
% 2.21/0.71  fof(f6,axiom,(
% 2.21/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.21/0.71  fof(f1137,plain,(
% 2.21/0.71    k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK3)) | ~spl4_49),
% 2.21/0.71    inference(forward_demodulation,[],[f1131,f37])).
% 2.21/0.71  fof(f1131,plain,(
% 2.21/0.71    k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) | ~spl4_49),
% 2.21/0.71    inference(superposition,[],[f40,f966])).
% 2.21/0.71  fof(f966,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) | ~spl4_49),
% 2.21/0.71    inference(avatar_component_clause,[],[f965])).
% 2.21/0.71  fof(f40,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.21/0.71    inference(cnf_transformation,[],[f10])).
% 2.21/0.71  fof(f10,axiom,(
% 2.21/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.21/0.71  fof(f1071,plain,(
% 2.21/0.71    spl4_53 | ~spl4_48),
% 2.21/0.71    inference(avatar_split_clause,[],[f1067,f960,f1069])).
% 2.21/0.71  fof(f960,plain,(
% 2.21/0.71    spl4_48 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.21/0.71  fof(f1067,plain,(
% 2.21/0.71    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_48),
% 2.21/0.71    inference(forward_demodulation,[],[f1066,f77])).
% 2.21/0.71  fof(f1066,plain,(
% 2.21/0.71    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) | ~spl4_48),
% 2.21/0.71    inference(forward_demodulation,[],[f1059,f33])).
% 2.21/0.71  fof(f1059,plain,(
% 2.21/0.71    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) | ~spl4_48),
% 2.21/0.71    inference(superposition,[],[f40,f961])).
% 2.21/0.71  fof(f961,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl4_48),
% 2.21/0.71    inference(avatar_component_clause,[],[f960])).
% 2.21/0.71  fof(f1019,plain,(
% 2.21/0.71    spl4_48 | ~spl4_17),
% 2.21/0.71    inference(avatar_split_clause,[],[f928,f278,f960])).
% 2.21/0.71  fof(f278,plain,(
% 2.21/0.71    spl4_17 <=> k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.21/0.71  fof(f928,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl4_17),
% 2.21/0.71    inference(superposition,[],[f279,f48])).
% 2.21/0.71  fof(f48,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.21/0.71    inference(definition_unfolding,[],[f36,f38,f38])).
% 2.21/0.71  fof(f38,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.71    inference(cnf_transformation,[],[f14])).
% 2.21/0.71  fof(f14,axiom,(
% 2.21/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.21/0.71  fof(f36,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.21/0.71    inference(cnf_transformation,[],[f2])).
% 2.21/0.71  fof(f2,axiom,(
% 2.21/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.21/0.71  fof(f279,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) | ~spl4_17),
% 2.21/0.71    inference(avatar_component_clause,[],[f278])).
% 2.21/0.71  fof(f993,plain,(
% 2.21/0.71    spl4_49 | ~spl4_40),
% 2.21/0.71    inference(avatar_split_clause,[],[f992,f617,f965])).
% 2.21/0.71  fof(f617,plain,(
% 2.21/0.71    spl4_40 <=> sK3 = k4_xboole_0(sK3,sK2)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.21/0.71  fof(f992,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) | ~spl4_40),
% 2.21/0.71    inference(forward_demodulation,[],[f886,f75])).
% 2.21/0.71  fof(f75,plain,(
% 2.21/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.21/0.71    inference(superposition,[],[f47,f32])).
% 2.21/0.71  fof(f32,plain,(
% 2.21/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.71    inference(cnf_transformation,[],[f11])).
% 2.21/0.71  fof(f11,axiom,(
% 2.21/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.21/0.71  fof(f47,plain,(
% 2.21/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.21/0.71    inference(definition_unfolding,[],[f31,f38])).
% 2.21/0.71  fof(f31,plain,(
% 2.21/0.71    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.21/0.71    inference(cnf_transformation,[],[f8])).
% 2.21/0.71  fof(f8,axiom,(
% 2.21/0.71    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.21/0.71  fof(f886,plain,(
% 2.21/0.71    k4_xboole_0(sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) | ~spl4_40),
% 2.21/0.71    inference(superposition,[],[f48,f618])).
% 2.21/0.71  fof(f618,plain,(
% 2.21/0.71    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_40),
% 2.21/0.71    inference(avatar_component_clause,[],[f617])).
% 2.21/0.71  fof(f683,plain,(
% 2.21/0.71    spl4_41 | ~spl4_12),
% 2.21/0.71    inference(avatar_split_clause,[],[f651,f203,f673])).
% 2.21/0.71  fof(f203,plain,(
% 2.21/0.71    spl4_12 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.21/0.71  fof(f651,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) | ~spl4_12),
% 2.21/0.71    inference(superposition,[],[f204,f46])).
% 2.21/0.71  fof(f204,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl4_12),
% 2.21/0.71    inference(avatar_component_clause,[],[f203])).
% 2.21/0.71  fof(f619,plain,(
% 2.21/0.71    spl4_40 | ~spl4_19 | ~spl4_39),
% 2.21/0.71    inference(avatar_split_clause,[],[f615,f536,f294,f617])).
% 2.21/0.71  fof(f294,plain,(
% 2.21/0.71    spl4_19 <=> sK3 = k4_xboole_0(sK3,sK1)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.21/0.71  fof(f615,plain,(
% 2.21/0.71    sK3 = k4_xboole_0(sK3,sK2) | (~spl4_19 | ~spl4_39)),
% 2.21/0.71    inference(forward_demodulation,[],[f600,f295])).
% 2.21/0.71  fof(f295,plain,(
% 2.21/0.71    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_19),
% 2.21/0.71    inference(avatar_component_clause,[],[f294])).
% 2.21/0.71  fof(f600,plain,(
% 2.21/0.71    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) | (~spl4_19 | ~spl4_39)),
% 2.21/0.71    inference(superposition,[],[f403,f537])).
% 2.21/0.71  fof(f403,plain,(
% 2.21/0.71    ( ! [X27] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X27)) = k4_xboole_0(sK3,X27)) ) | ~spl4_19),
% 2.21/0.71    inference(superposition,[],[f45,f295])).
% 2.21/0.71  fof(f45,plain,(
% 2.21/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.71    inference(cnf_transformation,[],[f13])).
% 2.21/0.71  fof(f13,axiom,(
% 2.21/0.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.21/0.71  fof(f538,plain,(
% 2.21/0.71    spl4_39 | ~spl4_36),
% 2.21/0.71    inference(avatar_split_clause,[],[f534,f512,f536])).
% 2.21/0.71  fof(f512,plain,(
% 2.21/0.71    spl4_36 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.21/0.71  fof(f534,plain,(
% 2.21/0.71    sK1 = k2_xboole_0(sK1,sK2) | ~spl4_36),
% 2.21/0.71    inference(forward_demodulation,[],[f528,f33])).
% 2.21/0.71  fof(f528,plain,(
% 2.21/0.71    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) | ~spl4_36),
% 2.21/0.71    inference(superposition,[],[f40,f513])).
% 2.21/0.71  fof(f513,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl4_36),
% 2.21/0.71    inference(avatar_component_clause,[],[f512])).
% 2.21/0.71  fof(f515,plain,(
% 2.21/0.71    spl4_36 | ~spl4_24 | ~spl4_31),
% 2.21/0.71    inference(avatar_split_clause,[],[f497,f448,f330,f512])).
% 2.21/0.71  fof(f330,plain,(
% 2.21/0.71    spl4_24 <=> sK2 = k4_xboole_0(sK2,sK0)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.21/0.71  fof(f448,plain,(
% 2.21/0.71    spl4_31 <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.21/0.71  fof(f497,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl4_24 | ~spl4_31)),
% 2.21/0.71    inference(superposition,[],[f449,f398])).
% 2.21/0.71  fof(f398,plain,(
% 2.21/0.71    ( ! [X22] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X22)) = k4_xboole_0(sK2,X22)) ) | ~spl4_24),
% 2.21/0.71    inference(superposition,[],[f45,f331])).
% 2.21/0.71  fof(f331,plain,(
% 2.21/0.71    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_24),
% 2.21/0.71    inference(avatar_component_clause,[],[f330])).
% 2.21/0.71  fof(f449,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_31),
% 2.21/0.71    inference(avatar_component_clause,[],[f448])).
% 2.21/0.71  fof(f457,plain,(
% 2.21/0.71    spl4_31 | ~spl4_6 | ~spl4_10),
% 2.21/0.71    inference(avatar_split_clause,[],[f456,f176,f143,f448])).
% 2.21/0.71  fof(f143,plain,(
% 2.21/0.71    spl4_6 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK3),k2_xboole_0(sK0,sK1))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.21/0.71  fof(f176,plain,(
% 2.21/0.71    spl4_10 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.21/0.71  fof(f456,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | (~spl4_6 | ~spl4_10)),
% 2.21/0.71    inference(forward_demodulation,[],[f411,f177])).
% 2.21/0.71  fof(f177,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_10),
% 2.21/0.71    inference(avatar_component_clause,[],[f176])).
% 2.21/0.71  fof(f411,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))) | ~spl4_6),
% 2.21/0.71    inference(superposition,[],[f144,f45])).
% 2.21/0.71  fof(f144,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK3),k2_xboole_0(sK0,sK1)) | ~spl4_6),
% 2.21/0.71    inference(avatar_component_clause,[],[f143])).
% 2.21/0.71  fof(f332,plain,(
% 2.21/0.71    spl4_24 | ~spl4_18),
% 2.21/0.71    inference(avatar_split_clause,[],[f328,f282,f330])).
% 2.21/0.71  fof(f282,plain,(
% 2.21/0.71    spl4_18 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.21/0.71  fof(f328,plain,(
% 2.21/0.71    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_18),
% 2.21/0.71    inference(forward_demodulation,[],[f327,f77])).
% 2.21/0.71  fof(f327,plain,(
% 2.21/0.71    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) | ~spl4_18),
% 2.21/0.71    inference(forward_demodulation,[],[f322,f33])).
% 2.21/0.71  fof(f322,plain,(
% 2.21/0.71    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) | ~spl4_18),
% 2.21/0.71    inference(superposition,[],[f40,f283])).
% 2.21/0.71  fof(f283,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_18),
% 2.21/0.71    inference(avatar_component_clause,[],[f282])).
% 2.21/0.71  fof(f320,plain,(
% 2.21/0.71    spl4_23 | ~spl4_21),
% 2.21/0.71    inference(avatar_split_clause,[],[f312,f308,f318])).
% 2.21/0.71  fof(f308,plain,(
% 2.21/0.71    spl4_21 <=> r1_tarski(sK3,k2_xboole_0(sK1,sK3))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.21/0.71  fof(f312,plain,(
% 2.21/0.71    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK3)) | ~spl4_21),
% 2.21/0.71    inference(resolution,[],[f309,f41])).
% 2.21/0.71  fof(f309,plain,(
% 2.21/0.71    r1_tarski(sK3,k2_xboole_0(sK1,sK3)) | ~spl4_21),
% 2.21/0.71    inference(avatar_component_clause,[],[f308])).
% 2.21/0.71  fof(f310,plain,(
% 2.21/0.71    spl4_21 | ~spl4_19),
% 2.21/0.71    inference(avatar_split_clause,[],[f306,f294,f308])).
% 2.21/0.71  fof(f306,plain,(
% 2.21/0.71    r1_tarski(sK3,k2_xboole_0(sK1,sK3)) | ~spl4_19),
% 2.21/0.71    inference(forward_demodulation,[],[f301,f37])).
% 2.21/0.71  fof(f301,plain,(
% 2.21/0.71    r1_tarski(sK3,k2_xboole_0(sK3,sK1)) | ~spl4_19),
% 2.21/0.71    inference(superposition,[],[f125,f295])).
% 2.21/0.71  fof(f125,plain,(
% 2.21/0.71    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7))) )),
% 2.21/0.71    inference(superposition,[],[f35,f39])).
% 2.21/0.71  fof(f296,plain,(
% 2.21/0.71    spl4_19 | ~spl4_17),
% 2.21/0.71    inference(avatar_split_clause,[],[f292,f278,f294])).
% 2.21/0.71  fof(f292,plain,(
% 2.21/0.71    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_17),
% 2.21/0.71    inference(forward_demodulation,[],[f291,f77])).
% 2.21/0.71  fof(f291,plain,(
% 2.21/0.71    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) | ~spl4_17),
% 2.21/0.71    inference(forward_demodulation,[],[f286,f33])).
% 2.21/0.71  fof(f286,plain,(
% 2.21/0.71    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) | ~spl4_17),
% 2.21/0.71    inference(superposition,[],[f40,f279])).
% 2.21/0.71  fof(f284,plain,(
% 2.21/0.71    spl4_18 | ~spl4_3),
% 2.21/0.71    inference(avatar_split_clause,[],[f276,f59,f282])).
% 2.21/0.71  fof(f59,plain,(
% 2.21/0.71    spl4_3 <=> r1_xboole_0(sK2,sK0)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.21/0.71  fof(f276,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_3),
% 2.21/0.71    inference(resolution,[],[f49,f60])).
% 2.21/0.71  fof(f60,plain,(
% 2.21/0.71    r1_xboole_0(sK2,sK0) | ~spl4_3),
% 2.21/0.71    inference(avatar_component_clause,[],[f59])).
% 2.21/0.71  fof(f49,plain,(
% 2.21/0.71    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.71    inference(definition_unfolding,[],[f42,f38])).
% 2.21/0.71  fof(f42,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.21/0.71    inference(cnf_transformation,[],[f23])).
% 2.21/0.71  fof(f23,plain,(
% 2.21/0.71    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.21/0.71    inference(ennf_transformation,[],[f19])).
% 2.21/0.71  fof(f19,plain,(
% 2.21/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.21/0.71    inference(unused_predicate_definition_removal,[],[f3])).
% 2.21/0.71  fof(f3,axiom,(
% 2.21/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.21/0.71  fof(f280,plain,(
% 2.21/0.71    spl4_17 | ~spl4_2),
% 2.21/0.71    inference(avatar_split_clause,[],[f275,f55,f278])).
% 2.21/0.71  fof(f55,plain,(
% 2.21/0.71    spl4_2 <=> r1_xboole_0(sK3,sK1)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.21/0.71  fof(f275,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) | ~spl4_2),
% 2.21/0.71    inference(resolution,[],[f49,f56])).
% 2.21/0.71  fof(f56,plain,(
% 2.21/0.71    r1_xboole_0(sK3,sK1) | ~spl4_2),
% 2.21/0.71    inference(avatar_component_clause,[],[f55])).
% 2.21/0.71  fof(f205,plain,(
% 2.21/0.71    spl4_12 | ~spl4_11),
% 2.21/0.71    inference(avatar_split_clause,[],[f201,f193,f203])).
% 2.21/0.71  fof(f193,plain,(
% 2.21/0.71    spl4_11 <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.21/0.71  fof(f201,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl4_11),
% 2.21/0.71    inference(forward_demodulation,[],[f196,f33])).
% 2.21/0.71  fof(f196,plain,(
% 2.21/0.71    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) | ~spl4_11),
% 2.21/0.71    inference(superposition,[],[f40,f194])).
% 2.21/0.71  fof(f194,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_11),
% 2.21/0.71    inference(avatar_component_clause,[],[f193])).
% 2.21/0.71  fof(f195,plain,(
% 2.21/0.71    spl4_11 | ~spl4_10),
% 2.21/0.71    inference(avatar_split_clause,[],[f191,f176,f193])).
% 2.21/0.71  fof(f191,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_10),
% 2.21/0.71    inference(forward_demodulation,[],[f190,f75])).
% 2.21/0.71  fof(f190,plain,(
% 2.21/0.71    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | ~spl4_10),
% 2.21/0.71    inference(superposition,[],[f39,f177])).
% 2.21/0.71  fof(f178,plain,(
% 2.21/0.71    spl4_10 | ~spl4_4 | ~spl4_5),
% 2.21/0.71    inference(avatar_split_clause,[],[f174,f131,f63,f176])).
% 2.21/0.71  fof(f131,plain,(
% 2.21/0.71    spl4_5 <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.21/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.21/0.71  fof(f174,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | (~spl4_4 | ~spl4_5)),
% 2.21/0.71    inference(forward_demodulation,[],[f173,f64])).
% 2.21/0.71  fof(f173,plain,(
% 2.21/0.71    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_5),
% 2.21/0.71    inference(forward_demodulation,[],[f172,f37])).
% 2.21/0.71  fof(f172,plain,(
% 2.21/0.71    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_5),
% 2.21/0.71    inference(forward_demodulation,[],[f161,f40])).
% 2.21/0.71  fof(f161,plain,(
% 2.21/0.71    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) | ~spl4_5),
% 2.21/0.71    inference(superposition,[],[f40,f132])).
% 2.21/0.71  fof(f132,plain,(
% 2.21/0.71    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl4_5),
% 2.21/0.71    inference(avatar_component_clause,[],[f131])).
% 2.21/0.71  fof(f145,plain,(
% 2.21/0.71    spl4_6 | ~spl4_5),
% 2.21/0.71    inference(avatar_split_clause,[],[f138,f131,f143])).
% 2.21/0.71  fof(f138,plain,(
% 2.21/0.71    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK3),k2_xboole_0(sK0,sK1)) | ~spl4_5),
% 2.21/0.71    inference(superposition,[],[f101,f132])).
% 2.21/0.71  fof(f101,plain,(
% 2.21/0.71    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 2.21/0.71    inference(resolution,[],[f44,f35])).
% 2.21/0.71  fof(f44,plain,(
% 2.21/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.21/0.71    inference(cnf_transformation,[],[f26])).
% 2.21/0.71  fof(f26,plain,(
% 2.21/0.71    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.21/0.71    inference(nnf_transformation,[],[f5])).
% 2.21/0.71  fof(f5,axiom,(
% 2.21/0.71    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.21/0.71  fof(f133,plain,(
% 2.21/0.71    spl4_5 | ~spl4_4),
% 2.21/0.71    inference(avatar_split_clause,[],[f120,f63,f131])).
% 2.21/0.71  fof(f120,plain,(
% 2.21/0.71    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl4_4),
% 2.21/0.71    inference(superposition,[],[f39,f64])).
% 2.21/0.71  fof(f65,plain,(
% 2.21/0.71    spl4_4),
% 2.21/0.71    inference(avatar_split_clause,[],[f27,f63])).
% 2.21/0.71  fof(f27,plain,(
% 2.21/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.21/0.71    inference(cnf_transformation,[],[f25])).
% 2.21/0.71  fof(f25,plain,(
% 2.21/0.71    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.21/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f24])).
% 2.70/0.72  fof(f24,plain,(
% 2.70/0.72    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 2.70/0.72    introduced(choice_axiom,[])).
% 2.70/0.72  fof(f21,plain,(
% 2.70/0.72    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.70/0.72    inference(flattening,[],[f20])).
% 2.70/0.72  fof(f20,plain,(
% 2.70/0.72    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.70/0.72    inference(ennf_transformation,[],[f17])).
% 2.70/0.72  fof(f17,negated_conjecture,(
% 2.70/0.72    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.70/0.72    inference(negated_conjecture,[],[f16])).
% 2.70/0.72  fof(f16,conjecture,(
% 2.70/0.72    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.70/0.72  fof(f61,plain,(
% 2.70/0.72    spl4_3),
% 2.70/0.72    inference(avatar_split_clause,[],[f28,f59])).
% 2.70/0.72  fof(f28,plain,(
% 2.70/0.72    r1_xboole_0(sK2,sK0)),
% 2.70/0.72    inference(cnf_transformation,[],[f25])).
% 2.70/0.72  fof(f57,plain,(
% 2.70/0.72    spl4_2),
% 2.70/0.72    inference(avatar_split_clause,[],[f29,f55])).
% 2.70/0.72  fof(f29,plain,(
% 2.70/0.72    r1_xboole_0(sK3,sK1)),
% 2.70/0.72    inference(cnf_transformation,[],[f25])).
% 2.70/0.72  fof(f53,plain,(
% 2.70/0.72    ~spl4_1),
% 2.70/0.72    inference(avatar_split_clause,[],[f30,f51])).
% 2.70/0.72  fof(f30,plain,(
% 2.70/0.72    sK1 != sK2),
% 2.70/0.72    inference(cnf_transformation,[],[f25])).
% 2.70/0.72  % SZS output end Proof for theBenchmark
% 2.70/0.72  % (25855)------------------------------
% 2.70/0.72  % (25855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.72  % (25855)Termination reason: Refutation
% 2.70/0.72  
% 2.70/0.72  % (25855)Memory used [KB]: 11641
% 2.70/0.72  % (25855)Time elapsed: 0.289 s
% 2.70/0.72  % (25855)------------------------------
% 2.70/0.72  % (25855)------------------------------
% 2.70/0.72  % (25835)Success in time 0.358 s
%------------------------------------------------------------------------------
