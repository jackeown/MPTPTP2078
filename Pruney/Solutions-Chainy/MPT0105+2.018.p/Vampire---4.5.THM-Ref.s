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
% DateTime   : Thu Dec  3 12:32:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 136 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  187 ( 279 expanded)
%              Number of equality atoms :   72 ( 118 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f43,f47,f51,f59,f63,f71,f75,f79,f129,f243,f362,f503,f1078,f1148,f1184])).

fof(f1184,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_46
    | ~ spl2_48 ),
    inference(avatar_contradiction_clause,[],[f1183])).

fof(f1183,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_46
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f30,f1182])).

fof(f1182,plain,
    ( ! [X8,X7] : k5_xboole_0(X8,k4_xboole_0(X7,X8)) = k2_xboole_0(X8,X7)
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_46
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1181,f62])).

fof(f62,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f1181,plain,
    ( ! [X8,X7] : k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k5_xboole_0(X8,k4_xboole_0(X7,X8))
    | ~ spl2_5
    | ~ spl2_46
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1154,f46])).

fof(f46,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_5
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1154,plain,
    ( ! [X8,X7] : k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X7,X8),k1_xboole_0))
    | ~ spl2_46
    | ~ spl2_48 ),
    inference(superposition,[],[f1147,f1077])).

fof(f1077,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f1076,plain,
    ( spl2_46
  <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f1147,plain,
    ( ! [X4,X3] : k2_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1146,plain,
    ( spl2_48
  <=> ! [X3,X4] : k2_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f30,plain,
    ( k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1148,plain,
    ( spl2_48
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f256,f241,f77,f1146])).

fof(f77,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f241,plain,
    ( spl2_23
  <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f256,plain,
    ( ! [X4,X3] : k2_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(superposition,[],[f242,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f242,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f241])).

fof(f1078,plain,
    ( spl2_46
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_28
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f543,f501,f360,f127,f73,f61,f1076])).

fof(f73,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f127,plain,
    ( spl2_13
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f360,plain,
    ( spl2_28
  <=> ! [X3,X2,X4] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f501,plain,
    ( spl2_33
  <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f543,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_28
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f542,f135])).

fof(f135,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f130,f62])).

fof(f130,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(superposition,[],[f128,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f128,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f542,plain,
    ( ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl2_8
    | ~ spl2_28
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f514,f62])).

fof(f514,plain,
    ( ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_28
    | ~ spl2_33 ),
    inference(superposition,[],[f502,f361])).

fof(f361,plain,
    ( ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f360])).

fof(f502,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f501])).

fof(f503,plain,
    ( spl2_33
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f106,f73,f57,f501])).

fof(f57,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f106,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f99,f74])).

fof(f99,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7)))
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(superposition,[],[f74,f58])).

fof(f58,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f362,plain,
    ( spl2_28
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f101,f73,f61,f360])).

fof(f101,plain,
    ( ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(superposition,[],[f62,f74])).

fof(f243,plain,
    ( spl2_23
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f88,f69,f49,f241])).

fof(f49,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f69,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f88,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f70,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f70,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f129,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f66,f57,f41,f33,f127])).

fof(f33,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( spl2_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f66,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f64,f34])).

fof(f34,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f64,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f58,f42])).

fof(f42,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f79,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f26,f77])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f75,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f25,f73])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f71,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f24,f69])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f63,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f59,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f51,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (4316)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (4316)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f1201,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f31,f35,f43,f47,f51,f59,f63,f71,f75,f79,f129,f243,f362,f503,f1078,f1148,f1184])).
% 0.22/0.49  fof(f1184,plain,(
% 0.22/0.49    spl2_1 | ~spl2_5 | ~spl2_8 | ~spl2_46 | ~spl2_48),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f1183])).
% 0.22/0.49  fof(f1183,plain,(
% 0.22/0.49    $false | (spl2_1 | ~spl2_5 | ~spl2_8 | ~spl2_46 | ~spl2_48)),
% 0.22/0.49    inference(subsumption_resolution,[],[f30,f1182])).
% 0.22/0.49  fof(f1182,plain,(
% 0.22/0.49    ( ! [X8,X7] : (k5_xboole_0(X8,k4_xboole_0(X7,X8)) = k2_xboole_0(X8,X7)) ) | (~spl2_5 | ~spl2_8 | ~spl2_46 | ~spl2_48)),
% 0.22/0.49    inference(forward_demodulation,[],[f1181,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl2_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.49  fof(f1181,plain,(
% 0.22/0.49    ( ! [X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k5_xboole_0(X8,k4_xboole_0(X7,X8))) ) | (~spl2_5 | ~spl2_46 | ~spl2_48)),
% 0.22/0.49    inference(forward_demodulation,[],[f1154,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    spl2_5 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f1154,plain,(
% 0.22/0.49    ( ! [X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X7,X8),k1_xboole_0))) ) | (~spl2_46 | ~spl2_48)),
% 0.22/0.49    inference(superposition,[],[f1147,f1077])).
% 0.22/0.49  fof(f1077,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)) ) | ~spl2_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f1076])).
% 0.22/0.49  fof(f1076,plain,(
% 0.22/0.49    spl2_46 <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.22/0.49  fof(f1147,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))) ) | ~spl2_48),
% 0.22/0.49    inference(avatar_component_clause,[],[f1146])).
% 0.22/0.49  fof(f1146,plain,(
% 0.22/0.49    spl2_48 <=> ! [X3,X4] : k2_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    spl2_1 <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f1148,plain,(
% 0.22/0.49    spl2_48 | ~spl2_11 | ~spl2_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f256,f241,f77,f1146])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl2_11 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    spl2_23 <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))) ) | (~spl2_11 | ~spl2_23)),
% 0.22/0.49    inference(superposition,[],[f242,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))) ) | ~spl2_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f241])).
% 0.22/0.49  fof(f1078,plain,(
% 0.22/0.49    spl2_46 | ~spl2_8 | ~spl2_10 | ~spl2_13 | ~spl2_28 | ~spl2_33),
% 0.22/0.49    inference(avatar_split_clause,[],[f543,f501,f360,f127,f73,f61,f1076])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl2_10 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl2_13 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    spl2_28 <=> ! [X3,X2,X4] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.49  fof(f501,plain,(
% 0.22/0.49    spl2_33 <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.49  fof(f543,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)) ) | (~spl2_8 | ~spl2_10 | ~spl2_13 | ~spl2_28 | ~spl2_33)),
% 0.22/0.49    inference(forward_demodulation,[],[f542,f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl2_8 | ~spl2_10 | ~spl2_13)),
% 0.22/0.49    inference(forward_demodulation,[],[f130,f62])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) ) | (~spl2_10 | ~spl2_13)),
% 0.22/0.49    inference(superposition,[],[f128,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f127])).
% 0.22/0.49  fof(f542,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X1))) ) | (~spl2_8 | ~spl2_28 | ~spl2_33)),
% 0.22/0.49    inference(forward_demodulation,[],[f514,f62])).
% 0.22/0.49  fof(f514,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | (~spl2_28 | ~spl2_33)),
% 0.22/0.49    inference(superposition,[],[f502,f361])).
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) ) | ~spl2_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f360])).
% 0.22/0.49  fof(f502,plain,(
% 0.22/0.49    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))) ) | ~spl2_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f501])).
% 0.22/0.49  fof(f503,plain,(
% 0.22/0.49    spl2_33 | ~spl2_7 | ~spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f106,f73,f57,f501])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))) ) | (~spl2_7 | ~spl2_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f99,f74])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7)))) ) | (~spl2_7 | ~spl2_10)),
% 0.22/0.49    inference(superposition,[],[f74,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f362,plain,(
% 0.22/0.49    spl2_28 | ~spl2_8 | ~spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f101,f73,f61,f360])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) ) | (~spl2_8 | ~spl2_10)),
% 0.22/0.49    inference(superposition,[],[f62,f74])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    spl2_23 | ~spl2_6 | ~spl2_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f88,f69,f49,f241])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))) ) | (~spl2_6 | ~spl2_9)),
% 0.22/0.49    inference(superposition,[],[f70,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl2_13 | ~spl2_2 | ~spl2_4 | ~spl2_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f66,f57,f41,f33,f127])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    spl2_2 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    spl2_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_2 | ~spl2_4 | ~spl2_7)),
% 0.22/0.49    inference(forward_demodulation,[],[f64,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f33])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl2_4 | ~spl2_7)),
% 0.22/0.49    inference(superposition,[],[f58,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f41])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl2_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f77])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f73])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl2_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f69])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl2_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f61])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl2_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f57])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f49])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    spl2_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f45])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f41])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f17,f33])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f28])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (4316)------------------------------
% 0.22/0.49  % (4316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (4316)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (4316)Memory used [KB]: 7164
% 0.22/0.49  % (4316)Time elapsed: 0.031 s
% 0.22/0.49  % (4316)------------------------------
% 0.22/0.49  % (4316)------------------------------
% 0.22/0.49  % (4310)Success in time 0.13 s
%------------------------------------------------------------------------------
