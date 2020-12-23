%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 157 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 ( 332 expanded)
%              Number of equality atoms :   72 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f51,f60,f68,f76,f97,f101,f122,f140,f174,f222,f270,f274,f493,f612,f1180])).

fof(f1180,plain,
    ( ~ spl2_7
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(avatar_contradiction_clause,[],[f1179])).

fof(f1179,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f1178,f67])).

fof(f67,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_7
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f1178,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f1177,f221])).

fof(f221,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl2_19
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f1177,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(backward_demodulation,[],[f582,f1176])).

fof(f1176,plain,
    ( ! [X33,X31,X32] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X31,X32),X33),k2_xboole_0(X31,X32)) = k4_xboole_0(X33,k2_xboole_0(X31,X32))
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f1112,f67])).

fof(f1112,plain,
    ( ! [X33,X31,X32] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X31,X32),X33),k2_xboole_0(X31,X32)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X33,k2_xboole_0(X31,X32)))
    | ~ spl2_17
    | ~ spl2_36 ),
    inference(superposition,[],[f611,f173])).

fof(f173,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl2_17
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f611,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl2_36
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f582,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f581,f273])).

fof(f273,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl2_22
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f581,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | ~ spl2_21
    | ~ spl2_29 ),
    inference(backward_demodulation,[],[f34,f564])).

fof(f564,plain,
    ( ! [X17,X18,X16] : k4_xboole_0(X17,X18) = k4_xboole_0(k2_xboole_0(X16,X17),k2_xboole_0(k4_xboole_0(X16,X17),X18))
    | ~ spl2_21
    | ~ spl2_29 ),
    inference(superposition,[],[f269,f492])).

fof(f492,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl2_29
  <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f269,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f21,f28,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f612,plain,(
    spl2_36 ),
    inference(avatar_split_clause,[],[f33,f610])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f493,plain,
    ( spl2_29
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f355,f272,f268,f99,f95,f41,f491])).

fof(f41,plain,
    ( spl2_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f95,plain,
    ( spl2_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f99,plain,
    ( spl2_13
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f355,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f354,f42])).

fof(f42,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f354,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0)
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f312,f284])).

fof(f284,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl2_13
    | ~ spl2_21 ),
    inference(superposition,[],[f269,f100])).

fof(f100,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f312,plain,
    ( ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(superposition,[],[f273,f96])).

fof(f96,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f274,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f35,f272])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f270,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f32,f268])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f222,plain,
    ( spl2_19
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f141,f138,f74,f220])).

fof(f74,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f138,plain,
    ( spl2_15
  <=> ! [X3,X2] : r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f141,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(resolution,[],[f139,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f139,plain,
    ( ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X3,X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f174,plain,
    ( spl2_17
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f114,f99,f95,f172])).

fof(f114,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(superposition,[],[f100,f96])).

fof(f140,plain,
    ( spl2_15
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f131,f120,f58,f138])).

fof(f58,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f120,plain,
    ( spl2_14
  <=> ! [X3,X4] : r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f131,plain,
    ( ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X3,X2))
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f121,f59])).

fof(f59,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f121,plain,
    ( ! [X4,X3] : r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X3,X4))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f115,f95,f49,f120])).

fof(f49,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f115,plain,
    ( ! [X4,X3] : r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X3,X4))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f50,f96])).

fof(f50,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f101,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f77,f74,f49,f99])).

fof(f77,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f75,f50])).

fof(f97,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f29,f95])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f76,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f68,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f61,f58,f37,f66])).

fof(f37,plain,
    ( spl2_1
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f61,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f59,f38])).

fof(f38,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f43,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (5128)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.43  % (5136)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.43  % (5136)Refutation not found, incomplete strategy% (5136)------------------------------
% 0.20/0.43  % (5136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (5136)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (5136)Memory used [KB]: 10490
% 0.20/0.43  % (5136)Time elapsed: 0.045 s
% 0.20/0.43  % (5136)------------------------------
% 0.20/0.43  % (5136)------------------------------
% 0.20/0.44  % (5139)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.44  % (5134)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.45  % (5138)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (5140)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (5137)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (5132)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (5130)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (5142)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (5127)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (5131)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (5125)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (5126)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (5141)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (5129)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (5135)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (5133)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (5132)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f1217,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f39,f43,f51,f60,f68,f76,f97,f101,f122,f140,f174,f222,f270,f274,f493,f612,f1180])).
% 0.20/0.50  fof(f1180,plain,(
% 0.20/0.50    ~spl2_7 | ~spl2_17 | ~spl2_19 | ~spl2_21 | ~spl2_22 | ~spl2_29 | ~spl2_36),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1179])).
% 0.20/0.50  fof(f1179,plain,(
% 0.20/0.50    $false | (~spl2_7 | ~spl2_17 | ~spl2_19 | ~spl2_21 | ~spl2_22 | ~spl2_29 | ~spl2_36)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1178,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl2_7 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.50  fof(f1178,plain,(
% 0.20/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_7 | ~spl2_17 | ~spl2_19 | ~spl2_21 | ~spl2_22 | ~spl2_29 | ~spl2_36)),
% 0.20/0.50    inference(forward_demodulation,[],[f1177,f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ) | ~spl2_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f220])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    spl2_19 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.50  fof(f1177,plain,(
% 0.20/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_7 | ~spl2_17 | ~spl2_21 | ~spl2_22 | ~spl2_29 | ~spl2_36)),
% 0.20/0.50    inference(backward_demodulation,[],[f582,f1176])).
% 0.20/0.50  fof(f1176,plain,(
% 0.20/0.50    ( ! [X33,X31,X32] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X31,X32),X33),k2_xboole_0(X31,X32)) = k4_xboole_0(X33,k2_xboole_0(X31,X32))) ) | (~spl2_7 | ~spl2_17 | ~spl2_36)),
% 0.20/0.50    inference(forward_demodulation,[],[f1112,f67])).
% 0.20/0.50  fof(f1112,plain,(
% 0.20/0.50    ( ! [X33,X31,X32] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X31,X32),X33),k2_xboole_0(X31,X32)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X33,k2_xboole_0(X31,X32)))) ) | (~spl2_17 | ~spl2_36)),
% 0.20/0.50    inference(superposition,[],[f611,f173])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ) | ~spl2_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f172])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    spl2_17 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.50  fof(f611,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl2_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f610])).
% 0.20/0.50  fof(f610,plain,(
% 0.20/0.50    spl2_36 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.20/0.50  fof(f582,plain,(
% 0.20/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_21 | ~spl2_22 | ~spl2_29)),
% 0.20/0.50    inference(forward_demodulation,[],[f581,f273])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f272])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    spl2_22 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.50  fof(f581,plain,(
% 0.20/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | (~spl2_21 | ~spl2_29)),
% 0.20/0.50    inference(backward_demodulation,[],[f34,f564])).
% 0.20/0.50  fof(f564,plain,(
% 0.20/0.50    ( ! [X17,X18,X16] : (k4_xboole_0(X17,X18) = k4_xboole_0(k2_xboole_0(X16,X17),k2_xboole_0(k4_xboole_0(X16,X17),X18))) ) | (~spl2_21 | ~spl2_29)),
% 0.20/0.50    inference(superposition,[],[f269,f492])).
% 0.20/0.50  fof(f492,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) ) | ~spl2_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f491])).
% 0.20/0.50  fof(f491,plain,(
% 0.20/0.50    spl2_29 <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f268])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    spl2_21 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.20/0.50    inference(definition_unfolding,[],[f21,f28,f30,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f13])).
% 0.20/0.50  fof(f13,conjecture,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.50  fof(f612,plain,(
% 0.20/0.50    spl2_36),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f610])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.20/0.50  fof(f493,plain,(
% 0.20/0.50    spl2_29 | ~spl2_2 | ~spl2_12 | ~spl2_13 | ~spl2_21 | ~spl2_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f355,f272,f268,f99,f95,f41,f491])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    spl2_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    spl2_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl2_13 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) ) | (~spl2_2 | ~spl2_12 | ~spl2_13 | ~spl2_21 | ~spl2_22)),
% 0.20/0.50    inference(forward_demodulation,[],[f354,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f41])).
% 0.20/0.50  fof(f354,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0)) ) | (~spl2_12 | ~spl2_13 | ~spl2_21 | ~spl2_22)),
% 0.20/0.50    inference(forward_demodulation,[],[f312,f284])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) ) | (~spl2_13 | ~spl2_21)),
% 0.20/0.50    inference(superposition,[],[f269,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl2_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f99])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) ) | (~spl2_12 | ~spl2_22)),
% 0.20/0.50    inference(superposition,[],[f273,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl2_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f95])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    spl2_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f35,f272])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f26,f28,f28])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    spl2_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f268])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    spl2_19 | ~spl2_8 | ~spl2_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f141,f138,f74,f220])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl2_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    spl2_15 <=> ! [X3,X2] : r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X3,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ) | (~spl2_8 | ~spl2_15)),
% 0.20/0.50    inference(resolution,[],[f139,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X3,X2))) ) | ~spl2_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f138])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    spl2_17 | ~spl2_12 | ~spl2_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f114,f99,f95,f172])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ) | (~spl2_12 | ~spl2_13)),
% 0.20/0.50    inference(superposition,[],[f100,f96])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl2_15 | ~spl2_6 | ~spl2_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f131,f120,f58,f138])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    spl2_14 <=> ! [X3,X4] : r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X3,X4))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X3,X2))) ) | (~spl2_6 | ~spl2_14)),
% 0.20/0.50    inference(superposition,[],[f121,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X3,X4))) ) | ~spl2_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f120])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl2_14 | ~spl2_4 | ~spl2_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f115,f95,f49,f120])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    spl2_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X3,X4))) ) | (~spl2_4 | ~spl2_12)),
% 0.20/0.50    inference(superposition,[],[f50,f96])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f49])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl2_13 | ~spl2_4 | ~spl2_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f77,f74,f49,f99])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.50    inference(resolution,[],[f75,f50])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl2_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f95])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl2_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f74])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f61,f58,f37,f66])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    spl2_1 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_1 | ~spl2_6)),
% 0.20/0.50    inference(superposition,[],[f59,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f37])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl2_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f58])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    spl2_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f25,f49])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f23,f41])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f22,f37])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (5132)------------------------------
% 0.20/0.50  % (5132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5132)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (5132)Memory used [KB]: 7036
% 0.20/0.50  % (5132)Time elapsed: 0.038 s
% 0.20/0.50  % (5132)------------------------------
% 0.20/0.50  % (5132)------------------------------
% 0.20/0.51  % (5124)Success in time 0.151 s
%------------------------------------------------------------------------------
