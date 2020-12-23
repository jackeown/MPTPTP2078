%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 211 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  204 ( 396 expanded)
%              Number of equality atoms :   43 ( 104 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f67,f92,f147,f173,f203,f213,f325,f496,f620,f636,f642,f1211])).

fof(f1211,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f1210,f56,f64])).

fof(f64,plain,
    ( spl3_4
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1210,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f1204,f218])).

fof(f218,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f42,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1204,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK0)
    | ~ spl3_3 ),
    inference(superposition,[],[f1187,f95])).

fof(f1187,plain,
    ( ! [X2] : r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f1141,f218])).

fof(f1141,plain,
    ( ! [X2] : r1_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),k1_xboole_0),sK0)
    | ~ spl3_3 ),
    inference(superposition,[],[f159,f295])).

fof(f295,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
    inference(unit_resulting_resolution,[],[f129,f37])).

fof(f129,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
    inference(unit_resulting_resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f159,plain,
    ( ! [X0] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f128,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f128,plain,
    ( ! [X0] : r1_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f58,f45])).

fof(f58,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f642,plain,(
    spl3_25 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | spl3_25 ),
    inference(unit_resulting_resolution,[],[f43,f635])).

fof(f635,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl3_25
  <=> r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f636,plain,
    ( ~ spl3_25
    | spl3_1
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f621,f617,f47,f633])).

fof(f47,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f617,plain,
    ( spl3_24
  <=> k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f621,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | spl3_1
    | ~ spl3_24 ),
    inference(superposition,[],[f121,f619])).

fof(f619,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f617])).

fof(f121,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f49,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f620,plain,
    ( spl3_24
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f615,f493,f144,f617])).

fof(f144,plain,
    ( spl3_10
  <=> k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f493,plain,
    ( spl3_21
  <=> k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f615,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f614,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f614,plain,
    ( k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f146,f495])).

fof(f495,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f493])).

fof(f146,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f496,plain,
    ( spl3_21
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f491,f209,f153,f493])).

fof(f153,plain,
    ( spl3_11
  <=> k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f209,plain,
    ( spl3_16
  <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f491,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK0)
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f155,f211])).

fof(f211,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f209])).

fof(f155,plain,
    ( k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f325,plain,
    ( spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f313,f88,f153])).

fof(f88,plain,
    ( spl3_6
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f313,plain,
    ( k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0)
    | ~ spl3_6 ),
    inference(superposition,[],[f84,f90])).

fof(f90,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f213,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f206,f193,f209])).

fof(f193,plain,
    ( spl3_14
  <=> r1_xboole_0(k5_xboole_0(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f206,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0)
    | ~ spl3_14 ),
    inference(resolution,[],[f195,f37])).

fof(f195,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK0),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f203,plain,
    ( spl3_14
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f191,f170,f193])).

fof(f170,plain,
    ( spl3_13
  <=> r1_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f191,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK0),sK0)
    | ~ spl3_13 ),
    inference(resolution,[],[f172,f35])).

fof(f172,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK0,sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f170])).

fof(f173,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f163,f88,f56,f170])).

fof(f163,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK0,sK0))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(superposition,[],[f128,f90])).

fof(f147,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f142,f88,f144])).

fof(f142,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f139,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f139,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0))
    | ~ spl3_6 ),
    inference(superposition,[],[f44,f90])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f92,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f85,f56,f88])).

fof(f85,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f36,f58])).

fof(f67,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f60,f51,f64])).

fof(f51,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f53,f35])).

fof(f53,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f41,f56])).

fof(f41,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f25,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f54,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f51,f47])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:58:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (21412)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.44  % (21412)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f1212,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f54,f59,f67,f92,f147,f173,f203,f213,f325,f496,f620,f636,f642,f1211])).
% 0.22/0.44  fof(f1211,plain,(
% 0.22/0.44    spl3_4 | ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f1210,f56,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl3_4 <=> r1_xboole_0(sK2,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f1210,plain,(
% 0.22/0.44    r1_xboole_0(sK2,sK0) | ~spl3_3),
% 0.22/0.44    inference(forward_demodulation,[],[f1204,f218])).
% 0.22/0.44  fof(f218,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(backward_demodulation,[],[f42,f95])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f27,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.22/0.44    inference(definition_unfolding,[],[f28,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.44  fof(f1204,plain,(
% 0.22/0.44    r1_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK0) | ~spl3_3),
% 0.22/0.44    inference(superposition,[],[f1187,f95])).
% 0.22/0.44  fof(f1187,plain,(
% 0.22/0.44    ( ! [X2] : (r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0)) ) | ~spl3_3),
% 0.22/0.44    inference(forward_demodulation,[],[f1141,f218])).
% 0.22/0.44  fof(f1141,plain,(
% 0.22/0.44    ( ! [X2] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),k1_xboole_0),sK0)) ) | ~spl3_3),
% 0.22/0.44    inference(superposition,[],[f159,f295])).
% 0.22/0.44  fof(f295,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0)))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f129,f37])).
% 0.22/0.44  fof(f129,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0)))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f43,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f39,f33])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f31,f33])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.44  fof(f159,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)) ) | ~spl3_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f128,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.44  fof(f128,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) ) | ~spl3_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f58,f45])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f56])).
% 0.22/0.44  fof(f642,plain,(
% 0.22/0.44    spl3_25),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f637])).
% 0.22/0.44  fof(f637,plain,(
% 0.22/0.44    $false | spl3_25),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f43,f635])).
% 0.22/0.44  fof(f635,plain,(
% 0.22/0.44    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) | spl3_25),
% 0.22/0.44    inference(avatar_component_clause,[],[f633])).
% 0.22/0.44  fof(f633,plain,(
% 0.22/0.44    spl3_25 <=> r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.44  fof(f636,plain,(
% 0.22/0.44    ~spl3_25 | spl3_1 | ~spl3_24),
% 0.22/0.44    inference(avatar_split_clause,[],[f621,f617,f47,f633])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f617,plain,(
% 0.22/0.44    spl3_24 <=> k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.44  fof(f621,plain,(
% 0.22/0.44    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) | (spl3_1 | ~spl3_24)),
% 0.22/0.44    inference(superposition,[],[f121,f619])).
% 0.22/0.44  fof(f619,plain,(
% 0.22/0.44    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_24),
% 0.22/0.44    inference(avatar_component_clause,[],[f617])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) ) | spl3_1),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f49,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f47])).
% 0.22/0.44  fof(f620,plain,(
% 0.22/0.44    spl3_24 | ~spl3_10 | ~spl3_21),
% 0.22/0.44    inference(avatar_split_clause,[],[f615,f493,f144,f617])).
% 0.22/0.44  fof(f144,plain,(
% 0.22/0.44    spl3_10 <=> k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f493,plain,(
% 0.22/0.44    spl3_21 <=> k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.44  fof(f615,plain,(
% 0.22/0.44    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl3_10 | ~spl3_21)),
% 0.22/0.44    inference(forward_demodulation,[],[f614,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.44  fof(f614,plain,(
% 0.22/0.44    k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0) | (~spl3_10 | ~spl3_21)),
% 0.22/0.44    inference(forward_demodulation,[],[f146,f495])).
% 0.22/0.44  fof(f495,plain,(
% 0.22/0.44    k1_xboole_0 = k5_xboole_0(sK0,sK0) | ~spl3_21),
% 0.22/0.44    inference(avatar_component_clause,[],[f493])).
% 0.22/0.44  fof(f146,plain,(
% 0.22/0.44    k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f144])).
% 0.22/0.44  fof(f496,plain,(
% 0.22/0.44    spl3_21 | ~spl3_11 | ~spl3_16),
% 0.22/0.44    inference(avatar_split_clause,[],[f491,f209,f153,f493])).
% 0.22/0.44  fof(f153,plain,(
% 0.22/0.44    spl3_11 <=> k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f209,plain,(
% 0.22/0.44    spl3_16 <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.44  fof(f491,plain,(
% 0.22/0.44    k1_xboole_0 = k5_xboole_0(sK0,sK0) | (~spl3_11 | ~spl3_16)),
% 0.22/0.44    inference(forward_demodulation,[],[f155,f211])).
% 0.22/0.44  fof(f211,plain,(
% 0.22/0.44    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) | ~spl3_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f209])).
% 0.22/0.44  fof(f155,plain,(
% 0.22/0.44    k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f153])).
% 0.22/0.44  fof(f325,plain,(
% 0.22/0.44    spl3_11 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f313,f88,f153])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    spl3_6 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f313,plain,(
% 0.22/0.44    k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) | ~spl3_6),
% 0.22/0.44    inference(superposition,[],[f84,f90])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f88])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f43,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.44  fof(f213,plain,(
% 0.22/0.44    spl3_16 | ~spl3_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f206,f193,f209])).
% 0.22/0.44  fof(f193,plain,(
% 0.22/0.44    spl3_14 <=> r1_xboole_0(k5_xboole_0(sK0,sK0),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f206,plain,(
% 0.22/0.44    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) | ~spl3_14),
% 0.22/0.44    inference(resolution,[],[f195,f37])).
% 0.22/0.44  fof(f195,plain,(
% 0.22/0.44    r1_xboole_0(k5_xboole_0(sK0,sK0),sK0) | ~spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f193])).
% 0.22/0.44  fof(f203,plain,(
% 0.22/0.44    spl3_14 | ~spl3_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f191,f170,f193])).
% 0.22/0.44  fof(f170,plain,(
% 0.22/0.44    spl3_13 <=> r1_xboole_0(sK0,k5_xboole_0(sK0,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.44  fof(f191,plain,(
% 0.22/0.44    r1_xboole_0(k5_xboole_0(sK0,sK0),sK0) | ~spl3_13),
% 0.22/0.44    inference(resolution,[],[f172,f35])).
% 0.22/0.44  fof(f172,plain,(
% 0.22/0.44    r1_xboole_0(sK0,k5_xboole_0(sK0,sK0)) | ~spl3_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f170])).
% 0.22/0.44  fof(f173,plain,(
% 0.22/0.44    spl3_13 | ~spl3_3 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f163,f88,f56,f170])).
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    r1_xboole_0(sK0,k5_xboole_0(sK0,sK0)) | (~spl3_3 | ~spl3_6)),
% 0.22/0.44    inference(superposition,[],[f128,f90])).
% 0.22/0.44  fof(f147,plain,(
% 0.22/0.44    spl3_10 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f142,f88,f144])).
% 0.22/0.44  fof(f142,plain,(
% 0.22/0.44    k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_6),
% 0.22/0.44    inference(forward_demodulation,[],[f139,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.44  fof(f139,plain,(
% 0.22/0.44    k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) | ~spl3_6),
% 0.22/0.44    inference(superposition,[],[f44,f90])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f34,f33])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    spl3_6 | ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f85,f56,f88])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.44    inference(resolution,[],[f36,f58])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ~spl3_4 | spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f60,f51,f64])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ~r1_xboole_0(sK2,sK0) | spl3_2),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f53,f35])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f51])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f41,f56])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.44    inference(definition_unfolding,[],[f25,f33])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.44    inference(negated_conjecture,[],[f14])).
% 0.22/0.44  fof(f14,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ~spl3_1 | ~spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f51,f47])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (21412)------------------------------
% 0.22/0.44  % (21412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (21412)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (21412)Memory used [KB]: 6652
% 0.22/0.44  % (21412)Time elapsed: 0.026 s
% 0.22/0.44  % (21412)------------------------------
% 0.22/0.44  % (21412)------------------------------
% 0.22/0.45  % (21405)Success in time 0.083 s
%------------------------------------------------------------------------------
