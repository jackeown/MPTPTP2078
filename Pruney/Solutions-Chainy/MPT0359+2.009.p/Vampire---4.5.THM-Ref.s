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
% DateTime   : Thu Dec  3 12:44:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 276 expanded)
%              Number of leaves         :   38 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 ( 563 expanded)
%              Number of equality atoms :  108 ( 234 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f76,f80,f86,f131,f134,f145,f149,f356,f366,f368,f377,f383,f425,f432,f433,f434,f536,f1062,f1102])).

fof(f1102,plain,
    ( sK0 != k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) != k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | sK1 != k3_xboole_0(sK1,sK0)
    | sK0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1062,plain,
    ( spl3_35
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f1061,f358,f996])).

fof(f996,plain,
    ( spl3_35
  <=> sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f358,plain,
    ( spl3_15
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1061,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1060,f81])).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f61,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1060,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1059,f204])).

fof(f204,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f203,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f203,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5)) ),
    inference(forward_demodulation,[],[f193,f81])).

fof(f193,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X5,k1_xboole_0))) ),
    inference(superposition,[],[f59,f171])).

fof(f171,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f136,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f136,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1059,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1058,f359])).

fof(f359,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f358])).

fof(f1058,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f968,f44])).

fof(f968,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl3_15 ),
    inference(superposition,[],[f63,f359])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f58,f58])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f536,plain,
    ( spl3_31
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f524,f430,f526])).

fof(f526,plain,
    ( spl3_31
  <=> k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f430,plain,
    ( spl3_23
  <=> k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f524,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_23 ),
    inference(superposition,[],[f282,f431])).

fof(f431,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f430])).

fof(f282,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f215,f44])).

fof(f215,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f210,f52])).

fof(f210,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f201,f44])).

fof(f201,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f62,f59])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f434,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | sK0 != sK1
    | k5_xboole_0(sK0,sK1) != k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)
    | k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f433,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | sK0 != sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f432,plain,
    ( spl3_23
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f428,f423,f430])).

fof(f423,plain,
    ( spl3_22
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f428,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl3_22 ),
    inference(resolution,[],[f424,f52])).

fof(f424,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f423])).

fof(f425,plain,
    ( spl3_22
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f421,f371,f143,f423])).

fof(f143,plain,
    ( spl3_10
  <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f371,plain,
    ( spl3_17
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f421,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f403,f372])).

fof(f372,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f371])).

fof(f403,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f104,f144])).

fof(f144,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f104,plain,(
    ! [X2,X1] : r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f62,f44])).

fof(f383,plain,
    ( spl3_19
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f379,f364,f381])).

fof(f381,plain,
    ( spl3_19
  <=> k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f364,plain,
    ( spl3_16
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f379,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f365,f52])).

fof(f365,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f364])).

fof(f377,plain,
    ( spl3_17
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f376,f358,f354,f371])).

fof(f354,plain,
    ( spl3_14
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f376,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f355,f359])).

fof(f355,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f354])).

fof(f368,plain,
    ( spl3_15
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f160,f147,f358])).

fof(f147,plain,
    ( spl3_11
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f160,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f148,f44])).

fof(f148,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f366,plain,
    ( spl3_16
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f162,f147,f364])).

fof(f162,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f104,f148])).

fof(f356,plain,
    ( spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f339,f78,f354])).

fof(f78,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f339,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f64,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f47])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f149,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f141,f129,f147])).

fof(f129,plain,
    ( spl3_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f141,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f52,f130])).

fof(f130,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f145,plain,
    ( spl3_10
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f140,f68,f143])).

fof(f68,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f140,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f52,f74])).

fof(f74,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f134,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f132,f71,f84])).

fof(f84,plain,
    ( spl3_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( spl3_2
  <=> sK1 = k2_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f132,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(forward_demodulation,[],[f72,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f72,plain,
    ( sK1 != k2_subset_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f131,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f120,f78,f129])).

fof(f120,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f119,f79])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f36,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f86,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f71,f84])).

fof(f82,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f75,f38])).

fof(f75,plain,
    ( sK1 = k2_subset_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f80,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f76,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f34,f71,f68])).

fof(f34,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f71,f68])).

fof(f35,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:30:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (5497)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (5513)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (5513)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1103,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f73,f76,f80,f86,f131,f134,f145,f149,f356,f366,f368,f377,f383,f425,f432,f433,f434,f536,f1062,f1102])).
% 0.21/0.51  fof(f1102,plain,(
% 0.21/0.51    sK0 != k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) != k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | sK1 != k3_xboole_0(sK1,sK0) | sK0 = sK1),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f1062,plain,(
% 0.21/0.51    spl3_35 | ~spl3_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f1061,f358,f996])).
% 0.21/0.51  fof(f996,plain,(
% 0.21/0.51    spl3_35 <=> sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    spl3_15 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f1061,plain,(
% 0.21/0.51    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_15),
% 0.21/0.51    inference(forward_demodulation,[],[f1060,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f61,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f39,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f40,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f45,f47])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f1060,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | ~spl3_15),
% 0.21/0.51    inference(forward_demodulation,[],[f1059,f204])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f203,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.51    inference(rectify,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f193,f81])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X5,k1_xboole_0)))) )),
% 0.21/0.51    inference(superposition,[],[f59,f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f136,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f52,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f46,f47,f47])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f1059,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | ~spl3_15),
% 0.21/0.51    inference(forward_demodulation,[],[f1058,f359])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f358])).
% 0.21/0.51  fof(f1058,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) | ~spl3_15),
% 0.21/0.51    inference(forward_demodulation,[],[f968,f44])).
% 0.21/0.51  fof(f968,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl3_15),
% 0.21/0.51    inference(superposition,[],[f63,f359])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f43,f58,f58])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f536,plain,(
% 0.21/0.51    spl3_31 | ~spl3_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f524,f430,f526])).
% 0.21/0.51  fof(f526,plain,(
% 0.21/0.51    spl3_31 <=> k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    spl3_23 <=> k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.51  fof(f524,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_23),
% 0.21/0.51    inference(superposition,[],[f282,f431])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) | ~spl3_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f430])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 0.21/0.51    inference(superposition,[],[f215,f44])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 0.21/0.51    inference(resolution,[],[f210,f52])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 0.21/0.51    inference(superposition,[],[f201,f44])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.51    inference(superposition,[],[f62,f59])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f42,f47])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    sK1 != k3_xboole_0(sK1,sK0) | sK0 != sK1 | k5_xboole_0(sK0,sK1) != k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) | k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    sK1 != k3_xboole_0(sK1,sK0) | k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | sK0 != sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    spl3_23 | ~spl3_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f428,f423,f430])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    spl3_22 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) | ~spl3_22),
% 0.21/0.51    inference(resolution,[],[f424,f52])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) | ~spl3_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f423])).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    spl3_22 | ~spl3_10 | ~spl3_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f421,f371,f143,f423])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl3_10 <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    spl3_17 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) | (~spl3_10 | ~spl3_17)),
% 0.21/0.51    inference(forward_demodulation,[],[f403,f372])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f371])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1) | ~spl3_10),
% 0.21/0.51    inference(superposition,[],[f104,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f143])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)) )),
% 0.21/0.51    inference(superposition,[],[f62,f44])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    spl3_19 | ~spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f379,f364,f381])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    spl3_19 <=> k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    spl3_16 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) | ~spl3_16),
% 0.21/0.51    inference(resolution,[],[f365,f52])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(sK0,sK1),sK0) | ~spl3_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f364])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    spl3_17 | ~spl3_14 | ~spl3_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f376,f358,f354,f371])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    spl3_14 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | (~spl3_14 | ~spl3_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f355,f359])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f354])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    spl3_15 | ~spl3_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f160,f147,f358])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl3_11 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_11),
% 0.21/0.51    inference(superposition,[],[f148,f44])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    spl3_16 | ~spl3_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f162,f147,f364])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(sK0,sK1),sK0) | ~spl3_11),
% 0.21/0.51    inference(superposition,[],[f104,f148])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    spl3_14 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f339,f78,f354])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f64,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f53,f47])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl3_11 | ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f141,f129,f147])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl3_9 <=> r1_tarski(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_9),
% 0.21/0.51    inference(resolution,[],[f52,f130])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl3_10 | ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f140,f68,f143])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 0.21/0.51    inference(resolution,[],[f52,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ~spl3_4 | spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f132,f71,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl3_4 <=> sK0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl3_2 <=> sK1 = k2_subset_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    sK0 != sK1 | spl3_2),
% 0.21/0.51    inference(forward_demodulation,[],[f72,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    sK1 != k2_subset_1(sK0) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl3_9 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f120,f78,f129])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f119,f79])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(global_subsumption,[],[f36,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f48,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.51    inference(rectify,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl3_4 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f82,f71,f84])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    sK0 = sK1 | ~spl3_2),
% 0.21/0.51    inference(forward_demodulation,[],[f75,f38])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    sK1 = k2_subset_1(sK0) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f78])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f17])).
% 0.21/0.51  fof(f17,conjecture,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl3_1 | spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f71,f68])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f71,f68])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5513)------------------------------
% 0.21/0.51  % (5513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5513)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5513)Memory used [KB]: 11257
% 0.21/0.51  % (5513)Time elapsed: 0.096 s
% 0.21/0.51  % (5513)------------------------------
% 0.21/0.51  % (5513)------------------------------
% 0.21/0.51  % (5493)Success in time 0.144 s
%------------------------------------------------------------------------------
