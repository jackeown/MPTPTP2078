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
% DateTime   : Thu Dec  3 12:31:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 212 expanded)
%              Number of leaves         :   32 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  247 ( 406 expanded)
%              Number of equality atoms :   83 ( 169 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f84,f88,f92,f101,f107,f125,f129,f133,f510,f518,f537,f571,f613,f644,f1692,f1765])).

fof(f1765,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_8
    | ~ spl3_9
    | ~ spl3_69 ),
    inference(avatar_contradiction_clause,[],[f1764])).

fof(f1764,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_8
    | ~ spl3_9
    | ~ spl3_69 ),
    inference(subsumption_resolution,[],[f1763,f51])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_3
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1763,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl3_4
    | spl3_8
    | ~ spl3_9
    | ~ spl3_69 ),
    inference(backward_demodulation,[],[f94,f1733])).

fof(f1733,plain,
    ( ! [X6,X5] : k4_xboole_0(sK0,X6) = k4_xboole_0(sK0,k2_xboole_0(X6,k4_xboole_0(sK1,X5)))
    | ~ spl3_4
    | ~ spl3_69 ),
    inference(superposition,[],[f1691,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1691,plain,
    ( ! [X2,X1] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,X1),X2))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f1690])).

fof(f1690,plain,
    ( spl3_69
  <=> ! [X1,X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f94,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))
    | spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f93,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f93,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_8
    | ~ spl3_9 ),
    inference(resolution,[],[f87,f83])).

fof(f83,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_8
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1692,plain,
    ( spl3_69
    | ~ spl3_12
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f654,f642,f105,f1690])).

fof(f105,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f642,plain,
    ( spl3_43
  <=> ! [X13] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f654,plain,
    ( ! [X2,X1] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,X1),X2))
    | ~ spl3_12
    | ~ spl3_43 ),
    inference(superposition,[],[f106,f643])).

fof(f643,plain,
    ( ! [X13] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X13))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f642])).

fof(f106,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f644,plain,
    ( spl3_43
    | ~ spl3_37
    | ~ spl3_39
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f640,f611,f535,f507,f642])).

fof(f507,plain,
    ( spl3_37
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f535,plain,
    ( spl3_39
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f611,plain,
    ( spl3_42
  <=> ! [X7,X6] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f640,plain,
    ( ! [X13] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X13))
    | ~ spl3_37
    | ~ spl3_39
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f637,f509])).

fof(f509,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f507])).

fof(f637,plain,
    ( ! [X13] : k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,X13))
    | ~ spl3_39
    | ~ spl3_42 ),
    inference(superposition,[],[f536,f612])).

fof(f612,plain,
    ( ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f611])).

fof(f536,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f535])).

fof(f613,plain,
    ( spl3_42
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f606,f569,f127,f123,f611])).

fof(f123,plain,
    ( spl3_15
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f127,plain,
    ( spl3_16
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f569,plain,
    ( spl3_41
  <=> ! [X13,X14] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f606,plain,
    ( ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f576,f465])).

fof(f465,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(superposition,[],[f128,f124])).

fof(f124,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f128,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f576,plain,
    ( ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X7,X6))),X6) = X6
    | ~ spl3_15
    | ~ spl3_41 ),
    inference(superposition,[],[f570,f124])).

fof(f570,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f569])).

fof(f571,plain,
    ( spl3_41
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f503,f131,f127,f58,f569])).

fof(f58,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f131,plain,
    ( spl3_17
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f503,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f474,f132])).

fof(f132,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f474,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,X14))
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(superposition,[],[f59,f128])).

fof(f59,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f537,plain,
    ( spl3_39
    | ~ spl3_4
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f519,f516,f54,f535])).

fof(f516,plain,
    ( spl3_38
  <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f519,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))
    | ~ spl3_4
    | ~ spl3_38 ),
    inference(superposition,[],[f517,f55])).

fof(f517,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f516])).

fof(f518,plain,
    ( spl3_38
    | ~ spl3_12
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f513,f507,f105,f516])).

fof(f513,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_12
    | ~ spl3_37 ),
    inference(superposition,[],[f106,f509])).

fof(f510,plain,
    ( spl3_37
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f489,f127,f98,f46,f507])).

fof(f46,plain,
    ( spl3_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f489,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f469,f47])).

fof(f47,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f469,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(superposition,[],[f128,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f133,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f34,f131])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f129,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f33,f127])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f125,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f32,f123])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f107,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f29,f105])).

fof(f101,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f95,f90,f41,f98])).

fof(f41,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f95,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f91,f43])).

fof(f43,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f88,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f35,f86])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f38,f32])).

fof(f38,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f30,f32])).

fof(f30,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f18,f24,f24])).

fof(f18,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f60,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f50])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f31,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f44,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (10104)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (10107)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (10109)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (10118)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (10110)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (10102)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (10114)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (10108)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (10115)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (10120)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (10113)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (10117)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (10112)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (10111)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (10116)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (10119)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (10103)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (10106)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.55  % (10110)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1775,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f84,f88,f92,f101,f107,f125,f129,f133,f510,f518,f537,f571,f613,f644,f1692,f1765])).
% 0.21/0.58  fof(f1765,plain,(
% 0.21/0.58    ~spl3_3 | ~spl3_4 | spl3_8 | ~spl3_9 | ~spl3_69),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1764])).
% 0.21/0.58  fof(f1764,plain,(
% 0.21/0.58    $false | (~spl3_3 | ~spl3_4 | spl3_8 | ~spl3_9 | ~spl3_69)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1763,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    spl3_3 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.58  fof(f1763,plain,(
% 0.21/0.58    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl3_4 | spl3_8 | ~spl3_9 | ~spl3_69)),
% 0.21/0.58    inference(backward_demodulation,[],[f94,f1733])).
% 0.21/0.58  fof(f1733,plain,(
% 0.21/0.58    ( ! [X6,X5] : (k4_xboole_0(sK0,X6) = k4_xboole_0(sK0,k2_xboole_0(X6,k4_xboole_0(sK1,X5)))) ) | (~spl3_4 | ~spl3_69)),
% 0.21/0.58    inference(superposition,[],[f1691,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    spl3_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.58  fof(f1691,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,X1),X2))) ) | ~spl3_69),
% 0.21/0.58    inference(avatar_component_clause,[],[f1690])).
% 0.21/0.58  fof(f1690,plain,(
% 0.21/0.58    spl3_69 <=> ! [X1,X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,X1),X2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) | (spl3_8 | ~spl3_9)),
% 0.21/0.58    inference(forward_demodulation,[],[f93,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (spl3_8 | ~spl3_9)),
% 0.21/0.58    inference(resolution,[],[f87,f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_8),
% 0.21/0.58    inference(avatar_component_clause,[],[f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    spl3_8 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f86])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    spl3_9 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.58  fof(f1692,plain,(
% 0.21/0.58    spl3_69 | ~spl3_12 | ~spl3_43),
% 0.21/0.58    inference(avatar_split_clause,[],[f654,f642,f105,f1690])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    spl3_12 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.58  fof(f642,plain,(
% 0.21/0.58    spl3_43 <=> ! [X13] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X13))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.58  fof(f654,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,X1),X2))) ) | (~spl3_12 | ~spl3_43)),
% 0.21/0.58    inference(superposition,[],[f106,f643])).
% 0.21/0.58  fof(f643,plain,(
% 0.21/0.58    ( ! [X13] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) ) | ~spl3_43),
% 0.21/0.58    inference(avatar_component_clause,[],[f642])).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f105])).
% 0.21/0.58  fof(f644,plain,(
% 0.21/0.58    spl3_43 | ~spl3_37 | ~spl3_39 | ~spl3_42),
% 0.21/0.58    inference(avatar_split_clause,[],[f640,f611,f535,f507,f642])).
% 0.21/0.58  fof(f507,plain,(
% 0.21/0.58    spl3_37 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.58  fof(f535,plain,(
% 0.21/0.58    spl3_39 <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.58  fof(f611,plain,(
% 0.21/0.58    spl3_42 <=> ! [X7,X6] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.58  fof(f640,plain,(
% 0.21/0.58    ( ! [X13] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) ) | (~spl3_37 | ~spl3_39 | ~spl3_42)),
% 0.21/0.58    inference(forward_demodulation,[],[f637,f509])).
% 0.21/0.58  fof(f509,plain,(
% 0.21/0.58    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_37),
% 0.21/0.58    inference(avatar_component_clause,[],[f507])).
% 0.21/0.58  fof(f637,plain,(
% 0.21/0.58    ( ! [X13] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) ) | (~spl3_39 | ~spl3_42)),
% 0.21/0.58    inference(superposition,[],[f536,f612])).
% 0.21/0.58  fof(f612,plain,(
% 0.21/0.58    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6) ) | ~spl3_42),
% 0.21/0.58    inference(avatar_component_clause,[],[f611])).
% 0.21/0.58  fof(f536,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))) ) | ~spl3_39),
% 0.21/0.58    inference(avatar_component_clause,[],[f535])).
% 0.21/0.58  fof(f613,plain,(
% 0.21/0.58    spl3_42 | ~spl3_15 | ~spl3_16 | ~spl3_41),
% 0.21/0.58    inference(avatar_split_clause,[],[f606,f569,f127,f123,f611])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    spl3_15 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    spl3_16 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.58  fof(f569,plain,(
% 0.21/0.58    spl3_41 <=> ! [X13,X14] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.58  fof(f606,plain,(
% 0.21/0.58    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6) ) | (~spl3_15 | ~spl3_16 | ~spl3_41)),
% 0.21/0.58    inference(forward_demodulation,[],[f576,f465])).
% 0.21/0.58  fof(f465,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl3_15 | ~spl3_16)),
% 0.21/0.58    inference(superposition,[],[f128,f124])).
% 0.21/0.58  fof(f124,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f123])).
% 0.21/0.58  fof(f128,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_16),
% 0.21/0.58    inference(avatar_component_clause,[],[f127])).
% 0.21/0.58  fof(f576,plain,(
% 0.21/0.58    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X7,X6))),X6) = X6) ) | (~spl3_15 | ~spl3_41)),
% 0.21/0.58    inference(superposition,[],[f570,f124])).
% 0.21/0.58  fof(f570,plain,(
% 0.21/0.58    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13) ) | ~spl3_41),
% 0.21/0.58    inference(avatar_component_clause,[],[f569])).
% 0.21/0.58  fof(f571,plain,(
% 0.21/0.58    spl3_41 | ~spl3_5 | ~spl3_16 | ~spl3_17),
% 0.21/0.58    inference(avatar_split_clause,[],[f503,f131,f127,f58,f569])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    spl3_17 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.58  fof(f503,plain,(
% 0.21/0.58    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13) ) | (~spl3_5 | ~spl3_16 | ~spl3_17)),
% 0.21/0.58    inference(forward_demodulation,[],[f474,f132])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_17),
% 0.21/0.58    inference(avatar_component_clause,[],[f131])).
% 0.21/0.58  fof(f474,plain,(
% 0.21/0.58    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,X14))) ) | (~spl3_5 | ~spl3_16)),
% 0.21/0.58    inference(superposition,[],[f59,f128])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f58])).
% 0.21/0.58  fof(f537,plain,(
% 0.21/0.58    spl3_39 | ~spl3_4 | ~spl3_38),
% 0.21/0.58    inference(avatar_split_clause,[],[f519,f516,f54,f535])).
% 0.21/0.58  fof(f516,plain,(
% 0.21/0.58    spl3_38 <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.58  fof(f519,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))) ) | (~spl3_4 | ~spl3_38)),
% 0.21/0.58    inference(superposition,[],[f517,f55])).
% 0.21/0.58  fof(f517,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_38),
% 0.21/0.58    inference(avatar_component_clause,[],[f516])).
% 0.21/0.58  fof(f518,plain,(
% 0.21/0.58    spl3_38 | ~spl3_12 | ~spl3_37),
% 0.21/0.58    inference(avatar_split_clause,[],[f513,f507,f105,f516])).
% 0.21/0.58  fof(f513,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | (~spl3_12 | ~spl3_37)),
% 0.21/0.58    inference(superposition,[],[f106,f509])).
% 0.21/0.58  fof(f510,plain,(
% 0.21/0.58    spl3_37 | ~spl3_2 | ~spl3_11 | ~spl3_16),
% 0.21/0.58    inference(avatar_split_clause,[],[f489,f127,f98,f46,f507])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    spl3_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.58  fof(f489,plain,(
% 0.21/0.58    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_11 | ~spl3_16)),
% 0.21/0.58    inference(forward_demodulation,[],[f469,f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f46])).
% 0.21/0.58  fof(f469,plain,(
% 0.21/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_11 | ~spl3_16)),
% 0.21/0.58    inference(superposition,[],[f128,f100])).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f98])).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    spl3_17),
% 0.21/0.58    inference(avatar_split_clause,[],[f34,f131])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f26,f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    spl3_16),
% 0.21/0.58    inference(avatar_split_clause,[],[f33,f127])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f25,f24])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.58  fof(f125,plain,(
% 0.21/0.58    spl3_15),
% 0.21/0.58    inference(avatar_split_clause,[],[f32,f123])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f22,f24,f24])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    spl3_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f29,f105])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    spl3_11 | ~spl3_1 | ~spl3_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f95,f90,f41,f98])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    spl3_10 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_10)),
% 0.21/0.58    inference(resolution,[],[f91,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f41])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f90])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    spl3_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f36,f90])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f27,f24])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.58    inference(nnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    spl3_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f35,f86])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f28,f24])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    ~spl3_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f39,f81])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.58    inference(forward_demodulation,[],[f38,f32])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.58    inference(backward_demodulation,[],[f30,f32])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 0.21/0.58    inference(definition_unfolding,[],[f18,f24,f24])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.58    inference(negated_conjecture,[],[f11])).
% 0.21/0.58  fof(f11,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    spl3_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    spl3_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f21,f54])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    spl3_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f37,f50])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.58    inference(backward_demodulation,[],[f31,f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f19,f24])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    spl3_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    spl3_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f17,f41])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    r1_xboole_0(sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (10110)------------------------------
% 0.21/0.58  % (10110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (10110)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (10110)Memory used [KB]: 7419
% 0.21/0.58  % (10110)Time elapsed: 0.095 s
% 0.21/0.58  % (10110)------------------------------
% 0.21/0.58  % (10110)------------------------------
% 0.21/0.58  % (10098)Success in time 0.222 s
%------------------------------------------------------------------------------
