%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:12 EST 2020

% Result     : Theorem 2.99s
% Output     : Refutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 170 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  212 ( 331 expanded)
%              Number of equality atoms :   63 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8461,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f80,f84,f94,f136,f149,f776,f915,f919,f1329,f1580,f1737,f1757,f1880,f5279,f7115,f7442,f8305])).

fof(f8305,plain,
    ( ~ spl3_52
    | ~ spl3_72
    | spl3_76
    | ~ spl3_119
    | ~ spl3_139
    | ~ spl3_144 ),
    inference(avatar_contradiction_clause,[],[f8303])).

fof(f8303,plain,
    ( $false
    | ~ spl3_52
    | ~ spl3_72
    | spl3_76
    | ~ spl3_119
    | ~ spl3_139
    | ~ spl3_144 ),
    inference(subsumption_resolution,[],[f1879,f8302])).

fof(f8302,plain,
    ( ! [X57,X58,X56] : k2_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,k4_xboole_0(X56,X58))) = k4_xboole_0(X56,k4_xboole_0(X57,X58))
    | ~ spl3_52
    | ~ spl3_72
    | ~ spl3_119
    | ~ spl3_139
    | ~ spl3_144 ),
    inference(forward_demodulation,[],[f8301,f6112])).

fof(f6112,plain,
    ( ! [X8,X7,X9] : k4_xboole_0(X7,k4_xboole_0(X8,X9)) = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)))
    | ~ spl3_72
    | ~ spl3_119 ),
    inference(forward_demodulation,[],[f5955,f1756])).

fof(f1756,plain,
    ( ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X8),X9) = X9
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f1755,plain,
    ( spl3_72
  <=> ! [X9,X8] : k2_xboole_0(k4_xboole_0(X8,X8),X9) = X9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f5955,plain,
    ( ! [X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X8,X9))) = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)))
    | ~ spl3_119 ),
    inference(superposition,[],[f5278,f5278])).

fof(f5278,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))
    | ~ spl3_119 ),
    inference(avatar_component_clause,[],[f5277])).

fof(f5277,plain,
    ( spl3_119
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_119])])).

fof(f8301,plain,
    ( ! [X57,X58,X56] : k4_xboole_0(X56,k4_xboole_0(X56,k2_xboole_0(k4_xboole_0(X56,X57),X58))) = k2_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,k4_xboole_0(X56,X58)))
    | ~ spl3_52
    | ~ spl3_139
    | ~ spl3_144 ),
    inference(forward_demodulation,[],[f8101,f7441])).

fof(f7441,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ~ spl3_144 ),
    inference(avatar_component_clause,[],[f7440])).

fof(f7440,plain,
    ( spl3_144
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_144])])).

fof(f8101,plain,
    ( ! [X57,X58,X56] : k4_xboole_0(X56,k4_xboole_0(X56,k2_xboole_0(k4_xboole_0(X56,X57),X58))) = k2_xboole_0(k4_xboole_0(X56,k4_xboole_0(X57,k4_xboole_0(X57,X56))),k4_xboole_0(X56,k4_xboole_0(X56,X58)))
    | ~ spl3_52
    | ~ spl3_139 ),
    inference(superposition,[],[f7114,f914])).

fof(f914,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f913])).

fof(f913,plain,
    ( spl3_52
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f7114,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_139 ),
    inference(avatar_component_clause,[],[f7113])).

fof(f7113,plain,
    ( spl3_139
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).

fof(f1879,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl3_76 ),
    inference(avatar_component_clause,[],[f1877])).

fof(f1877,plain,
    ( spl3_76
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f7442,plain,
    ( spl3_144
    | ~ spl3_52
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f1429,f917,f913,f7440])).

fof(f917,plain,
    ( spl3_53
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f1429,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ~ spl3_52
    | ~ spl3_53 ),
    inference(superposition,[],[f918,f914])).

fof(f918,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f917])).

fof(f7115,plain,(
    spl3_139 ),
    inference(avatar_split_clause,[],[f58,f7113])).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f45,f39,f39,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f5279,plain,(
    spl3_119 ),
    inference(avatar_split_clause,[],[f59,f5277])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f57,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f43,f39,f39])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1880,plain,(
    ~ spl3_76 ),
    inference(avatar_split_clause,[],[f52,f1877])).

fof(f52,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1757,plain,
    ( spl3_72
    | ~ spl3_5
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f1742,f1735,f78,f1755])).

fof(f78,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1735,plain,
    ( spl3_71
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f1742,plain,
    ( ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X8),X9) = X9
    | ~ spl3_5
    | ~ spl3_71 ),
    inference(resolution,[],[f1736,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f1736,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1)
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f1737,plain,
    ( spl3_71
    | ~ spl3_8
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f1719,f1578,f92,f1735])).

fof(f92,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1578,plain,
    ( spl3_70
  <=> ! [X16,X18,X17] : r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)),X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f1719,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1)
    | ~ spl3_8
    | ~ spl3_70 ),
    inference(superposition,[],[f1579,f93])).

fof(f93,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1579,plain,
    ( ! [X17,X18,X16] : r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)),X17)
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f1578])).

fof(f1580,plain,
    ( spl3_70
    | ~ spl3_14
    | ~ spl3_44
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f1409,f1327,f774,f147,f1578])).

fof(f147,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] : r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f774,plain,
    ( spl3_44
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1327,plain,
    ( spl3_63
  <=> ! [X13,X14] : k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13) = X13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f1409,plain,
    ( ! [X17,X18,X16] : r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)),X17)
    | ~ spl3_14
    | ~ spl3_44
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f1355,f775])).

fof(f775,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f774])).

fof(f1355,plain,
    ( ! [X17,X18,X16] : r1_tarski(k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),X18),X17)
    | ~ spl3_14
    | ~ spl3_63 ),
    inference(superposition,[],[f148,f1328])).

fof(f1328,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13) = X13
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f1327])).

fof(f148,plain,
    ( ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1329,plain,
    ( spl3_63
    | ~ spl3_8
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f1224,f913,f92,f1327])).

fof(f1224,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13) = X13
    | ~ spl3_8
    | ~ spl3_52 ),
    inference(superposition,[],[f93,f914])).

fof(f919,plain,(
    spl3_53 ),
    inference(avatar_split_clause,[],[f55,f917])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f915,plain,(
    spl3_52 ),
    inference(avatar_split_clause,[],[f54,f913])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f39,f39])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f776,plain,(
    spl3_44 ),
    inference(avatar_split_clause,[],[f44,f774])).

fof(f149,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f140,f134,f65,f147])).

fof(f65,plain,
    ( spl3_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f134,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] : r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f140,plain,
    ( ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0))
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(superposition,[],[f135,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f135,plain,
    ( ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f105,f82,f61,f134])).

fof(f61,plain,
    ( spl3_1
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f105,plain,
    ( ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X0,k2_xboole_0(X2,X1)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f94,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f85,f78,f61,f92])).

fof(f85,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f79,f62])).

fof(f84,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f82])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f63,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 19:59:49 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.11/0.32  % (1440)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.11/0.33  % (1439)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.11/0.33  % (1441)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.11/0.33  % (1455)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.11/0.34  % (1442)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.11/0.34  % (1453)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.11/0.34  % (1445)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.11/0.34  % (1449)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.11/0.35  % (1451)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.11/0.35  % (1452)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.11/0.35  % (1446)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.11/0.35  % (1454)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.11/0.35  % (1443)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.11/0.36  % (1448)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.11/0.36  % (1456)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.11/0.36  % (1444)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.11/0.37  % (1447)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.11/0.38  % (1450)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.11/0.39  % (1450)Refutation not found, incomplete strategy% (1450)------------------------------
% 0.11/0.39  % (1450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (1450)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.39  
% 0.11/0.39  % (1450)Memory used [KB]: 10618
% 0.11/0.39  % (1450)Time elapsed: 0.068 s
% 0.11/0.39  % (1450)------------------------------
% 0.11/0.39  % (1450)------------------------------
% 2.99/0.68  % (1446)Refutation found. Thanks to Tanya!
% 2.99/0.68  % SZS status Theorem for theBenchmark
% 2.99/0.68  % SZS output start Proof for theBenchmark
% 2.99/0.68  fof(f8461,plain,(
% 2.99/0.68    $false),
% 2.99/0.68    inference(avatar_sat_refutation,[],[f63,f67,f80,f84,f94,f136,f149,f776,f915,f919,f1329,f1580,f1737,f1757,f1880,f5279,f7115,f7442,f8305])).
% 2.99/0.68  fof(f8305,plain,(
% 2.99/0.68    ~spl3_52 | ~spl3_72 | spl3_76 | ~spl3_119 | ~spl3_139 | ~spl3_144),
% 2.99/0.68    inference(avatar_contradiction_clause,[],[f8303])).
% 2.99/0.68  fof(f8303,plain,(
% 2.99/0.68    $false | (~spl3_52 | ~spl3_72 | spl3_76 | ~spl3_119 | ~spl3_139 | ~spl3_144)),
% 2.99/0.68    inference(subsumption_resolution,[],[f1879,f8302])).
% 2.99/0.68  fof(f8302,plain,(
% 2.99/0.68    ( ! [X57,X58,X56] : (k2_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,k4_xboole_0(X56,X58))) = k4_xboole_0(X56,k4_xboole_0(X57,X58))) ) | (~spl3_52 | ~spl3_72 | ~spl3_119 | ~spl3_139 | ~spl3_144)),
% 2.99/0.68    inference(forward_demodulation,[],[f8301,f6112])).
% 2.99/0.68  fof(f6112,plain,(
% 2.99/0.68    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k4_xboole_0(X8,X9)) = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)))) ) | (~spl3_72 | ~spl3_119)),
% 2.99/0.68    inference(forward_demodulation,[],[f5955,f1756])).
% 2.99/0.68  fof(f1756,plain,(
% 2.99/0.68    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X8),X9) = X9) ) | ~spl3_72),
% 2.99/0.68    inference(avatar_component_clause,[],[f1755])).
% 2.99/0.68  fof(f1755,plain,(
% 2.99/0.68    spl3_72 <=> ! [X9,X8] : k2_xboole_0(k4_xboole_0(X8,X8),X9) = X9),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 2.99/0.68  fof(f5955,plain,(
% 2.99/0.68    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X8,X9))) = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)))) ) | ~spl3_119),
% 2.99/0.68    inference(superposition,[],[f5278,f5278])).
% 2.99/0.68  fof(f5278,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ) | ~spl3_119),
% 2.99/0.68    inference(avatar_component_clause,[],[f5277])).
% 2.99/0.68  fof(f5277,plain,(
% 2.99/0.68    spl3_119 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_119])])).
% 2.99/0.68  fof(f8301,plain,(
% 2.99/0.68    ( ! [X57,X58,X56] : (k4_xboole_0(X56,k4_xboole_0(X56,k2_xboole_0(k4_xboole_0(X56,X57),X58))) = k2_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,k4_xboole_0(X56,X58)))) ) | (~spl3_52 | ~spl3_139 | ~spl3_144)),
% 2.99/0.68    inference(forward_demodulation,[],[f8101,f7441])).
% 2.99/0.68  fof(f7441,plain,(
% 2.99/0.68    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ) | ~spl3_144),
% 2.99/0.68    inference(avatar_component_clause,[],[f7440])).
% 2.99/0.68  fof(f7440,plain,(
% 2.99/0.68    spl3_144 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_144])])).
% 2.99/0.68  fof(f8101,plain,(
% 2.99/0.68    ( ! [X57,X58,X56] : (k4_xboole_0(X56,k4_xboole_0(X56,k2_xboole_0(k4_xboole_0(X56,X57),X58))) = k2_xboole_0(k4_xboole_0(X56,k4_xboole_0(X57,k4_xboole_0(X57,X56))),k4_xboole_0(X56,k4_xboole_0(X56,X58)))) ) | (~spl3_52 | ~spl3_139)),
% 2.99/0.68    inference(superposition,[],[f7114,f914])).
% 2.99/0.68  fof(f914,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_52),
% 2.99/0.68    inference(avatar_component_clause,[],[f913])).
% 2.99/0.68  fof(f913,plain,(
% 2.99/0.68    spl3_52 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 2.99/0.68  fof(f7114,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_139),
% 2.99/0.68    inference(avatar_component_clause,[],[f7113])).
% 2.99/0.68  fof(f7113,plain,(
% 2.99/0.68    spl3_139 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).
% 2.99/0.68  fof(f1879,plain,(
% 2.99/0.68    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl3_76),
% 2.99/0.68    inference(avatar_component_clause,[],[f1877])).
% 2.99/0.68  fof(f1877,plain,(
% 2.99/0.68    spl3_76 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 2.99/0.68  fof(f7442,plain,(
% 2.99/0.68    spl3_144 | ~spl3_52 | ~spl3_53),
% 2.99/0.68    inference(avatar_split_clause,[],[f1429,f917,f913,f7440])).
% 2.99/0.68  fof(f917,plain,(
% 2.99/0.68    spl3_53 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 2.99/0.68  fof(f1429,plain,(
% 2.99/0.68    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ) | (~spl3_52 | ~spl3_53)),
% 2.99/0.68    inference(superposition,[],[f918,f914])).
% 2.99/0.68  fof(f918,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_53),
% 2.99/0.68    inference(avatar_component_clause,[],[f917])).
% 2.99/0.68  fof(f7115,plain,(
% 2.99/0.68    spl3_139),
% 2.99/0.68    inference(avatar_split_clause,[],[f58,f7113])).
% 2.99/0.68  fof(f58,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.99/0.68    inference(definition_unfolding,[],[f45,f39,f39,f39])).
% 2.99/0.68  fof(f39,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.99/0.68    inference(cnf_transformation,[],[f15])).
% 2.99/0.68  fof(f15,axiom,(
% 2.99/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.99/0.68  fof(f45,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.99/0.68    inference(cnf_transformation,[],[f6])).
% 2.99/0.68  fof(f6,axiom,(
% 2.99/0.68    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 2.99/0.68  fof(f5279,plain,(
% 2.99/0.68    spl3_119),
% 2.99/0.68    inference(avatar_split_clause,[],[f59,f5277])).
% 2.99/0.68  fof(f59,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 2.99/0.68    inference(backward_demodulation,[],[f57,f44])).
% 2.99/0.68  fof(f44,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.99/0.68    inference(cnf_transformation,[],[f11])).
% 2.99/0.68  fof(f11,axiom,(
% 2.99/0.68    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.99/0.68  fof(f57,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.99/0.68    inference(definition_unfolding,[],[f43,f39,f39])).
% 2.99/0.68  fof(f43,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.99/0.68    inference(cnf_transformation,[],[f16])).
% 2.99/0.68  fof(f16,axiom,(
% 2.99/0.68    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.99/0.68  fof(f1880,plain,(
% 2.99/0.68    ~spl3_76),
% 2.99/0.68    inference(avatar_split_clause,[],[f52,f1877])).
% 2.99/0.68  fof(f52,plain,(
% 2.99/0.68    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.99/0.68    inference(definition_unfolding,[],[f34,f39])).
% 2.99/0.68  fof(f34,plain,(
% 2.99/0.68    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 2.99/0.68    inference(cnf_transformation,[],[f33])).
% 2.99/0.68  fof(f33,plain,(
% 2.99/0.68    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 2.99/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f32])).
% 2.99/0.68  fof(f32,plain,(
% 2.99/0.68    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 2.99/0.68    introduced(choice_axiom,[])).
% 2.99/0.68  fof(f21,plain,(
% 2.99/0.68    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.99/0.68    inference(ennf_transformation,[],[f19])).
% 2.99/0.68  fof(f19,negated_conjecture,(
% 2.99/0.68    ~! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.99/0.68    inference(negated_conjecture,[],[f18])).
% 2.99/0.68  fof(f18,conjecture,(
% 2.99/0.68    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.99/0.68  fof(f1757,plain,(
% 2.99/0.68    spl3_72 | ~spl3_5 | ~spl3_71),
% 2.99/0.68    inference(avatar_split_clause,[],[f1742,f1735,f78,f1755])).
% 2.99/0.68  fof(f78,plain,(
% 2.99/0.68    spl3_5 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.99/0.68  fof(f1735,plain,(
% 2.99/0.68    spl3_71 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X0),X1)),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 2.99/0.68  fof(f1742,plain,(
% 2.99/0.68    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X8),X9) = X9) ) | (~spl3_5 | ~spl3_71)),
% 2.99/0.68    inference(resolution,[],[f1736,f79])).
% 2.99/0.68  fof(f79,plain,(
% 2.99/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_5),
% 2.99/0.68    inference(avatar_component_clause,[],[f78])).
% 2.99/0.68  fof(f1736,plain,(
% 2.99/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) ) | ~spl3_71),
% 2.99/0.68    inference(avatar_component_clause,[],[f1735])).
% 2.99/0.68  fof(f1737,plain,(
% 2.99/0.68    spl3_71 | ~spl3_8 | ~spl3_70),
% 2.99/0.68    inference(avatar_split_clause,[],[f1719,f1578,f92,f1735])).
% 2.99/0.68  fof(f92,plain,(
% 2.99/0.68    spl3_8 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.99/0.68  fof(f1578,plain,(
% 2.99/0.68    spl3_70 <=> ! [X16,X18,X17] : r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)),X17)),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 2.99/0.68  fof(f1719,plain,(
% 2.99/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) ) | (~spl3_8 | ~spl3_70)),
% 2.99/0.68    inference(superposition,[],[f1579,f93])).
% 2.99/0.68  fof(f93,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | ~spl3_8),
% 2.99/0.68    inference(avatar_component_clause,[],[f92])).
% 2.99/0.68  fof(f1579,plain,(
% 2.99/0.68    ( ! [X17,X18,X16] : (r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)),X17)) ) | ~spl3_70),
% 2.99/0.68    inference(avatar_component_clause,[],[f1578])).
% 2.99/0.68  fof(f1580,plain,(
% 2.99/0.68    spl3_70 | ~spl3_14 | ~spl3_44 | ~spl3_63),
% 2.99/0.68    inference(avatar_split_clause,[],[f1409,f1327,f774,f147,f1578])).
% 2.99/0.68  fof(f147,plain,(
% 2.99/0.68    spl3_14 <=> ! [X1,X0,X2] : r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.99/0.68  fof(f774,plain,(
% 2.99/0.68    spl3_44 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 2.99/0.68  fof(f1327,plain,(
% 2.99/0.68    spl3_63 <=> ! [X13,X14] : k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13) = X13),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 2.99/0.68  fof(f1409,plain,(
% 2.99/0.68    ( ! [X17,X18,X16] : (r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)),X17)) ) | (~spl3_14 | ~spl3_44 | ~spl3_63)),
% 2.99/0.68    inference(forward_demodulation,[],[f1355,f775])).
% 2.99/0.68  fof(f775,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_44),
% 2.99/0.68    inference(avatar_component_clause,[],[f774])).
% 2.99/0.68  fof(f1355,plain,(
% 2.99/0.68    ( ! [X17,X18,X16] : (r1_tarski(k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),X18),X17)) ) | (~spl3_14 | ~spl3_63)),
% 2.99/0.68    inference(superposition,[],[f148,f1328])).
% 2.99/0.68  fof(f1328,plain,(
% 2.99/0.68    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13) = X13) ) | ~spl3_63),
% 2.99/0.68    inference(avatar_component_clause,[],[f1327])).
% 2.99/0.68  fof(f148,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0))) ) | ~spl3_14),
% 2.99/0.68    inference(avatar_component_clause,[],[f147])).
% 2.99/0.68  fof(f1329,plain,(
% 2.99/0.68    spl3_63 | ~spl3_8 | ~spl3_52),
% 2.99/0.68    inference(avatar_split_clause,[],[f1224,f913,f92,f1327])).
% 2.99/0.68  fof(f1224,plain,(
% 2.99/0.68    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13) = X13) ) | (~spl3_8 | ~spl3_52)),
% 2.99/0.68    inference(superposition,[],[f93,f914])).
% 2.99/0.68  fof(f919,plain,(
% 2.99/0.68    spl3_53),
% 2.99/0.68    inference(avatar_split_clause,[],[f55,f917])).
% 2.99/0.68  fof(f55,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.99/0.68    inference(definition_unfolding,[],[f40,f39])).
% 2.99/0.68  fof(f40,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.99/0.68    inference(cnf_transformation,[],[f14])).
% 2.99/0.68  fof(f14,axiom,(
% 2.99/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.99/0.68  fof(f915,plain,(
% 2.99/0.68    spl3_52),
% 2.99/0.68    inference(avatar_split_clause,[],[f54,f913])).
% 2.99/0.68  fof(f54,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.99/0.68    inference(definition_unfolding,[],[f38,f39,f39])).
% 2.99/0.68  fof(f38,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.99/0.68    inference(cnf_transformation,[],[f2])).
% 2.99/0.68  fof(f2,axiom,(
% 2.99/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.99/0.68  fof(f776,plain,(
% 2.99/0.68    spl3_44),
% 2.99/0.68    inference(avatar_split_clause,[],[f44,f774])).
% 2.99/0.68  fof(f149,plain,(
% 2.99/0.68    spl3_14 | ~spl3_2 | ~spl3_13),
% 2.99/0.68    inference(avatar_split_clause,[],[f140,f134,f65,f147])).
% 2.99/0.68  fof(f65,plain,(
% 2.99/0.68    spl3_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.99/0.68  fof(f134,plain,(
% 2.99/0.68    spl3_13 <=> ! [X1,X0,X2] : r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.99/0.68  fof(f140,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0))) ) | (~spl3_2 | ~spl3_13)),
% 2.99/0.68    inference(superposition,[],[f135,f66])).
% 2.99/0.68  fof(f66,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_2),
% 2.99/0.68    inference(avatar_component_clause,[],[f65])).
% 2.99/0.68  fof(f135,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0))) ) | ~spl3_13),
% 2.99/0.68    inference(avatar_component_clause,[],[f134])).
% 2.99/0.68  fof(f136,plain,(
% 2.99/0.68    spl3_13 | ~spl3_1 | ~spl3_6),
% 2.99/0.68    inference(avatar_split_clause,[],[f105,f82,f61,f134])).
% 2.99/0.68  fof(f61,plain,(
% 2.99/0.68    spl3_1 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.99/0.68  fof(f82,plain,(
% 2.99/0.68    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.99/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.99/0.68  fof(f105,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0))) ) | (~spl3_1 | ~spl3_6)),
% 2.99/0.68    inference(resolution,[],[f83,f62])).
% 2.99/0.68  fof(f62,plain,(
% 2.99/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_1),
% 2.99/0.68    inference(avatar_component_clause,[],[f61])).
% 2.99/0.68  fof(f83,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) ) | ~spl3_6),
% 2.99/0.68    inference(avatar_component_clause,[],[f82])).
% 2.99/0.68  fof(f94,plain,(
% 2.99/0.68    spl3_8 | ~spl3_1 | ~spl3_5),
% 2.99/0.68    inference(avatar_split_clause,[],[f85,f78,f61,f92])).
% 2.99/0.68  fof(f85,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | (~spl3_1 | ~spl3_5)),
% 2.99/0.68    inference(resolution,[],[f79,f62])).
% 2.99/0.68  fof(f84,plain,(
% 2.99/0.68    spl3_6),
% 2.99/0.68    inference(avatar_split_clause,[],[f46,f82])).
% 2.99/0.68  fof(f46,plain,(
% 2.99/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.99/0.68    inference(cnf_transformation,[],[f24])).
% 2.99/0.68  fof(f24,plain,(
% 2.99/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.99/0.68    inference(ennf_transformation,[],[f4])).
% 2.99/0.68  fof(f4,axiom,(
% 2.99/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.99/0.68  fof(f80,plain,(
% 2.99/0.68    spl3_5),
% 2.99/0.68    inference(avatar_split_clause,[],[f41,f78])).
% 2.99/0.68  fof(f41,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.99/0.68    inference(cnf_transformation,[],[f22])).
% 2.99/0.68  fof(f22,plain,(
% 2.99/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.99/0.68    inference(ennf_transformation,[],[f5])).
% 2.99/0.68  fof(f5,axiom,(
% 2.99/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.99/0.68  fof(f67,plain,(
% 2.99/0.68    spl3_2),
% 2.99/0.68    inference(avatar_split_clause,[],[f37,f65])).
% 2.99/0.68  fof(f37,plain,(
% 2.99/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.99/0.68    inference(cnf_transformation,[],[f1])).
% 2.99/0.68  fof(f1,axiom,(
% 2.99/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.99/0.68  fof(f63,plain,(
% 2.99/0.68    spl3_1),
% 2.99/0.68    inference(avatar_split_clause,[],[f36,f61])).
% 2.99/0.68  fof(f36,plain,(
% 2.99/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.99/0.68    inference(cnf_transformation,[],[f10])).
% 2.99/0.68  fof(f10,axiom,(
% 2.99/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.99/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.99/0.68  % SZS output end Proof for theBenchmark
% 2.99/0.68  % (1446)------------------------------
% 2.99/0.68  % (1446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.99/0.68  % (1446)Termination reason: Refutation
% 2.99/0.68  
% 2.99/0.68  % (1446)Memory used [KB]: 12409
% 2.99/0.68  % (1446)Time elapsed: 0.349 s
% 2.99/0.68  % (1446)------------------------------
% 2.99/0.68  % (1446)------------------------------
% 2.99/0.68  % (1438)Success in time 0.405 s
%------------------------------------------------------------------------------
