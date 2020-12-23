%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 291 expanded)
%              Number of leaves         :   41 ( 146 expanded)
%              Depth                    :    9
%              Number of atoms          :  371 ( 644 expanded)
%              Number of equality atoms :  102 ( 215 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f53,f57,f67,f77,f81,f90,f99,f107,f111,f115,f124,f133,f177,f200,f289,f746,f750,f896,f900,f904,f1072,f1189,f1210,f1348,f1553,f2993,f3123])).

fof(f3123,plain,
    ( ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_20
    | ~ spl2_23
    | spl2_59
    | ~ spl2_79 ),
    inference(avatar_contradiction_clause,[],[f3122])).

fof(f3122,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_20
    | ~ spl2_23
    | spl2_59
    | ~ spl2_79 ),
    inference(subsumption_resolution,[],[f3121,f40])).

fof(f40,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_1
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3121,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_20
    | ~ spl2_23
    | spl2_59
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f3120,f199])).

fof(f199,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X6,k2_xboole_0(X4,X5)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl2_20
  <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X6,k2_xboole_0(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f3120,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_23
    | spl2_59
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f3118,f106])).

fof(f106,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f3118,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_23
    | spl2_59
    | ~ spl2_79 ),
    inference(backward_demodulation,[],[f2062,f3117])).

fof(f3117,plain,
    ( ! [X23,X21,X22] : k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X21,X22)),k2_xboole_0(X22,X21)) = k4_xboole_0(X23,k2_xboole_0(X22,X21))
    | ~ spl2_1
    | ~ spl2_23
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f3077,f40])).

fof(f3077,plain,
    ( ! [X23,X21,X22] : k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X21,X22)),k2_xboole_0(X22,X21)) = k2_xboole_0(k4_xboole_0(X23,k2_xboole_0(X22,X21)),k1_xboole_0)
    | ~ spl2_23
    | ~ spl2_79 ),
    inference(superposition,[],[f288,f2992])).

fof(f2992,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))
    | ~ spl2_79 ),
    inference(avatar_component_clause,[],[f2991])).

fof(f2991,plain,
    ( spl2_79
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f288,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f2062,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | ~ spl2_7
    | spl2_59 ),
    inference(superposition,[],[f1552,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f1552,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_59 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f1550,plain,
    ( spl2_59
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f2993,plain,
    ( spl2_79
    | ~ spl2_11
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f1360,f1346,f97,f2991])).

fof(f97,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1346,plain,
    ( spl2_49
  <=> ! [X65,X64] : r1_tarski(k4_xboole_0(X65,X64),k2_xboole_0(X64,X65)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f1360,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))
    | ~ spl2_11
    | ~ spl2_49 ),
    inference(resolution,[],[f1347,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1347,plain,
    ( ! [X64,X65] : r1_tarski(k4_xboole_0(X65,X64),k2_xboole_0(X64,X65))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f1346])).

fof(f1553,plain,
    ( ~ spl2_59
    | ~ spl2_12
    | ~ spl2_16
    | ~ spl2_39
    | spl2_47 ),
    inference(avatar_split_clause,[],[f1504,f1207,f902,f131,f105,f1550])).

fof(f131,plain,
    ( spl2_16
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f902,plain,
    ( spl2_39
  <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f1207,plain,
    ( spl2_47
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f1504,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_12
    | ~ spl2_16
    | ~ spl2_39
    | spl2_47 ),
    inference(forward_demodulation,[],[f1503,f132])).

fof(f132,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1503,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | ~ spl2_12
    | ~ spl2_39
    | spl2_47 ),
    inference(backward_demodulation,[],[f1209,f1477])).

fof(f1477,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(X6,X7) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(k4_xboole_0(X5,X6),X7))
    | ~ spl2_12
    | ~ spl2_39 ),
    inference(superposition,[],[f106,f903])).

fof(f903,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f902])).

fof(f1209,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_47 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1348,plain,
    ( spl2_49
    | ~ spl2_35
    | ~ spl2_38
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1263,f1187,f898,f744,f1346])).

fof(f744,plain,
    ( spl2_35
  <=> ! [X1,X0] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f898,plain,
    ( spl2_38
  <=> ! [X5,X6] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f1187,plain,
    ( spl2_42
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1263,plain,
    ( ! [X64,X65] : r1_tarski(k4_xboole_0(X65,X64),k2_xboole_0(X64,X65))
    | ~ spl2_35
    | ~ spl2_38
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f1235,f745])).

fof(f745,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f744])).

fof(f1235,plain,
    ( ! [X64,X65] : r1_tarski(k4_xboole_0(k2_xboole_0(X64,X65),X64),k2_xboole_0(X64,X65))
    | ~ spl2_38
    | ~ spl2_42 ),
    inference(superposition,[],[f1188,f899])).

fof(f899,plain,
    ( ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f898])).

fof(f1188,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f1187])).

fof(f1210,plain,(
    ~ spl2_47 ),
    inference(avatar_split_clause,[],[f34,f1207])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f21,f29,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f1189,plain,
    ( spl2_42
    | ~ spl2_16
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f1104,f1070,f131,f1187])).

fof(f1070,plain,
    ( spl2_40
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f1104,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)
    | ~ spl2_16
    | ~ spl2_40 ),
    inference(superposition,[],[f1071,f132])).

fof(f1071,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1072,plain,
    ( spl2_40
    | ~ spl2_37
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f1024,f898,f894,f1070])).

fof(f894,plain,
    ( spl2_37
  <=> ! [X18,X17,X19] : r1_tarski(k4_xboole_0(X19,X18),k4_xboole_0(k2_xboole_0(X17,X19),X18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1024,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)
    | ~ spl2_37
    | ~ spl2_38 ),
    inference(superposition,[],[f895,f899])).

fof(f895,plain,
    ( ! [X19,X17,X18] : r1_tarski(k4_xboole_0(X19,X18),k4_xboole_0(k2_xboole_0(X17,X19),X18))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f894])).

fof(f904,plain,
    ( spl2_39
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f886,f748,f131,f122,f43,f902])).

fof(f43,plain,
    ( spl2_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f122,plain,
    ( spl2_15
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f748,plain,
    ( spl2_36
  <=> ! [X1,X0] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f886,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f885,f44])).

fof(f44,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f885,plain,
    ( ! [X6,X7] : k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f870,f123])).

fof(f123,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f870,plain,
    ( ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))
    | ~ spl2_16
    | ~ spl2_36 ),
    inference(superposition,[],[f132,f749])).

fof(f749,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0)
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f748])).

fof(f900,plain,
    ( spl2_38
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f856,f744,f131,f113,f43,f898])).

fof(f113,plain,
    ( spl2_14
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f856,plain,
    ( ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f855,f44])).

fof(f855,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f839,f114])).

fof(f114,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f839,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(superposition,[],[f132,f745])).

fof(f896,plain,
    ( spl2_37
    | ~ spl2_9
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f670,f287,f79,f894])).

fof(f79,plain,
    ( spl2_9
  <=> ! [X3,X2] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f670,plain,
    ( ! [X19,X17,X18] : r1_tarski(k4_xboole_0(X19,X18),k4_xboole_0(k2_xboole_0(X17,X19),X18))
    | ~ spl2_9
    | ~ spl2_23 ),
    inference(superposition,[],[f80,f288])).

fof(f80,plain,
    ( ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f750,plain,
    ( spl2_36
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f711,f287,f55,f39,f748])).

fof(f55,plain,
    ( spl2_5
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f711,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f638,f40])).

fof(f638,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(superposition,[],[f288,f56])).

fof(f56,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f746,plain,
    ( spl2_35
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f683,f287,f75,f55,f744])).

fof(f75,plain,
    ( spl2_8
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f683,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f615,f76])).

fof(f76,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f615,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(superposition,[],[f288,f56])).

fof(f289,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f33,f287])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f200,plain,
    ( spl2_20
    | ~ spl2_7
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f185,f175,f65,f198])).

fof(f175,plain,
    ( spl2_18
  <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f185,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X6,k2_xboole_0(X4,X5)))
    | ~ spl2_7
    | ~ spl2_18 ),
    inference(superposition,[],[f176,f66])).

fof(f176,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( spl2_18
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f149,f113,f109,f105,f175])).

fof(f109,plain,
    ( spl2_13
  <=> ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f149,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f136,f110])).

fof(f110,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f136,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(superposition,[],[f106,f114])).

fof(f133,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f36,f131])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f124,plain,
    ( spl2_15
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f101,f97,f79,f122])).

fof(f101,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(resolution,[],[f98,f80])).

fof(f115,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f100,f97,f51,f113])).

fof(f51,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f100,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(resolution,[],[f98,f52])).

fof(f52,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f111,plain,
    ( spl2_13
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f103,f97,f88,f109])).

fof(f88,plain,
    ( spl2_10
  <=> ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f103,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(resolution,[],[f98,f89])).

fof(f89,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f107,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f32,f105])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f99,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f31,f97])).

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

fof(f90,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f86,f75,f51,f88])).

% (24943)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f86,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f52,f76])).

fof(f81,plain,
    ( spl2_9
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f71,f65,f51,f79])).

fof(f71,plain,
    ( ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f52,f66])).

fof(f77,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f68,f65,f39,f75])).

fof(f68,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f66,f40])).

fof(f67,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f57,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f37,f55])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f35,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f29])).

% (24941)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (24936)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (24942)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (24931)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24934)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (24932)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (24939)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (24940)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (24940)Refutation not found, incomplete strategy% (24940)------------------------------
% 0.21/0.48  % (24940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24940)Memory used [KB]: 10490
% 0.21/0.48  % (24940)Time elapsed: 0.070 s
% 0.21/0.48  % (24940)------------------------------
% 0.21/0.48  % (24940)------------------------------
% 0.21/0.49  % (24930)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (24933)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (24937)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (24929)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (24944)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (24945)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (24938)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (24936)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f3150,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f41,f45,f53,f57,f67,f77,f81,f90,f99,f107,f111,f115,f124,f133,f177,f200,f289,f746,f750,f896,f900,f904,f1072,f1189,f1210,f1348,f1553,f2993,f3123])).
% 0.21/0.50  fof(f3123,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_20 | ~spl2_23 | spl2_59 | ~spl2_79),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f3122])).
% 0.21/0.50  fof(f3122,plain,(
% 0.21/0.50    $false | (~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_20 | ~spl2_23 | spl2_59 | ~spl2_79)),
% 0.21/0.50    inference(subsumption_resolution,[],[f3121,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl2_1 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f3121,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_20 | ~spl2_23 | spl2_59 | ~spl2_79)),
% 0.21/0.50    inference(forward_demodulation,[],[f3120,f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X6,k2_xboole_0(X4,X5)))) ) | ~spl2_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f198])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl2_20 <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X6,k2_xboole_0(X4,X5)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.50  fof(f3120,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) | (~spl2_1 | ~spl2_7 | ~spl2_12 | ~spl2_23 | spl2_59 | ~spl2_79)),
% 0.21/0.50    inference(forward_demodulation,[],[f3118,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl2_12 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.50  fof(f3118,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))) | (~spl2_1 | ~spl2_7 | ~spl2_23 | spl2_59 | ~spl2_79)),
% 0.21/0.50    inference(backward_demodulation,[],[f2062,f3117])).
% 0.21/0.50  fof(f3117,plain,(
% 0.21/0.50    ( ! [X23,X21,X22] : (k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X21,X22)),k2_xboole_0(X22,X21)) = k4_xboole_0(X23,k2_xboole_0(X22,X21))) ) | (~spl2_1 | ~spl2_23 | ~spl2_79)),
% 0.21/0.50    inference(forward_demodulation,[],[f3077,f40])).
% 0.21/0.50  fof(f3077,plain,(
% 0.21/0.50    ( ! [X23,X21,X22] : (k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X21,X22)),k2_xboole_0(X22,X21)) = k2_xboole_0(k4_xboole_0(X23,k2_xboole_0(X22,X21)),k1_xboole_0)) ) | (~spl2_23 | ~spl2_79)),
% 0.21/0.50    inference(superposition,[],[f288,f2992])).
% 0.21/0.50  fof(f2992,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ) | ~spl2_79),
% 0.21/0.50    inference(avatar_component_clause,[],[f2991])).
% 0.21/0.50  fof(f2991,plain,(
% 0.21/0.50    spl2_79 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl2_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f287])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    spl2_23 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.50  fof(f2062,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | (~spl2_7 | spl2_59)),
% 0.21/0.50    inference(superposition,[],[f1552,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl2_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.50  fof(f1552,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_59),
% 0.21/0.50    inference(avatar_component_clause,[],[f1550])).
% 0.21/0.50  fof(f1550,plain,(
% 0.21/0.50    spl2_59 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.21/0.50  fof(f2993,plain,(
% 0.21/0.50    spl2_79 | ~spl2_11 | ~spl2_49),
% 0.21/0.50    inference(avatar_split_clause,[],[f1360,f1346,f97,f2991])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl2_11 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.50  fof(f1346,plain,(
% 0.21/0.50    spl2_49 <=> ! [X65,X64] : r1_tarski(k4_xboole_0(X65,X64),k2_xboole_0(X64,X65))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.50  fof(f1360,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ) | (~spl2_11 | ~spl2_49)),
% 0.21/0.50    inference(resolution,[],[f1347,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f1347,plain,(
% 0.21/0.50    ( ! [X64,X65] : (r1_tarski(k4_xboole_0(X65,X64),k2_xboole_0(X64,X65))) ) | ~spl2_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f1346])).
% 0.21/0.50  fof(f1553,plain,(
% 0.21/0.50    ~spl2_59 | ~spl2_12 | ~spl2_16 | ~spl2_39 | spl2_47),
% 0.21/0.50    inference(avatar_split_clause,[],[f1504,f1207,f902,f131,f105,f1550])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl2_16 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.50  fof(f902,plain,(
% 0.21/0.50    spl2_39 <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.50  fof(f1207,plain,(
% 0.21/0.50    spl2_47 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.21/0.50  fof(f1504,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_12 | ~spl2_16 | ~spl2_39 | spl2_47)),
% 0.21/0.50    inference(forward_demodulation,[],[f1503,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f1503,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | (~spl2_12 | ~spl2_39 | spl2_47)),
% 0.21/0.51    inference(backward_demodulation,[],[f1209,f1477])).
% 0.21/0.51  fof(f1477,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (k4_xboole_0(X6,X7) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(k4_xboole_0(X5,X6),X7))) ) | (~spl2_12 | ~spl2_39)),
% 0.21/0.51    inference(superposition,[],[f106,f903])).
% 0.21/0.51  fof(f903,plain,(
% 0.21/0.51    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) ) | ~spl2_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f902])).
% 0.21/0.51  fof(f1209,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f1207])).
% 0.21/0.51  fof(f1348,plain,(
% 0.21/0.51    spl2_49 | ~spl2_35 | ~spl2_38 | ~spl2_42),
% 0.21/0.51    inference(avatar_split_clause,[],[f1263,f1187,f898,f744,f1346])).
% 0.21/0.51  fof(f744,plain,(
% 0.21/0.51    spl2_35 <=> ! [X1,X0] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.51  fof(f898,plain,(
% 0.21/0.51    spl2_38 <=> ! [X5,X6] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.51  fof(f1187,plain,(
% 0.21/0.51    spl2_42 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.51  fof(f1263,plain,(
% 0.21/0.51    ( ! [X64,X65] : (r1_tarski(k4_xboole_0(X65,X64),k2_xboole_0(X64,X65))) ) | (~spl2_35 | ~spl2_38 | ~spl2_42)),
% 0.21/0.51    inference(forward_demodulation,[],[f1235,f745])).
% 0.21/0.51  fof(f745,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) ) | ~spl2_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f744])).
% 0.21/0.51  fof(f1235,plain,(
% 0.21/0.51    ( ! [X64,X65] : (r1_tarski(k4_xboole_0(k2_xboole_0(X64,X65),X64),k2_xboole_0(X64,X65))) ) | (~spl2_38 | ~spl2_42)),
% 0.21/0.51    inference(superposition,[],[f1188,f899])).
% 0.21/0.51  fof(f899,plain,(
% 0.21/0.51    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5) ) | ~spl2_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f898])).
% 0.21/0.51  fof(f1188,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ) | ~spl2_42),
% 0.21/0.51    inference(avatar_component_clause,[],[f1187])).
% 0.21/0.51  fof(f1210,plain,(
% 0.21/0.51    ~spl2_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f1207])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f29,f30,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.51  fof(f1189,plain,(
% 0.21/0.51    spl2_42 | ~spl2_16 | ~spl2_40),
% 0.21/0.51    inference(avatar_split_clause,[],[f1104,f1070,f131,f1187])).
% 0.21/0.51  fof(f1070,plain,(
% 0.21/0.51    spl2_40 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.51  fof(f1104,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ) | (~spl2_16 | ~spl2_40)),
% 0.21/0.51    inference(superposition,[],[f1071,f132])).
% 0.21/0.51  fof(f1071,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ) | ~spl2_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f1070])).
% 0.21/0.51  fof(f1072,plain,(
% 0.21/0.51    spl2_40 | ~spl2_37 | ~spl2_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f1024,f898,f894,f1070])).
% 0.21/0.51  fof(f894,plain,(
% 0.21/0.51    spl2_37 <=> ! [X18,X17,X19] : r1_tarski(k4_xboole_0(X19,X18),k4_xboole_0(k2_xboole_0(X17,X19),X18))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.51  fof(f1024,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ) | (~spl2_37 | ~spl2_38)),
% 0.21/0.51    inference(superposition,[],[f895,f899])).
% 0.21/0.51  fof(f895,plain,(
% 0.21/0.51    ( ! [X19,X17,X18] : (r1_tarski(k4_xboole_0(X19,X18),k4_xboole_0(k2_xboole_0(X17,X19),X18))) ) | ~spl2_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f894])).
% 0.21/0.51  fof(f904,plain,(
% 0.21/0.51    spl2_39 | ~spl2_2 | ~spl2_15 | ~spl2_16 | ~spl2_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f886,f748,f131,f122,f43,f902])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl2_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl2_15 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.51  fof(f748,plain,(
% 0.21/0.51    spl2_36 <=> ! [X1,X0] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.51  fof(f886,plain,(
% 0.21/0.51    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) ) | (~spl2_2 | ~spl2_15 | ~spl2_16 | ~spl2_36)),
% 0.21/0.51    inference(forward_demodulation,[],[f885,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f885,plain,(
% 0.21/0.51    ( ! [X6,X7] : (k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) ) | (~spl2_15 | ~spl2_16 | ~spl2_36)),
% 0.21/0.51    inference(forward_demodulation,[],[f870,f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | ~spl2_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f870,plain,(
% 0.21/0.51    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) ) | (~spl2_16 | ~spl2_36)),
% 0.21/0.51    inference(superposition,[],[f132,f749])).
% 0.21/0.51  fof(f749,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0)) ) | ~spl2_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f748])).
% 0.21/0.51  fof(f900,plain,(
% 0.21/0.51    spl2_38 | ~spl2_2 | ~spl2_14 | ~spl2_16 | ~spl2_35),
% 0.21/0.51    inference(avatar_split_clause,[],[f856,f744,f131,f113,f43,f898])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl2_14 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.51  fof(f856,plain,(
% 0.21/0.51    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5) ) | (~spl2_2 | ~spl2_14 | ~spl2_16 | ~spl2_35)),
% 0.21/0.51    inference(forward_demodulation,[],[f855,f44])).
% 0.21/0.51  fof(f855,plain,(
% 0.21/0.51    ( ! [X6,X5] : (k4_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) ) | (~spl2_14 | ~spl2_16 | ~spl2_35)),
% 0.21/0.51    inference(forward_demodulation,[],[f839,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f839,plain,(
% 0.21/0.51    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) ) | (~spl2_16 | ~spl2_35)),
% 0.21/0.51    inference(superposition,[],[f132,f745])).
% 0.21/0.51  fof(f896,plain,(
% 0.21/0.51    spl2_37 | ~spl2_9 | ~spl2_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f670,f287,f79,f894])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl2_9 <=> ! [X3,X2] : r1_tarski(X2,k2_xboole_0(X3,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f670,plain,(
% 0.21/0.51    ( ! [X19,X17,X18] : (r1_tarski(k4_xboole_0(X19,X18),k4_xboole_0(k2_xboole_0(X17,X19),X18))) ) | (~spl2_9 | ~spl2_23)),
% 0.21/0.51    inference(superposition,[],[f80,f288])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) ) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f79])).
% 0.21/0.51  fof(f750,plain,(
% 0.21/0.51    spl2_36 | ~spl2_1 | ~spl2_5 | ~spl2_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f711,f287,f55,f39,f748])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl2_5 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f711,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0)) ) | (~spl2_1 | ~spl2_5 | ~spl2_23)),
% 0.21/0.51    inference(forward_demodulation,[],[f638,f40])).
% 0.21/0.51  fof(f638,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)) ) | (~spl2_5 | ~spl2_23)),
% 0.21/0.51    inference(superposition,[],[f288,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f55])).
% 0.21/0.51  fof(f746,plain,(
% 0.21/0.51    spl2_35 | ~spl2_5 | ~spl2_8 | ~spl2_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f683,f287,f75,f55,f744])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl2_8 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f683,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) ) | (~spl2_5 | ~spl2_8 | ~spl2_23)),
% 0.21/0.51    inference(forward_demodulation,[],[f615,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f615,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) ) | (~spl2_5 | ~spl2_23)),
% 0.21/0.51    inference(superposition,[],[f288,f56])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    spl2_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f287])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl2_20 | ~spl2_7 | ~spl2_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f185,f175,f65,f198])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl2_18 <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X6,k2_xboole_0(X4,X5)))) ) | (~spl2_7 | ~spl2_18)),
% 0.21/0.51    inference(superposition,[],[f176,f66])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))) ) | ~spl2_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f175])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl2_18 | ~spl2_12 | ~spl2_13 | ~spl2_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f149,f113,f109,f105,f175])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl2_13 <=> ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))) ) | (~spl2_12 | ~spl2_13 | ~spl2_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f136,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) ) | ~spl2_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))) ) | (~spl2_12 | ~spl2_14)),
% 0.21/0.51    inference(superposition,[],[f106,f114])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl2_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f131])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f29,f29])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl2_15 | ~spl2_9 | ~spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f101,f97,f79,f122])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | (~spl2_9 | ~spl2_11)),
% 0.21/0.51    inference(resolution,[],[f98,f80])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl2_14 | ~spl2_4 | ~spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f100,f97,f51,f113])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl2_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_11)),
% 0.21/0.51    inference(resolution,[],[f98,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl2_13 | ~spl2_10 | ~spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f97,f88,f109])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl2_10 <=> ! [X2] : r1_tarski(k1_xboole_0,X2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) ) | (~spl2_10 | ~spl2_11)),
% 0.21/0.51    inference(resolution,[],[f98,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl2_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl2_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f105])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f97])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl2_10 | ~spl2_4 | ~spl2_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f86,f75,f51,f88])).
% 0.21/0.51  % (24943)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | (~spl2_4 | ~spl2_8)),
% 0.21/0.51    inference(superposition,[],[f52,f76])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl2_9 | ~spl2_4 | ~spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f71,f65,f51,f79])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) ) | (~spl2_4 | ~spl2_7)),
% 0.21/0.51    inference(superposition,[],[f52,f66])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl2_8 | ~spl2_1 | ~spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f65,f39,f75])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_1 | ~spl2_7)),
% 0.21/0.51    inference(superposition,[],[f66,f40])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f65])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f55])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f35,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f29])).
% 0.21/0.51  % (24941)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f43])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f39])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24936)------------------------------
% 0.21/0.51  % (24936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24936)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (24936)Memory used [KB]: 8443
% 0.21/0.51  % (24936)Time elapsed: 0.107 s
% 0.21/0.51  % (24936)------------------------------
% 0.21/0.51  % (24936)------------------------------
% 0.21/0.51  % (24928)Success in time 0.153 s
%------------------------------------------------------------------------------
