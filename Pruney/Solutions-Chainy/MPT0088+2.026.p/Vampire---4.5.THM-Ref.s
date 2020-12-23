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
% DateTime   : Thu Dec  3 12:31:34 EST 2020

% Result     : Theorem 2.91s
% Output     : Refutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  237 (1058 expanded)
%              Number of leaves         :   48 ( 401 expanded)
%              Depth                    :   13
%              Number of atoms          :  425 (1373 expanded)
%              Number of equality atoms :  184 ( 997 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f41,f48,f144,f179,f661,f678,f963,f989,f994,f1013,f1018,f1214,f1230,f1262,f1315,f1326,f1736,f1774,f1987,f2042,f2105,f2125,f2411,f3031,f3089,f3094,f3144,f3265,f3270,f3275,f3339,f3344,f3597,f5893,f6022,f6069,f6091,f6104])).

fof(f6104,plain,
    ( spl3_4
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f6103])).

fof(f6103,plain,
    ( $false
    | spl3_4
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f6089,f47])).

fof(f47,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f6089,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_38 ),
    inference(superposition,[],[f24,f6068])).

fof(f6068,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),sK2)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f6066])).

fof(f6066,plain,
    ( spl3_38
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f6091,plain,
    ( spl3_4
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f6090])).

fof(f6090,plain,
    ( $false
    | spl3_4
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f6070,f47])).

fof(f6070,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_38 ),
    inference(superposition,[],[f6068,f24])).

fof(f6069,plain,
    ( spl3_38
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f6036,f6019,f6066])).

fof(f6019,plain,
    ( spl3_37
  <=> sK2 = k2_xboole_0(sK2,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f6036,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),sK2)
    | ~ spl3_37 ),
    inference(superposition,[],[f166,f6021])).

fof(f6021,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(sK1,sK0))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f6019])).

fof(f166,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f152,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f152,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f25,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f49,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f6022,plain,
    ( spl3_37
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f5967,f675,f6019])).

fof(f675,plain,
    ( spl3_8
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f5967,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(sK1,sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f5758,f2741])).

fof(f2741,plain,(
    ! [X17,X18] : k3_xboole_0(X17,X18) = k3_xboole_0(k3_xboole_0(X17,X18),X17) ),
    inference(superposition,[],[f201,f2584])).

fof(f2584,plain,(
    ! [X21,X20] : k2_xboole_0(X20,k3_xboole_0(X20,X21)) = X20 ),
    inference(superposition,[],[f2513,f20])).

fof(f2513,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f2437,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f2437,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f155,f166])).

fof(f155,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f21,f25])).

fof(f201,plain,(
    ! [X10,X9] : k3_xboole_0(X9,k2_xboole_0(X10,X9)) = X9 ),
    inference(forward_demodulation,[],[f195,f19])).

fof(f195,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k1_xboole_0) = k3_xboole_0(X9,k2_xboole_0(X10,X9)) ),
    inference(superposition,[],[f20,f166])).

fof(f5758,plain,
    ( ! [X4] : sK2 = k2_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X4,sK0),sK1))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f5739,f18])).

fof(f5739,plain,
    ( ! [X4] : k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X4,sK0),sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f64,f5540])).

fof(f5540,plain,
    ( ! [X116] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X116,sK0),k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f5321,f51])).

fof(f5321,plain,
    ( ! [X116] : k3_xboole_0(k3_xboole_0(X116,sK0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(X116,sK0),k3_xboole_0(X116,sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f65,f677])).

fof(f677,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f675])).

fof(f65,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k3_xboole_0(X5,X6),X7) = k4_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,k4_xboole_0(X6,X7))) ),
    inference(superposition,[],[f20,f24])).

fof(f64,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k3_xboole_0(X2,X3)) = k2_xboole_0(X4,k3_xboole_0(X2,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f21,f24])).

fof(f5893,plain,
    ( spl3_36
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f5728,f675,f5890])).

fof(f5890,plain,
    ( spl3_36
  <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f5728,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f5540,f326])).

fof(f326,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4) ),
    inference(forward_demodulation,[],[f319,f19])).

fof(f319,plain,(
    ! [X4] : k3_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(superposition,[],[f20,f288])).

fof(f288,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3) ),
    inference(superposition,[],[f145,f51])).

fof(f145,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f25,f19])).

fof(f3597,plain,
    ( spl3_35
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f3571,f3341,f3594])).

fof(f3594,plain,
    ( spl3_35
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_xboole_0(sK2,sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f3341,plain,
    ( spl3_34
  <=> sK2 = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f3571,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_xboole_0(sK2,sK0),sK1),sK2)
    | ~ spl3_34 ),
    inference(superposition,[],[f166,f3343])).

fof(f3343,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f3341])).

fof(f3344,plain,
    ( spl3_34
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f3312,f3267,f3341])).

fof(f3267,plain,
    ( spl3_31
  <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f3312,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1))
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f3299,f18])).

fof(f3299,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1))
    | ~ spl3_31 ),
    inference(superposition,[],[f64,f3269])).

fof(f3269,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f3267])).

fof(f3339,plain,
    ( spl3_33
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f3277,f3262,f3336])).

fof(f3336,plain,
    ( spl3_33
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f3262,plain,
    ( spl3_30
  <=> sK1 = k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f3277,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK0),sK1)
    | ~ spl3_30 ),
    inference(superposition,[],[f166,f3264])).

fof(f3264,plain,
    ( sK1 = k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f3262])).

fof(f3275,plain,
    ( spl3_32
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f3200,f3141,f3272])).

fof(f3272,plain,
    ( spl3_32
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f3141,plain,
    ( spl3_29
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f3200,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f3189,f20])).

fof(f3189,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_29 ),
    inference(superposition,[],[f20,f3143])).

fof(f3143,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f3141])).

fof(f3270,plain,
    ( spl3_31
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f3198,f3141,f3267])).

fof(f3198,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2))
    | ~ spl3_29 ),
    inference(superposition,[],[f2916,f3143])).

fof(f2916,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f2737,f24])).

fof(f2737,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f166,f2584])).

fof(f3265,plain,
    ( spl3_30
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f3174,f3091,f3262])).

fof(f3091,plain,
    ( spl3_28
  <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f3174,plain,
    ( sK1 = k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f3161,f18])).

fof(f3161,plain,
    ( k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_28 ),
    inference(superposition,[],[f64,f3093])).

fof(f3093,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f3091])).

fof(f3144,plain,
    ( spl3_29
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f3047,f3028,f3141])).

fof(f3028,plain,
    ( spl3_26
  <=> k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f3047,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f3046,f19])).

fof(f3046,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f3045,f154])).

fof(f154,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k3_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f58,f25])).

fof(f58,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f24,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f52,f19])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f20,f51])).

fof(f3045,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f3033,f25])).

fof(f3033,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0))
    | ~ spl3_26 ),
    inference(superposition,[],[f50,f3030])).

fof(f3030,plain,
    ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f3028])).

fof(f50,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f20,f20])).

fof(f3094,plain,
    ( spl3_28
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2991,f986,f3091])).

fof(f986,plain,
    ( spl3_10
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f2991,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_10 ),
    inference(superposition,[],[f2916,f988])).

fof(f988,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f986])).

fof(f3089,plain,
    ( spl3_27
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f2987,f991,f3086])).

fof(f3086,plain,
    ( spl3_27
  <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f991,plain,
    ( spl3_11
  <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f2987,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f2916,f993])).

fof(f993,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f991])).

fof(f3031,plain,
    ( spl3_26
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f2982,f675,f3028])).

fof(f2982,plain,
    ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_8 ),
    inference(superposition,[],[f2916,f677])).

fof(f2411,plain,
    ( spl3_25
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f2345,f1984,f2408])).

fof(f2408,plain,
    ( spl3_25
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f1984,plain,
    ( spl3_21
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f2345,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_21 ),
    inference(superposition,[],[f1899,f1986])).

fof(f1986,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f1899,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X12,X13),k2_xboole_0(k1_xboole_0,X13)) ),
    inference(superposition,[],[f1828,f308])).

fof(f308,plain,(
    ! [X14,X13] : k3_xboole_0(X13,k2_xboole_0(k1_xboole_0,X14)) = k3_xboole_0(X13,X14) ),
    inference(forward_demodulation,[],[f300,f20])).

fof(f300,plain,(
    ! [X14,X13] : k3_xboole_0(X13,k2_xboole_0(k1_xboole_0,X14)) = k4_xboole_0(X13,k4_xboole_0(X13,X14)) ),
    inference(superposition,[],[f20,f145])).

fof(f1828,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f166,f1648])).

fof(f1648,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f1647,f18])).

fof(f1647,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1560,f17])).

fof(f1560,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k2_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f64,f51])).

fof(f2125,plain,
    ( spl3_24
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1920,f1010,f2122])).

fof(f2122,plain,
    ( spl3_24
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1010,plain,
    ( spl3_12
  <=> k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1920,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f1828,f1012])).

fof(f1012,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f2105,plain,
    ( spl3_23
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f2046,f1771,f2102])).

fof(f2102,plain,
    ( spl3_23
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1771,plain,
    ( spl3_20
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f2046,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_20 ),
    inference(superposition,[],[f2004,f326])).

fof(f2004,plain,
    ( ! [X13] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X13,k3_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_20 ),
    inference(superposition,[],[f166,f1790])).

fof(f1790,plain,
    ( ! [X1] : sK2 = k2_xboole_0(sK2,k3_xboole_0(X1,k3_xboole_0(sK0,sK1)))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f1789,f18])).

fof(f1789,plain,
    ( ! [X1] : k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(X1,k3_xboole_0(sK0,sK1)))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f1782,f17])).

fof(f1782,plain,
    ( ! [X1] : k2_xboole_0(sK2,k3_xboole_0(X1,k3_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,k3_xboole_0(X1,k1_xboole_0))
    | ~ spl3_20 ),
    inference(superposition,[],[f64,f1773])).

fof(f1773,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f2042,plain,
    ( spl3_22
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f1991,f1771,f2039])).

fof(f2039,plain,
    ( spl3_22
  <=> sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1991,plain,
    ( sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)))
    | ~ spl3_20 ),
    inference(superposition,[],[f1790,f326])).

fof(f1987,plain,
    ( spl3_21
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f1752,f1733,f1984])).

fof(f1733,plain,
    ( spl3_19
  <=> sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f1752,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_19 ),
    inference(superposition,[],[f201,f1735])).

fof(f1735,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f1733])).

fof(f1774,plain,
    ( spl3_20
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f1748,f1733,f1771])).

fof(f1748,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_19 ),
    inference(superposition,[],[f166,f1735])).

fof(f1736,plain,
    ( spl3_19
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f1702,f38,f1733])).

fof(f38,plain,
    ( spl3_3
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1702,plain,
    ( sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f1599,f18])).

fof(f1599,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f64,f40])).

fof(f40,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f1326,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f1162,f675,f38,f1323])).

fof(f1323,plain,
    ( spl3_18
  <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f1162,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f1149,f40])).

fof(f1149,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))
    | ~ spl3_8 ),
    inference(superposition,[],[f958,f519])).

fof(f519,plain,(
    ! [X4] : k2_xboole_0(X4,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X4))) = X4 ),
    inference(forward_demodulation,[],[f512,f18])).

fof(f512,plain,(
    ! [X4] : k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X4))) ),
    inference(superposition,[],[f21,f315])).

fof(f315,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)),X1) ),
    inference(superposition,[],[f288,f145])).

fof(f958,plain,
    ( ! [X5] : k3_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X5)) = k3_xboole_0(sK0,X5)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f953,f20])).

fof(f953,plain,
    ( ! [X5] : k3_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X5)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X5))
    | ~ spl3_8 ),
    inference(superposition,[],[f20,f681])).

fof(f681,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0))
    | ~ spl3_8 ),
    inference(superposition,[],[f25,f677])).

fof(f1315,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f1282,f1259,f1312])).

fof(f1312,plain,
    ( spl3_17
  <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1259,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1282,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)))
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f1279,f19])).

fof(f1279,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)))
    | ~ spl3_16 ),
    inference(superposition,[],[f20,f1261])).

fof(f1261,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f1259])).

fof(f1262,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1215,f1211,f1259])).

fof(f1211,plain,
    ( spl3_14
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1215,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)))
    | ~ spl3_14 ),
    inference(superposition,[],[f1213,f25])).

fof(f1213,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f1230,plain,
    ( spl3_15
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1129,f1010,f1227])).

fof(f1227,plain,
    ( spl3_15
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,k3_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1129,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,k3_xboole_0(sK0,sK1))))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f1123,f24])).

fof(f1123,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f62,f1012])).

fof(f62,plain,(
    ! [X8,X9] : k1_xboole_0 = k3_xboole_0(X8,k4_xboole_0(X9,k3_xboole_0(X8,X9))) ),
    inference(superposition,[],[f24,f51])).

fof(f1214,plain,
    ( spl3_14
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f995,f986,f1211])).

fof(f995,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))
    | ~ spl3_10 ),
    inference(superposition,[],[f186,f988])).

fof(f186,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f166,f21])).

fof(f1018,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f1008,f991,f1015])).

fof(f1015,plain,
    ( spl3_13
  <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1008,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f1007,f51])).

fof(f1007,plain,
    ( k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(superposition,[],[f20,f993])).

fof(f1013,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f1001,f986,f1010])).

fof(f1001,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f999,f20])).

fof(f999,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_10 ),
    inference(superposition,[],[f20,f988])).

fof(f994,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f979,f675,f991])).

fof(f979,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f968,f19])).

fof(f968,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_8 ),
    inference(superposition,[],[f956,f288])).

fof(f956,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f944,f681])).

fof(f944,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_8 ),
    inference(superposition,[],[f681,f21])).

fof(f989,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f964,f675,f986])).

fof(f964,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f956,f20])).

fof(f963,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f955,f675,f960])).

fof(f960,plain,
    ( spl3_9
  <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f955,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f943,f677])).

fof(f943,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))
    | ~ spl3_8 ),
    inference(superposition,[],[f681,f519])).

fof(f678,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f662,f658,f675])).

fof(f658,plain,
    ( spl3_7
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f662,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(superposition,[],[f660,f58])).

fof(f660,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f658])).

fof(f661,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f636,f38,f658])).

fof(f636,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f607,f19])).

fof(f607,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(superposition,[],[f50,f40])).

fof(f179,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f174,f141,f176])).

fof(f176,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f141,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f174,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f173,f19])).

fof(f173,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f20,f143])).

fof(f143,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f136,f38,f141])).

fof(f136,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f130,f40])).

fof(f130,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_3 ),
    inference(superposition,[],[f68,f56])).

fof(f56,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = X3 ),
    inference(forward_demodulation,[],[f55,f18])).

fof(f55,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = k2_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f21,f51])).

fof(f68,plain,
    ( ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,X4)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f59,f25])).

fof(f59,plain,
    ( ! [X4] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X4)) = k4_xboole_0(k1_xboole_0,X4)
    | ~ spl3_3 ),
    inference(superposition,[],[f24,f40])).

fof(f48,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f42,f32,f45])).

fof(f32,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f41,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f27,f38])).

fof(f27,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f30,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f27])).

fof(f15,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (7221)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (7226)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (7222)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (7223)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (7228)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (7217)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (7233)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (7220)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (7216)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (7218)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (7219)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (7231)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (7232)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (7225)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (7224)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.52  % (7227)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.53  % (7229)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.54  % (7230)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 2.91/0.73  % (7216)Refutation found. Thanks to Tanya!
% 2.91/0.73  % SZS status Theorem for theBenchmark
% 2.91/0.73  % SZS output start Proof for theBenchmark
% 2.91/0.73  fof(f6105,plain,(
% 2.91/0.73    $false),
% 2.91/0.73    inference(avatar_sat_refutation,[],[f30,f35,f41,f48,f144,f179,f661,f678,f963,f989,f994,f1013,f1018,f1214,f1230,f1262,f1315,f1326,f1736,f1774,f1987,f2042,f2105,f2125,f2411,f3031,f3089,f3094,f3144,f3265,f3270,f3275,f3339,f3344,f3597,f5893,f6022,f6069,f6091,f6104])).
% 2.91/0.73  fof(f6104,plain,(
% 2.91/0.73    spl3_4 | ~spl3_38),
% 2.91/0.73    inference(avatar_contradiction_clause,[],[f6103])).
% 2.91/0.73  fof(f6103,plain,(
% 2.91/0.73    $false | (spl3_4 | ~spl3_38)),
% 2.91/0.73    inference(subsumption_resolution,[],[f6089,f47])).
% 2.91/0.73  fof(f47,plain,(
% 2.91/0.73    k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_4),
% 2.91/0.73    inference(avatar_component_clause,[],[f45])).
% 2.91/0.73  fof(f45,plain,(
% 2.91/0.73    spl3_4 <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.91/0.73  fof(f6089,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_38),
% 2.91/0.73    inference(superposition,[],[f24,f6068])).
% 2.91/0.73  fof(f6068,plain,(
% 2.91/0.73    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),sK2) | ~spl3_38),
% 2.91/0.73    inference(avatar_component_clause,[],[f6066])).
% 2.91/0.73  fof(f6066,plain,(
% 2.91/0.73    spl3_38 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),sK2)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 2.91/0.73  fof(f24,plain,(
% 2.91/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.91/0.73    inference(cnf_transformation,[],[f8])).
% 2.91/0.73  fof(f8,axiom,(
% 2.91/0.73    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.91/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.91/0.73  fof(f6091,plain,(
% 2.91/0.73    spl3_4 | ~spl3_38),
% 2.91/0.73    inference(avatar_contradiction_clause,[],[f6090])).
% 2.91/0.73  fof(f6090,plain,(
% 2.91/0.73    $false | (spl3_4 | ~spl3_38)),
% 2.91/0.73    inference(subsumption_resolution,[],[f6070,f47])).
% 2.91/0.73  fof(f6070,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_38),
% 2.91/0.73    inference(superposition,[],[f6068,f24])).
% 2.91/0.73  fof(f6069,plain,(
% 2.91/0.73    spl3_38 | ~spl3_37),
% 2.91/0.73    inference(avatar_split_clause,[],[f6036,f6019,f6066])).
% 2.91/0.73  fof(f6019,plain,(
% 2.91/0.73    spl3_37 <=> sK2 = k2_xboole_0(sK2,k3_xboole_0(sK1,sK0))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.91/0.73  fof(f6036,plain,(
% 2.91/0.73    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),sK2) | ~spl3_37),
% 2.91/0.73    inference(superposition,[],[f166,f6021])).
% 2.91/0.73  fof(f6021,plain,(
% 2.91/0.73    sK2 = k2_xboole_0(sK2,k3_xboole_0(sK1,sK0)) | ~spl3_37),
% 2.91/0.73    inference(avatar_component_clause,[],[f6019])).
% 2.91/0.73  fof(f166,plain,(
% 2.91/0.73    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))) )),
% 2.91/0.73    inference(forward_demodulation,[],[f152,f21])).
% 2.91/0.73  fof(f21,plain,(
% 2.91/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.91/0.73    inference(cnf_transformation,[],[f4])).
% 2.91/0.73  fof(f4,axiom,(
% 2.91/0.73    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.91/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.91/0.73  fof(f152,plain,(
% 2.91/0.73    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 2.91/0.73    inference(superposition,[],[f25,f51])).
% 2.91/0.73  fof(f51,plain,(
% 2.91/0.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.91/0.73    inference(forward_demodulation,[],[f49,f17])).
% 2.91/0.73  fof(f17,plain,(
% 2.91/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.91/0.73    inference(cnf_transformation,[],[f3])).
% 2.91/0.73  fof(f3,axiom,(
% 2.91/0.73    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.91/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.91/0.73  fof(f49,plain,(
% 2.91/0.73    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.91/0.73    inference(superposition,[],[f20,f19])).
% 2.91/0.73  fof(f19,plain,(
% 2.91/0.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.91/0.73    inference(cnf_transformation,[],[f5])).
% 2.91/0.73  fof(f5,axiom,(
% 2.91/0.73    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.91/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.91/0.73  fof(f20,plain,(
% 2.91/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.91/0.73    inference(cnf_transformation,[],[f7])).
% 2.91/0.73  fof(f7,axiom,(
% 2.91/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.91/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.91/0.73  fof(f25,plain,(
% 2.91/0.73    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.91/0.73    inference(cnf_transformation,[],[f6])).
% 2.91/0.73  fof(f6,axiom,(
% 2.91/0.73    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.91/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.91/0.73  fof(f6022,plain,(
% 2.91/0.73    spl3_37 | ~spl3_8),
% 2.91/0.73    inference(avatar_split_clause,[],[f5967,f675,f6019])).
% 2.91/0.73  fof(f675,plain,(
% 2.91/0.73    spl3_8 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.91/0.73  fof(f5967,plain,(
% 2.91/0.73    sK2 = k2_xboole_0(sK2,k3_xboole_0(sK1,sK0)) | ~spl3_8),
% 2.91/0.73    inference(superposition,[],[f5758,f2741])).
% 2.91/0.73  fof(f2741,plain,(
% 2.91/0.73    ( ! [X17,X18] : (k3_xboole_0(X17,X18) = k3_xboole_0(k3_xboole_0(X17,X18),X17)) )),
% 2.91/0.73    inference(superposition,[],[f201,f2584])).
% 2.91/0.73  fof(f2584,plain,(
% 2.91/0.73    ( ! [X21,X20] : (k2_xboole_0(X20,k3_xboole_0(X20,X21)) = X20) )),
% 2.91/0.73    inference(superposition,[],[f2513,f20])).
% 2.91/0.73  fof(f2513,plain,(
% 2.91/0.73    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 2.91/0.73    inference(forward_demodulation,[],[f2437,f18])).
% 2.91/0.73  fof(f18,plain,(
% 2.91/0.73    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.91/0.73    inference(cnf_transformation,[],[f2])).
% 2.91/0.73  fof(f2,axiom,(
% 2.91/0.73    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.91/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.91/0.73  fof(f2437,plain,(
% 2.91/0.73    ( ! [X4,X5] : (k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 2.91/0.73    inference(superposition,[],[f155,f166])).
% 2.91/0.73  fof(f155,plain,(
% 2.91/0.73    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 2.91/0.73    inference(superposition,[],[f21,f25])).
% 2.91/0.73  fof(f201,plain,(
% 2.91/0.73    ( ! [X10,X9] : (k3_xboole_0(X9,k2_xboole_0(X10,X9)) = X9) )),
% 2.91/0.73    inference(forward_demodulation,[],[f195,f19])).
% 2.91/0.73  fof(f195,plain,(
% 2.91/0.73    ( ! [X10,X9] : (k4_xboole_0(X9,k1_xboole_0) = k3_xboole_0(X9,k2_xboole_0(X10,X9))) )),
% 2.91/0.73    inference(superposition,[],[f20,f166])).
% 2.91/0.73  fof(f5758,plain,(
% 2.91/0.73    ( ! [X4] : (sK2 = k2_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X4,sK0),sK1))) ) | ~spl3_8),
% 2.91/0.73    inference(forward_demodulation,[],[f5739,f18])).
% 2.91/0.73  fof(f5739,plain,(
% 2.91/0.73    ( ! [X4] : (k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X4,sK0),sK1))) ) | ~spl3_8),
% 2.91/0.73    inference(superposition,[],[f64,f5540])).
% 2.91/0.73  fof(f5540,plain,(
% 2.91/0.73    ( ! [X116] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X116,sK0),k4_xboole_0(sK1,sK2))) ) | ~spl3_8),
% 2.91/0.73    inference(forward_demodulation,[],[f5321,f51])).
% 2.91/0.73  fof(f5321,plain,(
% 2.91/0.73    ( ! [X116] : (k3_xboole_0(k3_xboole_0(X116,sK0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(X116,sK0),k3_xboole_0(X116,sK0))) ) | ~spl3_8),
% 2.91/0.73    inference(superposition,[],[f65,f677])).
% 2.91/0.73  fof(f677,plain,(
% 2.91/0.73    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_8),
% 2.91/0.73    inference(avatar_component_clause,[],[f675])).
% 2.91/0.73  fof(f65,plain,(
% 2.91/0.73    ( ! [X6,X7,X5] : (k3_xboole_0(k3_xboole_0(X5,X6),X7) = k4_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,k4_xboole_0(X6,X7)))) )),
% 2.91/0.73    inference(superposition,[],[f20,f24])).
% 2.91/0.73  fof(f64,plain,(
% 2.91/0.73    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k3_xboole_0(X2,X3)) = k2_xboole_0(X4,k3_xboole_0(X2,k4_xboole_0(X3,X4)))) )),
% 2.91/0.73    inference(superposition,[],[f21,f24])).
% 2.91/0.73  fof(f5893,plain,(
% 2.91/0.73    spl3_36 | ~spl3_8),
% 2.91/0.73    inference(avatar_split_clause,[],[f5728,f675,f5890])).
% 2.91/0.73  fof(f5890,plain,(
% 2.91/0.73    spl3_36 <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.91/0.73  fof(f5728,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2)) | ~spl3_8),
% 2.91/0.73    inference(superposition,[],[f5540,f326])).
% 2.91/0.73  fof(f326,plain,(
% 2.91/0.73    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4)) )),
% 2.91/0.73    inference(forward_demodulation,[],[f319,f19])).
% 2.91/0.73  fof(f319,plain,(
% 2.91/0.73    ( ! [X4] : (k3_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 2.91/0.73    inference(superposition,[],[f20,f288])).
% 2.91/0.73  fof(f288,plain,(
% 2.91/0.73    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3)) )),
% 2.91/0.73    inference(superposition,[],[f145,f51])).
% 2.91/0.73  fof(f145,plain,(
% 2.91/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 2.91/0.73    inference(superposition,[],[f25,f19])).
% 2.91/0.73  fof(f3597,plain,(
% 2.91/0.73    spl3_35 | ~spl3_34),
% 2.91/0.73    inference(avatar_split_clause,[],[f3571,f3341,f3594])).
% 2.91/0.73  fof(f3594,plain,(
% 2.91/0.73    spl3_35 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_xboole_0(sK2,sK0),sK1),sK2)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.91/0.73  fof(f3341,plain,(
% 2.91/0.73    spl3_34 <=> sK2 = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.91/0.73  fof(f3571,plain,(
% 2.91/0.73    k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_xboole_0(sK2,sK0),sK1),sK2) | ~spl3_34),
% 2.91/0.73    inference(superposition,[],[f166,f3343])).
% 2.91/0.73  fof(f3343,plain,(
% 2.91/0.73    sK2 = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1)) | ~spl3_34),
% 2.91/0.73    inference(avatar_component_clause,[],[f3341])).
% 2.91/0.73  fof(f3344,plain,(
% 2.91/0.73    spl3_34 | ~spl3_31),
% 2.91/0.73    inference(avatar_split_clause,[],[f3312,f3267,f3341])).
% 2.91/0.73  fof(f3267,plain,(
% 2.91/0.73    spl3_31 <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.91/0.73  fof(f3312,plain,(
% 2.91/0.73    sK2 = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1)) | ~spl3_31),
% 2.91/0.73    inference(forward_demodulation,[],[f3299,f18])).
% 2.91/0.73  fof(f3299,plain,(
% 2.91/0.73    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK2,sK0),sK1)) | ~spl3_31),
% 2.91/0.73    inference(superposition,[],[f64,f3269])).
% 2.91/0.73  fof(f3269,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2)) | ~spl3_31),
% 2.91/0.73    inference(avatar_component_clause,[],[f3267])).
% 2.91/0.73  fof(f3339,plain,(
% 2.91/0.73    spl3_33 | ~spl3_30),
% 2.91/0.73    inference(avatar_split_clause,[],[f3277,f3262,f3336])).
% 2.91/0.73  fof(f3336,plain,(
% 2.91/0.73    spl3_33 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK0),sK1)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.91/0.73  fof(f3262,plain,(
% 2.91/0.73    spl3_30 <=> sK1 = k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.91/0.73  fof(f3277,plain,(
% 2.91/0.73    k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK0),sK1) | ~spl3_30),
% 2.91/0.73    inference(superposition,[],[f166,f3264])).
% 2.91/0.73  fof(f3264,plain,(
% 2.91/0.73    sK1 = k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | ~spl3_30),
% 2.91/0.73    inference(avatar_component_clause,[],[f3262])).
% 2.91/0.73  fof(f3275,plain,(
% 2.91/0.73    spl3_32 | ~spl3_29),
% 2.91/0.73    inference(avatar_split_clause,[],[f3200,f3141,f3272])).
% 2.91/0.73  fof(f3272,plain,(
% 2.91/0.73    spl3_32 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.91/0.73  fof(f3141,plain,(
% 2.91/0.73    spl3_29 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.91/0.73  fof(f3200,plain,(
% 2.91/0.73    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_29),
% 2.91/0.73    inference(forward_demodulation,[],[f3189,f20])).
% 2.91/0.73  fof(f3189,plain,(
% 2.91/0.73    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_29),
% 2.91/0.73    inference(superposition,[],[f20,f3143])).
% 2.91/0.73  fof(f3143,plain,(
% 2.91/0.73    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_29),
% 2.91/0.73    inference(avatar_component_clause,[],[f3141])).
% 2.91/0.73  fof(f3270,plain,(
% 2.91/0.73    spl3_31 | ~spl3_29),
% 2.91/0.73    inference(avatar_split_clause,[],[f3198,f3141,f3267])).
% 2.91/0.73  fof(f3198,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2)) | ~spl3_29),
% 2.91/0.73    inference(superposition,[],[f2916,f3143])).
% 2.91/0.73  fof(f2916,plain,(
% 2.91/0.73    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 2.91/0.73    inference(superposition,[],[f2737,f24])).
% 2.91/0.73  fof(f2737,plain,(
% 2.91/0.73    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X8)) )),
% 2.91/0.73    inference(superposition,[],[f166,f2584])).
% 2.91/0.73  fof(f3265,plain,(
% 2.91/0.73    spl3_30 | ~spl3_28),
% 2.91/0.73    inference(avatar_split_clause,[],[f3174,f3091,f3262])).
% 2.91/0.73  fof(f3091,plain,(
% 2.91/0.73    spl3_28 <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.91/0.73  fof(f3174,plain,(
% 2.91/0.73    sK1 = k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | ~spl3_28),
% 2.91/0.73    inference(forward_demodulation,[],[f3161,f18])).
% 2.91/0.73  fof(f3161,plain,(
% 2.91/0.73    k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_28),
% 2.91/0.73    inference(superposition,[],[f64,f3093])).
% 2.91/0.73  fof(f3093,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_28),
% 2.91/0.73    inference(avatar_component_clause,[],[f3091])).
% 2.91/0.73  fof(f3144,plain,(
% 2.91/0.73    spl3_29 | ~spl3_26),
% 2.91/0.73    inference(avatar_split_clause,[],[f3047,f3028,f3141])).
% 2.91/0.73  fof(f3028,plain,(
% 2.91/0.73    spl3_26 <=> k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.91/0.73  fof(f3047,plain,(
% 2.91/0.73    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_26),
% 2.91/0.73    inference(forward_demodulation,[],[f3046,f19])).
% 2.91/0.73  fof(f3046,plain,(
% 2.91/0.73    k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_26),
% 2.91/0.73    inference(forward_demodulation,[],[f3045,f154])).
% 2.91/0.73  fof(f154,plain,(
% 2.91/0.73    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k3_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 2.91/0.73    inference(superposition,[],[f58,f25])).
% 2.91/0.73  fof(f58,plain,(
% 2.91/0.73    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.91/0.73    inference(superposition,[],[f24,f53])).
% 2.91/0.73  fof(f53,plain,(
% 2.91/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.91/0.73    inference(forward_demodulation,[],[f52,f19])).
% 2.91/0.73  fof(f52,plain,(
% 2.91/0.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 2.91/0.73    inference(superposition,[],[f20,f51])).
% 2.91/0.73  fof(f3045,plain,(
% 2.91/0.73    k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))) | ~spl3_26),
% 2.91/0.73    inference(forward_demodulation,[],[f3033,f25])).
% 2.91/0.73  fof(f3033,plain,(
% 2.91/0.73    k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) | ~spl3_26),
% 2.91/0.73    inference(superposition,[],[f50,f3030])).
% 2.91/0.73  fof(f3030,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_26),
% 2.91/0.73    inference(avatar_component_clause,[],[f3028])).
% 2.91/0.73  fof(f50,plain,(
% 2.91/0.73    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 2.91/0.73    inference(superposition,[],[f20,f20])).
% 2.91/0.73  fof(f3094,plain,(
% 2.91/0.73    spl3_28 | ~spl3_10),
% 2.91/0.73    inference(avatar_split_clause,[],[f2991,f986,f3091])).
% 2.91/0.73  fof(f986,plain,(
% 2.91/0.73    spl3_10 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.91/0.73  fof(f2991,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_10),
% 2.91/0.73    inference(superposition,[],[f2916,f988])).
% 2.91/0.73  fof(f988,plain,(
% 2.91/0.73    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_10),
% 2.91/0.73    inference(avatar_component_clause,[],[f986])).
% 2.91/0.73  fof(f3089,plain,(
% 2.91/0.73    spl3_27 | ~spl3_11),
% 2.91/0.73    inference(avatar_split_clause,[],[f2987,f991,f3086])).
% 2.91/0.73  fof(f3086,plain,(
% 2.91/0.73    spl3_27 <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.91/0.73  fof(f991,plain,(
% 2.91/0.73    spl3_11 <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.91/0.73  fof(f2987,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_11),
% 2.91/0.73    inference(superposition,[],[f2916,f993])).
% 2.91/0.73  fof(f993,plain,(
% 2.91/0.73    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) | ~spl3_11),
% 2.91/0.73    inference(avatar_component_clause,[],[f991])).
% 2.91/0.73  fof(f3031,plain,(
% 2.91/0.73    spl3_26 | ~spl3_8),
% 2.91/0.73    inference(avatar_split_clause,[],[f2982,f675,f3028])).
% 2.91/0.73  fof(f2982,plain,(
% 2.91/0.73    k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_8),
% 2.91/0.73    inference(superposition,[],[f2916,f677])).
% 2.91/0.73  fof(f2411,plain,(
% 2.91/0.73    spl3_25 | ~spl3_21),
% 2.91/0.73    inference(avatar_split_clause,[],[f2345,f1984,f2408])).
% 2.91/0.73  fof(f2408,plain,(
% 2.91/0.73    spl3_25 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k1_xboole_0,sK2))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.91/0.73  fof(f1984,plain,(
% 2.91/0.73    spl3_21 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.91/0.73  fof(f2345,plain,(
% 2.91/0.73    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k1_xboole_0,sK2)) | ~spl3_21),
% 2.91/0.73    inference(superposition,[],[f1899,f1986])).
% 2.91/0.73  fof(f1986,plain,(
% 2.91/0.73    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl3_21),
% 2.91/0.73    inference(avatar_component_clause,[],[f1984])).
% 2.91/0.73  fof(f1899,plain,(
% 2.91/0.73    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X12,X13),k2_xboole_0(k1_xboole_0,X13))) )),
% 2.91/0.73    inference(superposition,[],[f1828,f308])).
% 2.91/0.73  fof(f308,plain,(
% 2.91/0.73    ( ! [X14,X13] : (k3_xboole_0(X13,k2_xboole_0(k1_xboole_0,X14)) = k3_xboole_0(X13,X14)) )),
% 2.91/0.73    inference(forward_demodulation,[],[f300,f20])).
% 2.91/0.73  fof(f300,plain,(
% 2.91/0.73    ( ! [X14,X13] : (k3_xboole_0(X13,k2_xboole_0(k1_xboole_0,X14)) = k4_xboole_0(X13,k4_xboole_0(X13,X14))) )),
% 2.91/0.73    inference(superposition,[],[f20,f145])).
% 2.91/0.73  fof(f1828,plain,(
% 2.91/0.73    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X2),X2)) )),
% 2.91/0.73    inference(superposition,[],[f166,f1648])).
% 2.91/0.73  fof(f1648,plain,(
% 2.91/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 2.91/0.73    inference(forward_demodulation,[],[f1647,f18])).
% 2.91/0.73  fof(f1647,plain,(
% 2.91/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.91/0.73    inference(forward_demodulation,[],[f1560,f17])).
% 2.91/0.73  fof(f1560,plain,(
% 2.91/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k2_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 2.91/0.73    inference(superposition,[],[f64,f51])).
% 2.91/0.73  fof(f2125,plain,(
% 2.91/0.73    spl3_24 | ~spl3_12),
% 2.91/0.73    inference(avatar_split_clause,[],[f1920,f1010,f2122])).
% 2.91/0.73  fof(f2122,plain,(
% 2.91/0.73    spl3_24 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.91/0.73  fof(f1010,plain,(
% 2.91/0.73    spl3_12 <=> k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.91/0.73  fof(f1920,plain,(
% 2.91/0.73    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) | ~spl3_12),
% 2.91/0.73    inference(superposition,[],[f1828,f1012])).
% 2.91/0.73  fof(f1012,plain,(
% 2.91/0.73    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1) | ~spl3_12),
% 2.91/0.73    inference(avatar_component_clause,[],[f1010])).
% 2.91/0.73  fof(f2105,plain,(
% 2.91/0.73    spl3_23 | ~spl3_20),
% 2.91/0.73    inference(avatar_split_clause,[],[f2046,f1771,f2102])).
% 2.91/0.73  fof(f2102,plain,(
% 2.91/0.73    spl3_23 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)),sK2)),
% 2.91/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.91/0.74  fof(f1771,plain,(
% 2.91/0.74    spl3_20 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.91/0.74  fof(f2046,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)),sK2) | ~spl3_20),
% 2.91/0.74    inference(superposition,[],[f2004,f326])).
% 2.91/0.74  fof(f2004,plain,(
% 2.91/0.74    ( ! [X13] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X13,k3_xboole_0(sK0,sK1)),sK2)) ) | ~spl3_20),
% 2.91/0.74    inference(superposition,[],[f166,f1790])).
% 2.91/0.74  fof(f1790,plain,(
% 2.91/0.74    ( ! [X1] : (sK2 = k2_xboole_0(sK2,k3_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | ~spl3_20),
% 2.91/0.74    inference(forward_demodulation,[],[f1789,f18])).
% 2.91/0.74  fof(f1789,plain,(
% 2.91/0.74    ( ! [X1] : (k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | ~spl3_20),
% 2.91/0.74    inference(forward_demodulation,[],[f1782,f17])).
% 2.91/0.74  fof(f1782,plain,(
% 2.91/0.74    ( ! [X1] : (k2_xboole_0(sK2,k3_xboole_0(X1,k3_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,k3_xboole_0(X1,k1_xboole_0))) ) | ~spl3_20),
% 2.91/0.74    inference(superposition,[],[f64,f1773])).
% 2.91/0.74  fof(f1773,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl3_20),
% 2.91/0.74    inference(avatar_component_clause,[],[f1771])).
% 2.91/0.74  fof(f2042,plain,(
% 2.91/0.74    spl3_22 | ~spl3_20),
% 2.91/0.74    inference(avatar_split_clause,[],[f1991,f1771,f2039])).
% 2.91/0.74  fof(f2039,plain,(
% 2.91/0.74    spl3_22 <=> sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.91/0.74  fof(f1991,plain,(
% 2.91/0.74    sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))) | ~spl3_20),
% 2.91/0.74    inference(superposition,[],[f1790,f326])).
% 2.91/0.74  fof(f1987,plain,(
% 2.91/0.74    spl3_21 | ~spl3_19),
% 2.91/0.74    inference(avatar_split_clause,[],[f1752,f1733,f1984])).
% 2.91/0.74  fof(f1733,plain,(
% 2.91/0.74    spl3_19 <=> sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.91/0.74  fof(f1752,plain,(
% 2.91/0.74    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl3_19),
% 2.91/0.74    inference(superposition,[],[f201,f1735])).
% 2.91/0.74  fof(f1735,plain,(
% 2.91/0.74    sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_19),
% 2.91/0.74    inference(avatar_component_clause,[],[f1733])).
% 2.91/0.74  fof(f1774,plain,(
% 2.91/0.74    spl3_20 | ~spl3_19),
% 2.91/0.74    inference(avatar_split_clause,[],[f1748,f1733,f1771])).
% 2.91/0.74  fof(f1748,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl3_19),
% 2.91/0.74    inference(superposition,[],[f166,f1735])).
% 2.91/0.74  fof(f1736,plain,(
% 2.91/0.74    spl3_19 | ~spl3_3),
% 2.91/0.74    inference(avatar_split_clause,[],[f1702,f38,f1733])).
% 2.91/0.74  fof(f38,plain,(
% 2.91/0.74    spl3_3 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.91/0.74  fof(f1702,plain,(
% 2.91/0.74    sK2 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_3),
% 2.91/0.74    inference(forward_demodulation,[],[f1599,f18])).
% 2.91/0.74  fof(f1599,plain,(
% 2.91/0.74    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_3),
% 2.91/0.74    inference(superposition,[],[f64,f40])).
% 2.91/0.74  fof(f40,plain,(
% 2.91/0.74    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 2.91/0.74    inference(avatar_component_clause,[],[f38])).
% 2.91/0.74  fof(f1326,plain,(
% 2.91/0.74    spl3_18 | ~spl3_3 | ~spl3_8),
% 2.91/0.74    inference(avatar_split_clause,[],[f1162,f675,f38,f1323])).
% 2.91/0.74  fof(f1323,plain,(
% 2.91/0.74    spl3_18 <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.91/0.74  fof(f1162,plain,(
% 2.91/0.74    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) | (~spl3_3 | ~spl3_8)),
% 2.91/0.74    inference(forward_demodulation,[],[f1149,f40])).
% 2.91/0.74  fof(f1149,plain,(
% 2.91/0.74    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) | ~spl3_8),
% 2.91/0.74    inference(superposition,[],[f958,f519])).
% 2.91/0.74  fof(f519,plain,(
% 2.91/0.74    ( ! [X4] : (k2_xboole_0(X4,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X4))) = X4) )),
% 2.91/0.74    inference(forward_demodulation,[],[f512,f18])).
% 2.91/0.74  fof(f512,plain,(
% 2.91/0.74    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X4)))) )),
% 2.91/0.74    inference(superposition,[],[f21,f315])).
% 2.91/0.74  fof(f315,plain,(
% 2.91/0.74    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)),X1)) )),
% 2.91/0.74    inference(superposition,[],[f288,f145])).
% 2.91/0.74  fof(f958,plain,(
% 2.91/0.74    ( ! [X5] : (k3_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X5)) = k3_xboole_0(sK0,X5)) ) | ~spl3_8),
% 2.91/0.74    inference(forward_demodulation,[],[f953,f20])).
% 2.91/0.74  fof(f953,plain,(
% 2.91/0.74    ( ! [X5] : (k3_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X5)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X5))) ) | ~spl3_8),
% 2.91/0.74    inference(superposition,[],[f20,f681])).
% 2.91/0.74  fof(f681,plain,(
% 2.91/0.74    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0))) ) | ~spl3_8),
% 2.91/0.74    inference(superposition,[],[f25,f677])).
% 2.91/0.74  fof(f1315,plain,(
% 2.91/0.74    spl3_17 | ~spl3_16),
% 2.91/0.74    inference(avatar_split_clause,[],[f1282,f1259,f1312])).
% 2.91/0.74  fof(f1312,plain,(
% 2.91/0.74    spl3_17 <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.91/0.74  fof(f1259,plain,(
% 2.91/0.74    spl3_16 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.91/0.74  fof(f1282,plain,(
% 2.91/0.74    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | ~spl3_16),
% 2.91/0.74    inference(forward_demodulation,[],[f1279,f19])).
% 2.91/0.74  fof(f1279,plain,(
% 2.91/0.74    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | ~spl3_16),
% 2.91/0.74    inference(superposition,[],[f20,f1261])).
% 2.91/0.74  fof(f1261,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | ~spl3_16),
% 2.91/0.74    inference(avatar_component_clause,[],[f1259])).
% 2.91/0.74  fof(f1262,plain,(
% 2.91/0.74    spl3_16 | ~spl3_14),
% 2.91/0.74    inference(avatar_split_clause,[],[f1215,f1211,f1259])).
% 2.91/0.74  fof(f1211,plain,(
% 2.91/0.74    spl3_14 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.91/0.74  fof(f1215,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | ~spl3_14),
% 2.91/0.74    inference(superposition,[],[f1213,f25])).
% 2.91/0.74  fof(f1213,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | ~spl3_14),
% 2.91/0.74    inference(avatar_component_clause,[],[f1211])).
% 2.91/0.74  fof(f1230,plain,(
% 2.91/0.74    spl3_15 | ~spl3_12),
% 2.91/0.74    inference(avatar_split_clause,[],[f1129,f1010,f1227])).
% 2.91/0.74  fof(f1227,plain,(
% 2.91/0.74    spl3_15 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,k3_xboole_0(sK0,sK1))))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.91/0.74  fof(f1129,plain,(
% 2.91/0.74    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,k3_xboole_0(sK0,sK1)))) | ~spl3_12),
% 2.91/0.74    inference(forward_demodulation,[],[f1123,f24])).
% 2.91/0.74  fof(f1123,plain,(
% 2.91/0.74    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1))) | ~spl3_12),
% 2.91/0.74    inference(superposition,[],[f62,f1012])).
% 2.91/0.74  fof(f62,plain,(
% 2.91/0.74    ( ! [X8,X9] : (k1_xboole_0 = k3_xboole_0(X8,k4_xboole_0(X9,k3_xboole_0(X8,X9)))) )),
% 2.91/0.74    inference(superposition,[],[f24,f51])).
% 2.91/0.74  fof(f1214,plain,(
% 2.91/0.74    spl3_14 | ~spl3_10),
% 2.91/0.74    inference(avatar_split_clause,[],[f995,f986,f1211])).
% 2.91/0.74  fof(f995,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | ~spl3_10),
% 2.91/0.74    inference(superposition,[],[f186,f988])).
% 2.91/0.74  fof(f186,plain,(
% 2.91/0.74    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 2.91/0.74    inference(superposition,[],[f166,f21])).
% 2.91/0.74  fof(f1018,plain,(
% 2.91/0.74    spl3_13 | ~spl3_11),
% 2.91/0.74    inference(avatar_split_clause,[],[f1008,f991,f1015])).
% 2.91/0.74  fof(f1015,plain,(
% 2.91/0.74    spl3_13 <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.91/0.74  fof(f1008,plain,(
% 2.91/0.74    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) | ~spl3_11),
% 2.91/0.74    inference(forward_demodulation,[],[f1007,f51])).
% 2.91/0.74  fof(f1007,plain,(
% 2.91/0.74    k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) | ~spl3_11),
% 2.91/0.74    inference(superposition,[],[f20,f993])).
% 2.91/0.74  fof(f1013,plain,(
% 2.91/0.74    spl3_12 | ~spl3_10),
% 2.91/0.74    inference(avatar_split_clause,[],[f1001,f986,f1010])).
% 2.91/0.74  fof(f1001,plain,(
% 2.91/0.74    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1) | ~spl3_10),
% 2.91/0.74    inference(forward_demodulation,[],[f999,f20])).
% 2.91/0.74  fof(f999,plain,(
% 2.91/0.74    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_10),
% 2.91/0.74    inference(superposition,[],[f20,f988])).
% 2.91/0.74  fof(f994,plain,(
% 2.91/0.74    spl3_11 | ~spl3_8),
% 2.91/0.74    inference(avatar_split_clause,[],[f979,f675,f991])).
% 2.91/0.74  fof(f979,plain,(
% 2.91/0.74    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) | ~spl3_8),
% 2.91/0.74    inference(forward_demodulation,[],[f968,f19])).
% 2.91/0.74  fof(f968,plain,(
% 2.91/0.74    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) | ~spl3_8),
% 2.91/0.74    inference(superposition,[],[f956,f288])).
% 2.91/0.74  fof(f956,plain,(
% 2.91/0.74    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | ~spl3_8),
% 2.91/0.74    inference(forward_demodulation,[],[f944,f681])).
% 2.91/0.74  fof(f944,plain,(
% 2.91/0.74    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | ~spl3_8),
% 2.91/0.74    inference(superposition,[],[f681,f21])).
% 2.91/0.74  fof(f989,plain,(
% 2.91/0.74    spl3_10 | ~spl3_8),
% 2.91/0.74    inference(avatar_split_clause,[],[f964,f675,f986])).
% 2.91/0.74  fof(f964,plain,(
% 2.91/0.74    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_8),
% 2.91/0.74    inference(superposition,[],[f956,f20])).
% 2.91/0.74  fof(f963,plain,(
% 2.91/0.74    spl3_9 | ~spl3_8),
% 2.91/0.74    inference(avatar_split_clause,[],[f955,f675,f960])).
% 2.91/0.74  fof(f960,plain,(
% 2.91/0.74    spl3_9 <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.91/0.74  fof(f955,plain,(
% 2.91/0.74    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) | ~spl3_8),
% 2.91/0.74    inference(forward_demodulation,[],[f943,f677])).
% 2.91/0.74  fof(f943,plain,(
% 2.91/0.74    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) | ~spl3_8),
% 2.91/0.74    inference(superposition,[],[f681,f519])).
% 2.91/0.74  fof(f678,plain,(
% 2.91/0.74    spl3_8 | ~spl3_7),
% 2.91/0.74    inference(avatar_split_clause,[],[f662,f658,f675])).
% 2.91/0.74  fof(f658,plain,(
% 2.91/0.74    spl3_7 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.91/0.74  fof(f662,plain,(
% 2.91/0.74    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_7),
% 2.91/0.74    inference(superposition,[],[f660,f58])).
% 2.91/0.74  fof(f660,plain,(
% 2.91/0.74    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_7),
% 2.91/0.74    inference(avatar_component_clause,[],[f658])).
% 2.91/0.74  fof(f661,plain,(
% 2.91/0.74    spl3_7 | ~spl3_3),
% 2.91/0.74    inference(avatar_split_clause,[],[f636,f38,f658])).
% 2.91/0.74  fof(f636,plain,(
% 2.91/0.74    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 2.91/0.74    inference(forward_demodulation,[],[f607,f19])).
% 2.91/0.74  fof(f607,plain,(
% 2.91/0.74    k3_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_3),
% 2.91/0.74    inference(superposition,[],[f50,f40])).
% 2.91/0.74  fof(f179,plain,(
% 2.91/0.74    spl3_6 | ~spl3_5),
% 2.91/0.74    inference(avatar_split_clause,[],[f174,f141,f176])).
% 2.91/0.74  fof(f176,plain,(
% 2.91/0.74    spl3_6 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.91/0.74  fof(f141,plain,(
% 2.91/0.74    spl3_5 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.91/0.74  fof(f174,plain,(
% 2.91/0.74    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl3_5),
% 2.91/0.74    inference(forward_demodulation,[],[f173,f19])).
% 2.91/0.74  fof(f173,plain,(
% 2.91/0.74    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2) | ~spl3_5),
% 2.91/0.74    inference(superposition,[],[f20,f143])).
% 2.91/0.74  fof(f143,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl3_5),
% 2.91/0.74    inference(avatar_component_clause,[],[f141])).
% 2.91/0.74  fof(f144,plain,(
% 2.91/0.74    spl3_5 | ~spl3_3),
% 2.91/0.74    inference(avatar_split_clause,[],[f136,f38,f141])).
% 2.91/0.74  fof(f136,plain,(
% 2.91/0.74    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl3_3),
% 2.91/0.74    inference(forward_demodulation,[],[f130,f40])).
% 2.91/0.74  fof(f130,plain,(
% 2.91/0.74    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK2) | ~spl3_3),
% 2.91/0.74    inference(superposition,[],[f68,f56])).
% 2.91/0.74  fof(f56,plain,(
% 2.91/0.74    ( ! [X3] : (k2_xboole_0(X3,X3) = X3) )),
% 2.91/0.74    inference(forward_demodulation,[],[f55,f18])).
% 2.91/0.74  fof(f55,plain,(
% 2.91/0.74    ( ! [X3] : (k2_xboole_0(X3,X3) = k2_xboole_0(X3,k1_xboole_0)) )),
% 2.91/0.74    inference(superposition,[],[f21,f51])).
% 2.91/0.74  fof(f68,plain,(
% 2.91/0.74    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,X4)))) ) | ~spl3_3),
% 2.91/0.74    inference(forward_demodulation,[],[f59,f25])).
% 2.91/0.74  fof(f59,plain,(
% 2.91/0.74    ( ! [X4] : (k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X4)) = k4_xboole_0(k1_xboole_0,X4)) ) | ~spl3_3),
% 2.91/0.74    inference(superposition,[],[f24,f40])).
% 2.91/0.74  fof(f48,plain,(
% 2.91/0.74    ~spl3_4 | spl3_2),
% 2.91/0.74    inference(avatar_split_clause,[],[f42,f32,f45])).
% 2.91/0.74  fof(f32,plain,(
% 2.91/0.74    spl3_2 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.91/0.74  fof(f42,plain,(
% 2.91/0.74    k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 2.91/0.74    inference(resolution,[],[f23,f34])).
% 2.91/0.74  fof(f34,plain,(
% 2.91/0.74    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 2.91/0.74    inference(avatar_component_clause,[],[f32])).
% 2.91/0.74  fof(f23,plain,(
% 2.91/0.74    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.91/0.74    inference(cnf_transformation,[],[f14])).
% 2.91/0.74  fof(f14,plain,(
% 2.91/0.74    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.91/0.74    inference(nnf_transformation,[],[f1])).
% 2.91/0.74  fof(f1,axiom,(
% 2.91/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.91/0.74  fof(f41,plain,(
% 2.91/0.74    spl3_3 | ~spl3_1),
% 2.91/0.74    inference(avatar_split_clause,[],[f36,f27,f38])).
% 2.91/0.74  fof(f27,plain,(
% 2.91/0.74    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.91/0.74  fof(f36,plain,(
% 2.91/0.74    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.91/0.74    inference(resolution,[],[f22,f29])).
% 2.91/0.74  fof(f29,plain,(
% 2.91/0.74    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.91/0.74    inference(avatar_component_clause,[],[f27])).
% 2.91/0.74  fof(f22,plain,(
% 2.91/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.91/0.74    inference(cnf_transformation,[],[f14])).
% 2.91/0.74  fof(f35,plain,(
% 2.91/0.74    ~spl3_2),
% 2.91/0.74    inference(avatar_split_clause,[],[f16,f32])).
% 2.91/0.74  fof(f16,plain,(
% 2.91/0.74    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.91/0.74    inference(cnf_transformation,[],[f13])).
% 2.91/0.74  fof(f13,plain,(
% 2.91/0.74    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.91/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 2.91/0.74  fof(f12,plain,(
% 2.91/0.74    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.91/0.74    introduced(choice_axiom,[])).
% 2.91/0.74  fof(f11,plain,(
% 2.91/0.74    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.91/0.74    inference(ennf_transformation,[],[f10])).
% 2.91/0.74  fof(f10,negated_conjecture,(
% 2.91/0.74    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.91/0.74    inference(negated_conjecture,[],[f9])).
% 2.91/0.74  fof(f9,conjecture,(
% 2.91/0.74    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 2.91/0.74  fof(f30,plain,(
% 2.91/0.74    spl3_1),
% 2.91/0.74    inference(avatar_split_clause,[],[f15,f27])).
% 2.91/0.74  fof(f15,plain,(
% 2.91/0.74    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.91/0.74    inference(cnf_transformation,[],[f13])).
% 2.91/0.74  % SZS output end Proof for theBenchmark
% 2.91/0.74  % (7216)------------------------------
% 2.91/0.74  % (7216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.74  % (7216)Termination reason: Refutation
% 2.91/0.74  
% 2.91/0.74  % (7216)Memory used [KB]: 9722
% 2.91/0.74  % (7216)Time elapsed: 0.313 s
% 2.91/0.74  % (7216)------------------------------
% 2.91/0.74  % (7216)------------------------------
% 2.91/0.74  % (7215)Success in time 0.388 s
%------------------------------------------------------------------------------
