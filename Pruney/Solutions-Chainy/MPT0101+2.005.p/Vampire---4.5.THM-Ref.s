%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:52 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 448 expanded)
%              Number of leaves         :   27 ( 167 expanded)
%              Depth                    :   20
%              Number of atoms          :  172 ( 532 expanded)
%              Number of equality atoms :  105 ( 431 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2518,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f54,f105,f149,f150,f2463,f2468,f2483,f2491,f2497,f2505,f2510,f2511,f2515,f2517])).

fof(f2517,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f2516])).

fof(f2516,plain,
    ( $false
    | spl2_10 ),
    inference(trivial_inequality_removal,[],[f2512])).

fof(f2512,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | spl2_10 ),
    inference(superposition,[],[f2504,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2504,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f2502])).

fof(f2502,plain,
    ( spl2_10
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f2515,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f2514])).

fof(f2514,plain,
    ( $false
    | spl2_10 ),
    inference(trivial_inequality_removal,[],[f2513])).

fof(f2513,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | spl2_10 ),
    inference(superposition,[],[f2504,f26])).

fof(f2511,plain,
    ( ~ spl2_11
    | spl2_8 ),
    inference(avatar_split_clause,[],[f2500,f2488,f2507])).

fof(f2507,plain,
    ( spl2_11
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f2488,plain,
    ( spl2_8
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f2500,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | spl2_8 ),
    inference(superposition,[],[f2490,f26])).

fof(f2490,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f2488])).

fof(f2510,plain,
    ( ~ spl2_11
    | spl2_8 ),
    inference(avatar_split_clause,[],[f2499,f2488,f2507])).

fof(f2499,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | spl2_8 ),
    inference(superposition,[],[f2490,f26])).

fof(f2505,plain,
    ( ~ spl2_10
    | spl2_8 ),
    inference(avatar_split_clause,[],[f2498,f2488,f2502])).

fof(f2498,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)
    | spl2_8 ),
    inference(superposition,[],[f2490,f418])).

fof(f418,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(forward_demodulation,[],[f393,f131])).

fof(f131,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X10,X9),k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f112,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f112,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f83,f26])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f80])).

fof(f80,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f77,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f77,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1) ),
    inference(superposition,[],[f28,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f36,f65])).

fof(f65,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f47,f24])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f37,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f23,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f393,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f239,f28])).

fof(f239,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f183,f33])).

fof(f183,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k2_xboole_0(X4,X5),X4) ),
    inference(forward_demodulation,[],[f178,f24])).

fof(f178,plain,(
    ! [X4,X5] : k2_xboole_0(k2_xboole_0(X4,X5),X4) = k2_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0) ),
    inference(superposition,[],[f28,f161])).

fof(f161,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f152,f22])).

fof(f152,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f34,f72])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2497,plain,
    ( ~ spl2_9
    | spl2_7 ),
    inference(avatar_split_clause,[],[f2492,f2480,f2494])).

fof(f2494,plain,
    ( spl2_9
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f2480,plain,
    ( spl2_7
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f2492,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl2_7 ),
    inference(forward_demodulation,[],[f2485,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f2485,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)))
    | spl2_7 ),
    inference(superposition,[],[f2482,f91])).

fof(f91,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f33,f26])).

fof(f2482,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f2480])).

fof(f2491,plain,
    ( ~ spl2_8
    | spl2_7 ),
    inference(avatar_split_clause,[],[f2486,f2480,f2488])).

fof(f2486,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | spl2_7 ),
    inference(forward_demodulation,[],[f2484,f838])).

fof(f838,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = X6 ),
    inference(backward_demodulation,[],[f351,f836])).

fof(f836,plain,(
    ! [X19,X18] : k2_xboole_0(X18,k4_xboole_0(X18,X19)) = X18 ),
    inference(forward_demodulation,[],[f835,f831])).

fof(f831,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5 ),
    inference(forward_demodulation,[],[f809,f40])).

fof(f809,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f835,plain,(
    ! [X19,X18] : k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X18) = k2_xboole_0(X18,k4_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f834,f26])).

fof(f834,plain,(
    ! [X19,X18] : k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X18) = k2_xboole_0(k4_xboole_0(X18,X19),X18) ),
    inference(forward_demodulation,[],[f813,f28])).

fof(f813,plain,(
    ! [X19,X18] : k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X18) = k2_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,k4_xboole_0(X18,X19))) ),
    inference(superposition,[],[f418,f39])).

fof(f351,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f330,f26])).

fof(f330,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))) ),
    inference(superposition,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2484,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_7 ),
    inference(superposition,[],[f2482,f91])).

fof(f2483,plain,
    ( ~ spl2_7
    | spl2_6 ),
    inference(avatar_split_clause,[],[f2476,f2465,f2480])).

fof(f2465,plain,
    ( spl2_6
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f2476,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_6 ),
    inference(superposition,[],[f2467,f418])).

fof(f2467,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f2465])).

fof(f2468,plain,
    ( ~ spl2_6
    | spl2_3 ),
    inference(avatar_split_clause,[],[f2458,f102,f2465])).

fof(f102,plain,
    ( spl2_3
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2458,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f104,f2409])).

fof(f2409,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k4_xboole_0(X9,k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9))) ),
    inference(superposition,[],[f48,f802])).

fof(f802,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f39,f38])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f41,f34])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f32,f27,f27])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f104,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f2463,plain,
    ( ~ spl2_5
    | spl2_4 ),
    inference(avatar_split_clause,[],[f2457,f146,f2460])).

fof(f2460,plain,
    ( spl2_5
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f146,plain,
    ( spl2_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2457,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_4 ),
    inference(backward_demodulation,[],[f148,f2409])).

fof(f148,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f150,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f144,f102,f146])).

fof(f144,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_3 ),
    inference(superposition,[],[f104,f26])).

fof(f149,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f143,f102,f146])).

fof(f143,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_3 ),
    inference(superposition,[],[f104,f26])).

fof(f105,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f100,f51,f102])).

fof(f51,plain,
    ( spl2_2
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f100,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_2 ),
    inference(backward_demodulation,[],[f53,f83])).

fof(f53,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f49,f43,f51])).

fof(f43,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f49,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f45,f34])).

fof(f45,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f46,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f35,f43])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f31,f31,f27])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:31:00 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.43  % (16744)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (16742)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (16737)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (16740)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (16739)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (16743)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (16738)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (16745)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (16746)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (16747)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (16746)Refutation not found, incomplete strategy% (16746)------------------------------
% 0.22/0.49  % (16746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16746)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16746)Memory used [KB]: 10490
% 0.22/0.49  % (16746)Time elapsed: 0.044 s
% 0.22/0.49  % (16746)------------------------------
% 0.22/0.49  % (16746)------------------------------
% 0.22/0.50  % (16749)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (16752)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (16736)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (16735)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (16748)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (16751)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (16750)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (16741)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 2.31/0.68  % (16745)Refutation found. Thanks to Tanya!
% 2.31/0.68  % SZS status Theorem for theBenchmark
% 2.31/0.68  % SZS output start Proof for theBenchmark
% 2.31/0.68  fof(f2518,plain,(
% 2.31/0.68    $false),
% 2.31/0.68    inference(avatar_sat_refutation,[],[f46,f54,f105,f149,f150,f2463,f2468,f2483,f2491,f2497,f2505,f2510,f2511,f2515,f2517])).
% 2.31/0.68  fof(f2517,plain,(
% 2.31/0.68    spl2_10),
% 2.31/0.68    inference(avatar_contradiction_clause,[],[f2516])).
% 2.31/0.68  fof(f2516,plain,(
% 2.31/0.68    $false | spl2_10),
% 2.31/0.68    inference(trivial_inequality_removal,[],[f2512])).
% 2.31/0.68  fof(f2512,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | spl2_10),
% 2.31/0.68    inference(superposition,[],[f2504,f26])).
% 2.31/0.68  fof(f26,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f1])).
% 2.31/0.68  fof(f1,axiom,(
% 2.31/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.31/0.68  fof(f2504,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) | spl2_10),
% 2.31/0.68    inference(avatar_component_clause,[],[f2502])).
% 2.31/0.68  fof(f2502,plain,(
% 2.31/0.68    spl2_10 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0)),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.31/0.68  fof(f2515,plain,(
% 2.31/0.68    spl2_10),
% 2.31/0.68    inference(avatar_contradiction_clause,[],[f2514])).
% 2.31/0.68  fof(f2514,plain,(
% 2.31/0.68    $false | spl2_10),
% 2.31/0.68    inference(trivial_inequality_removal,[],[f2513])).
% 2.31/0.68  fof(f2513,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | spl2_10),
% 2.31/0.68    inference(superposition,[],[f2504,f26])).
% 2.31/0.68  fof(f2511,plain,(
% 2.31/0.68    ~spl2_11 | spl2_8),
% 2.31/0.68    inference(avatar_split_clause,[],[f2500,f2488,f2507])).
% 2.31/0.68  fof(f2507,plain,(
% 2.31/0.68    spl2_11 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.31/0.68  fof(f2488,plain,(
% 2.31/0.68    spl2_8 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.31/0.68  fof(f2500,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | spl2_8),
% 2.31/0.68    inference(superposition,[],[f2490,f26])).
% 2.31/0.68  fof(f2490,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) | spl2_8),
% 2.31/0.68    inference(avatar_component_clause,[],[f2488])).
% 2.31/0.68  fof(f2510,plain,(
% 2.31/0.68    ~spl2_11 | spl2_8),
% 2.31/0.68    inference(avatar_split_clause,[],[f2499,f2488,f2507])).
% 2.31/0.68  fof(f2499,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | spl2_8),
% 2.31/0.68    inference(superposition,[],[f2490,f26])).
% 2.31/0.68  fof(f2505,plain,(
% 2.31/0.68    ~spl2_10 | spl2_8),
% 2.31/0.68    inference(avatar_split_clause,[],[f2498,f2488,f2502])).
% 2.31/0.68  fof(f2498,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) | spl2_8),
% 2.31/0.68    inference(superposition,[],[f2490,f418])).
% 2.31/0.68  fof(f418,plain,(
% 2.31/0.68    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 2.31/0.68    inference(forward_demodulation,[],[f393,f131])).
% 2.31/0.68  fof(f131,plain,(
% 2.31/0.68    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X10,X9),k2_xboole_0(X9,X10))) )),
% 2.31/0.68    inference(superposition,[],[f112,f28])).
% 2.31/0.68  fof(f28,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f6])).
% 2.31/0.68  fof(f6,axiom,(
% 2.31/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.31/0.68  fof(f112,plain,(
% 2.31/0.68    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.31/0.68    inference(superposition,[],[f83,f26])).
% 2.31/0.68  fof(f83,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.31/0.68    inference(superposition,[],[f33,f80])).
% 2.31/0.68  fof(f80,plain,(
% 2.31/0.68    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 2.31/0.68    inference(forward_demodulation,[],[f77,f24])).
% 2.31/0.68  fof(f24,plain,(
% 2.31/0.68    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.31/0.68    inference(cnf_transformation,[],[f4])).
% 2.31/0.68  fof(f4,axiom,(
% 2.31/0.68    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.31/0.68  fof(f77,plain,(
% 2.31/0.68    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1)) )),
% 2.31/0.68    inference(superposition,[],[f28,f72])).
% 2.31/0.68  fof(f72,plain,(
% 2.31/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.31/0.68    inference(backward_demodulation,[],[f36,f65])).
% 2.31/0.68  fof(f65,plain,(
% 2.31/0.68    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.31/0.68    inference(superposition,[],[f47,f24])).
% 2.31/0.68  fof(f47,plain,(
% 2.31/0.68    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 2.31/0.68    inference(forward_demodulation,[],[f37,f22])).
% 2.31/0.68  fof(f22,plain,(
% 2.31/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f11])).
% 2.31/0.68  fof(f11,axiom,(
% 2.31/0.68    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.31/0.68  fof(f37,plain,(
% 2.31/0.68    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.31/0.68    inference(definition_unfolding,[],[f23,f31])).
% 2.31/0.68  fof(f31,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f3])).
% 2.31/0.68  fof(f3,axiom,(
% 2.31/0.68    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.31/0.68  fof(f23,plain,(
% 2.31/0.68    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.31/0.68    inference(cnf_transformation,[],[f14])).
% 2.31/0.68  fof(f14,axiom,(
% 2.31/0.68    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.31/0.68  fof(f36,plain,(
% 2.31/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.31/0.68    inference(definition_unfolding,[],[f21,f27])).
% 2.31/0.68  fof(f27,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f9])).
% 2.31/0.68  fof(f9,axiom,(
% 2.31/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.31/0.68  fof(f21,plain,(
% 2.31/0.68    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f5])).
% 2.31/0.68  fof(f5,axiom,(
% 2.31/0.68    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.31/0.68  fof(f33,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f12])).
% 2.31/0.68  fof(f12,axiom,(
% 2.31/0.68    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.31/0.68  fof(f393,plain,(
% 2.31/0.68    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12))) )),
% 2.31/0.68    inference(superposition,[],[f239,f28])).
% 2.31/0.68  fof(f239,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 2.31/0.68    inference(superposition,[],[f183,f33])).
% 2.31/0.68  fof(f183,plain,(
% 2.31/0.68    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k2_xboole_0(X4,X5),X4)) )),
% 2.31/0.68    inference(forward_demodulation,[],[f178,f24])).
% 2.31/0.68  fof(f178,plain,(
% 2.31/0.68    ( ! [X4,X5] : (k2_xboole_0(k2_xboole_0(X4,X5),X4) = k2_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)) )),
% 2.31/0.68    inference(superposition,[],[f28,f161])).
% 2.31/0.68  fof(f161,plain,(
% 2.31/0.68    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.31/0.68    inference(forward_demodulation,[],[f152,f22])).
% 2.31/0.68  fof(f152,plain,(
% 2.31/0.68    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 2.31/0.68    inference(superposition,[],[f34,f72])).
% 2.31/0.68  fof(f34,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f7])).
% 2.31/0.68  fof(f7,axiom,(
% 2.31/0.68    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.31/0.68  fof(f2497,plain,(
% 2.31/0.68    ~spl2_9 | spl2_7),
% 2.31/0.68    inference(avatar_split_clause,[],[f2492,f2480,f2494])).
% 2.31/0.68  fof(f2494,plain,(
% 2.31/0.68    spl2_9 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.31/0.68  fof(f2480,plain,(
% 2.31/0.68    spl2_7 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.31/0.68  fof(f2492,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl2_7),
% 2.31/0.68    inference(forward_demodulation,[],[f2485,f40])).
% 2.31/0.68  fof(f40,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.31/0.68    inference(definition_unfolding,[],[f30,f27])).
% 2.31/0.68  fof(f30,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.31/0.68    inference(cnf_transformation,[],[f13])).
% 2.31/0.68  fof(f13,axiom,(
% 2.31/0.68    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.31/0.68  fof(f2485,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) | spl2_7),
% 2.31/0.68    inference(superposition,[],[f2482,f91])).
% 2.31/0.68  fof(f91,plain,(
% 2.31/0.68    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 2.31/0.68    inference(superposition,[],[f33,f26])).
% 2.31/0.68  fof(f2482,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_7),
% 2.31/0.68    inference(avatar_component_clause,[],[f2480])).
% 2.31/0.68  fof(f2491,plain,(
% 2.31/0.68    ~spl2_8 | spl2_7),
% 2.31/0.68    inference(avatar_split_clause,[],[f2486,f2480,f2488])).
% 2.31/0.68  fof(f2486,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) | spl2_7),
% 2.31/0.68    inference(forward_demodulation,[],[f2484,f838])).
% 2.31/0.68  fof(f838,plain,(
% 2.31/0.68    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = X6) )),
% 2.31/0.68    inference(backward_demodulation,[],[f351,f836])).
% 2.31/0.68  fof(f836,plain,(
% 2.31/0.68    ( ! [X19,X18] : (k2_xboole_0(X18,k4_xboole_0(X18,X19)) = X18) )),
% 2.31/0.68    inference(forward_demodulation,[],[f835,f831])).
% 2.31/0.68  fof(f831,plain,(
% 2.31/0.68    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5) )),
% 2.31/0.68    inference(forward_demodulation,[],[f809,f40])).
% 2.31/0.68  fof(f809,plain,(
% 2.31/0.68    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6))) )),
% 2.31/0.68    inference(superposition,[],[f28,f39])).
% 2.31/0.68  fof(f39,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.31/0.68    inference(definition_unfolding,[],[f29,f27])).
% 2.31/0.68  fof(f29,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f8])).
% 2.31/0.68  fof(f8,axiom,(
% 2.31/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.31/0.68  fof(f835,plain,(
% 2.31/0.68    ( ! [X19,X18] : (k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X18) = k2_xboole_0(X18,k4_xboole_0(X18,X19))) )),
% 2.31/0.68    inference(forward_demodulation,[],[f834,f26])).
% 2.31/0.68  fof(f834,plain,(
% 2.31/0.68    ( ! [X19,X18] : (k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X18) = k2_xboole_0(k4_xboole_0(X18,X19),X18)) )),
% 2.31/0.68    inference(forward_demodulation,[],[f813,f28])).
% 2.31/0.68  fof(f813,plain,(
% 2.31/0.68    ( ! [X19,X18] : (k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X18) = k2_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,k4_xboole_0(X18,X19)))) )),
% 2.31/0.68    inference(superposition,[],[f418,f39])).
% 2.31/0.68  fof(f351,plain,(
% 2.31/0.68    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 2.31/0.68    inference(forward_demodulation,[],[f330,f26])).
% 2.31/0.68  fof(f330,plain,(
% 2.31/0.68    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6)))) )),
% 2.31/0.68    inference(superposition,[],[f28,f38])).
% 2.31/0.68  fof(f38,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.31/0.68    inference(definition_unfolding,[],[f25,f27,f27])).
% 2.31/0.68  fof(f25,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f2])).
% 2.31/0.68  fof(f2,axiom,(
% 2.31/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.31/0.68  fof(f2484,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_7),
% 2.31/0.68    inference(superposition,[],[f2482,f91])).
% 2.31/0.68  fof(f2483,plain,(
% 2.31/0.68    ~spl2_7 | spl2_6),
% 2.31/0.68    inference(avatar_split_clause,[],[f2476,f2465,f2480])).
% 2.31/0.68  fof(f2465,plain,(
% 2.31/0.68    spl2_6 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.31/0.68  fof(f2476,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_6),
% 2.31/0.68    inference(superposition,[],[f2467,f418])).
% 2.31/0.68  fof(f2467,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_6),
% 2.31/0.68    inference(avatar_component_clause,[],[f2465])).
% 2.31/0.68  fof(f2468,plain,(
% 2.31/0.68    ~spl2_6 | spl2_3),
% 2.31/0.68    inference(avatar_split_clause,[],[f2458,f102,f2465])).
% 2.31/0.68  fof(f102,plain,(
% 2.31/0.68    spl2_3 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.31/0.68  fof(f2458,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 2.31/0.68    inference(backward_demodulation,[],[f104,f2409])).
% 2.31/0.68  fof(f2409,plain,(
% 2.31/0.68    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k4_xboole_0(X9,k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)))) )),
% 2.31/0.68    inference(superposition,[],[f48,f802])).
% 2.31/0.68  fof(f802,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 2.31/0.68    inference(superposition,[],[f39,f38])).
% 2.31/0.68  fof(f48,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 2.31/0.68    inference(backward_demodulation,[],[f41,f34])).
% 2.31/0.68  fof(f41,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.31/0.68    inference(definition_unfolding,[],[f32,f27,f27])).
% 2.31/0.68  fof(f32,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f10])).
% 2.31/0.68  fof(f10,axiom,(
% 2.31/0.68    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.31/0.68  fof(f104,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_3),
% 2.31/0.68    inference(avatar_component_clause,[],[f102])).
% 2.31/0.68  fof(f2463,plain,(
% 2.31/0.68    ~spl2_5 | spl2_4),
% 2.31/0.68    inference(avatar_split_clause,[],[f2457,f146,f2460])).
% 2.31/0.68  fof(f2460,plain,(
% 2.31/0.68    spl2_5 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.31/0.68  fof(f146,plain,(
% 2.31/0.68    spl2_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.31/0.68  fof(f2457,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_4),
% 2.31/0.68    inference(backward_demodulation,[],[f148,f2409])).
% 2.31/0.68  fof(f148,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_4),
% 2.31/0.68    inference(avatar_component_clause,[],[f146])).
% 2.31/0.68  fof(f150,plain,(
% 2.31/0.68    ~spl2_4 | spl2_3),
% 2.31/0.68    inference(avatar_split_clause,[],[f144,f102,f146])).
% 2.31/0.68  fof(f144,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_3),
% 2.31/0.68    inference(superposition,[],[f104,f26])).
% 2.31/0.68  fof(f149,plain,(
% 2.31/0.68    ~spl2_4 | spl2_3),
% 2.31/0.68    inference(avatar_split_clause,[],[f143,f102,f146])).
% 2.31/0.68  fof(f143,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_3),
% 2.31/0.68    inference(superposition,[],[f104,f26])).
% 2.31/0.68  fof(f105,plain,(
% 2.31/0.68    ~spl2_3 | spl2_2),
% 2.31/0.68    inference(avatar_split_clause,[],[f100,f51,f102])).
% 2.31/0.68  fof(f51,plain,(
% 2.31/0.68    spl2_2 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.31/0.68  fof(f100,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_2),
% 2.31/0.68    inference(backward_demodulation,[],[f53,f83])).
% 2.31/0.68  fof(f53,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_2),
% 2.31/0.68    inference(avatar_component_clause,[],[f51])).
% 2.31/0.68  fof(f54,plain,(
% 2.31/0.68    ~spl2_2 | spl2_1),
% 2.31/0.68    inference(avatar_split_clause,[],[f49,f43,f51])).
% 2.31/0.68  fof(f43,plain,(
% 2.31/0.68    spl2_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.31/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.31/0.68  fof(f49,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_1),
% 2.31/0.68    inference(forward_demodulation,[],[f45,f34])).
% 2.31/0.68  fof(f45,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 2.31/0.68    inference(avatar_component_clause,[],[f43])).
% 2.31/0.68  fof(f46,plain,(
% 2.31/0.68    ~spl2_1),
% 2.31/0.68    inference(avatar_split_clause,[],[f35,f43])).
% 2.31/0.68  fof(f35,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.31/0.68    inference(definition_unfolding,[],[f20,f31,f31,f27])).
% 2.31/0.68  fof(f20,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.31/0.68    inference(cnf_transformation,[],[f19])).
% 2.31/0.68  fof(f19,plain,(
% 2.31/0.68    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.31/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 2.31/0.68  fof(f18,plain,(
% 2.31/0.68    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.31/0.68    introduced(choice_axiom,[])).
% 2.31/0.68  fof(f17,plain,(
% 2.31/0.68    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.31/0.68    inference(ennf_transformation,[],[f16])).
% 2.31/0.68  fof(f16,negated_conjecture,(
% 2.31/0.68    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.31/0.68    inference(negated_conjecture,[],[f15])).
% 2.31/0.68  fof(f15,conjecture,(
% 2.31/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.31/0.68  % SZS output end Proof for theBenchmark
% 2.31/0.68  % (16745)------------------------------
% 2.31/0.68  % (16745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.31/0.68  % (16745)Termination reason: Refutation
% 2.31/0.68  
% 2.31/0.68  % (16745)Memory used [KB]: 8059
% 2.31/0.68  % (16745)Time elapsed: 0.241 s
% 2.31/0.68  % (16745)------------------------------
% 2.31/0.68  % (16745)------------------------------
% 2.31/0.68  % (16734)Success in time 0.315 s
%------------------------------------------------------------------------------
