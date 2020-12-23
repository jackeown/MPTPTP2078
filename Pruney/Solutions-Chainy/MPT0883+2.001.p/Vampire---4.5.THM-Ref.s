%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:54 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 391 expanded)
%              Number of leaves         :   15 ( 141 expanded)
%              Depth                    :   14
%              Number of atoms          :   86 ( 426 expanded)
%              Number of equality atoms :   71 ( 408 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2606,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f2572,f2604])).

fof(f2604,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f2603])).

fof(f2603,plain,
    ( $false
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f2602])).

fof(f2602,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4))
    | spl5_2 ),
    inference(forward_demodulation,[],[f2584,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) ),
    inference(definition_unfolding,[],[f34,f22,f22,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f2584,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k1_tarski(sK4))
    | spl5_2 ),
    inference(superposition,[],[f2571,f230])).

fof(f230,plain,(
    ! [X10,X11,X9] : k2_zfmisc_1(k2_xboole_0(k1_tarski(X9),X11),k1_tarski(X10)) = k2_xboole_0(k1_tarski(k4_tarski(X9,X10)),k2_zfmisc_1(X11,k1_tarski(X10))) ),
    inference(superposition,[],[f28,f87])).

fof(f87,plain,(
    ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f77,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f77,plain,(
    ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_enumset1(X3,X3,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f41,f36])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_tarski(X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f31,f22,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f2571,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k1_tarski(sK4)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f2569])).

fof(f2569,plain,
    ( spl5_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k1_tarski(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2572,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2565,f117,f2569])).

fof(f117,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2565,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k1_tarski(sK4)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f2563,f2558])).

fof(f2558,plain,(
    ! [X14,X12,X15,X13] : k2_zfmisc_1(k1_enumset1(X13,X12,X15),k1_tarski(X14)) = k2_zfmisc_1(k1_enumset1(X12,X13,X15),k1_tarski(X14)) ),
    inference(forward_demodulation,[],[f2557,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f27,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f2557,plain,(
    ! [X14,X12,X15,X13] : k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_zfmisc_1(k1_enumset1(X13,X12,X15),k1_tarski(X14)) ),
    inference(forward_demodulation,[],[f2556,f2552])).

fof(f2552,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(k4_tarski(X3,X2))) = k2_zfmisc_1(k1_enumset1(X0,X1,X3),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f2551,f40])).

fof(f2551,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_xboole_0(k1_enumset1(X0,X0,X1),k1_tarski(X3)),k1_tarski(X2)) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(k4_tarski(X3,X2))) ),
    inference(forward_demodulation,[],[f2537,f1143])).

fof(f1143,plain,(
    ! [X41,X42,X40] : k2_xboole_0(k1_tarski(k4_tarski(X40,X41)),k1_tarski(k4_tarski(X42,X41))) = k2_zfmisc_1(k2_xboole_0(k1_tarski(X40),k1_tarski(X42)),k1_tarski(X41)) ),
    inference(backward_demodulation,[],[f394,f1142])).

fof(f1142,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),k1_tarski(X1)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k2_zfmisc_1(k1_enumset1(X2,X2,X0),k1_tarski(X1))) ),
    inference(forward_demodulation,[],[f1141,f229])).

fof(f229,plain,(
    ! [X6,X8,X7] : k2_zfmisc_1(k2_xboole_0(X8,k1_tarski(X6)),k1_tarski(X7)) = k2_xboole_0(k2_zfmisc_1(X8,k1_tarski(X7)),k1_tarski(k4_tarski(X6,X7))) ),
    inference(superposition,[],[f28,f87])).

fof(f1141,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k2_zfmisc_1(k1_enumset1(X2,X2,X0),k1_tarski(X1))) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)),k1_tarski(k4_tarski(X2,X1))) ),
    inference(forward_demodulation,[],[f1112,f36])).

fof(f1112,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k2_zfmisc_1(k1_enumset1(X2,X2,X0),k1_tarski(X1))) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_tarski(X1)),k1_tarski(k4_tarski(X2,X1))) ),
    inference(superposition,[],[f86,f78])).

fof(f78,plain,(
    ! [X6,X7,X5] : k1_enumset1(k4_tarski(X7,X6),k4_tarski(X7,X6),k4_tarski(X5,X6)) = k2_zfmisc_1(k1_enumset1(X5,X5,X7),k1_tarski(X6)) ),
    inference(superposition,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f86,plain,(
    ! [X21,X19,X22,X20] : k2_xboole_0(k1_tarski(k4_tarski(X19,X20)),k1_enumset1(k4_tarski(X19,X20),k4_tarski(X21,X20),X22)) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(X19,X19,X21),k1_tarski(X20)),k1_tarski(X22)) ),
    inference(superposition,[],[f43,f41])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f394,plain,(
    ! [X41,X42,X40] : k2_xboole_0(k1_tarski(k4_tarski(X40,X41)),k1_tarski(k4_tarski(X42,X41))) = k2_xboole_0(k1_tarski(k4_tarski(X40,X41)),k2_zfmisc_1(k1_enumset1(X42,X42,X40),k1_tarski(X41))) ),
    inference(superposition,[],[f70,f78])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[],[f43,f36])).

fof(f2537,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_xboole_0(k1_enumset1(X0,X0,X1),k1_tarski(X3)),k1_tarski(X2)) = k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2))),k1_tarski(k4_tarski(X3,X2))) ),
    inference(superposition,[],[f229,f199])).

fof(f199,plain,(
    ! [X10,X8,X9] : k2_zfmisc_1(k1_enumset1(X8,X8,X10),k1_tarski(X9)) = k2_xboole_0(k1_tarski(k4_tarski(X8,X9)),k1_tarski(k4_tarski(X10,X9))) ),
    inference(superposition,[],[f51,f41])).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f40,f36])).

fof(f2556,plain,(
    ! [X14,X12,X15,X13] : k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(X13),k1_tarski(X12)),k1_tarski(X14)),k1_tarski(k4_tarski(X15,X14))) ),
    inference(forward_demodulation,[],[f2555,f1143])).

fof(f2555,plain,(
    ! [X14,X12,X15,X13] : k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(X13,X14)),k1_tarski(k4_tarski(X12,X14))),k1_tarski(k4_tarski(X15,X14))) ),
    inference(forward_demodulation,[],[f2540,f51])).

fof(f2540,plain,(
    ! [X14,X12,X15,X13] : k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_xboole_0(k1_enumset1(k4_tarski(X13,X14),k4_tarski(X13,X14),k4_tarski(X12,X14)),k1_tarski(k4_tarski(X15,X14))) ),
    inference(superposition,[],[f229,f78])).

fof(f2563,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)),k1_tarski(sK4)))
    | spl5_1 ),
    inference(backward_demodulation,[],[f119,f2562])).

fof(f2562,plain,(
    ! [X6,X8,X7,X5] : k1_enumset1(k4_tarski(X5,X7),k4_tarski(X6,X7),k4_tarski(X8,X7)) = k2_zfmisc_1(k1_enumset1(X5,X6,X8),k1_tarski(X7)) ),
    inference(forward_demodulation,[],[f2544,f40])).

fof(f2544,plain,(
    ! [X6,X8,X7,X5] : k1_enumset1(k4_tarski(X5,X7),k4_tarski(X6,X7),k4_tarski(X8,X7)) = k2_zfmisc_1(k2_xboole_0(k1_enumset1(X5,X5,X6),k1_tarski(X8)),k1_tarski(X7)) ),
    inference(superposition,[],[f229,f81])).

fof(f81,plain,(
    ! [X4,X2,X5,X3] : k1_enumset1(k4_tarski(X2,X3),k4_tarski(X4,X3),X5) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(X2,X2,X4),k1_tarski(X3)),k1_tarski(X5)) ),
    inference(superposition,[],[f40,f41])).

fof(f119,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f120,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f117])).

fof(f38,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) ),
    inference(definition_unfolding,[],[f19,f24,f22,f22,f32,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (24955)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (24946)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (24940)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (24939)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (24941)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (24943)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (24951)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (24949)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (24953)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (24944)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (24945)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (24942)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (24948)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (24950)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (24954)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (24950)Refutation not found, incomplete strategy% (24950)------------------------------
% 0.22/0.51  % (24950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24950)Memory used [KB]: 10618
% 0.22/0.51  % (24950)Time elapsed: 0.083 s
% 0.22/0.51  % (24950)------------------------------
% 0.22/0.51  % (24950)------------------------------
% 0.22/0.51  % (24947)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (24952)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (24956)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.38/0.70  % (24954)Refutation found. Thanks to Tanya!
% 2.38/0.70  % SZS status Theorem for theBenchmark
% 2.38/0.70  % SZS output start Proof for theBenchmark
% 2.38/0.70  fof(f2606,plain,(
% 2.38/0.70    $false),
% 2.38/0.70    inference(avatar_sat_refutation,[],[f120,f2572,f2604])).
% 2.38/0.70  fof(f2604,plain,(
% 2.38/0.70    spl5_2),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f2603])).
% 2.38/0.70  fof(f2603,plain,(
% 2.38/0.70    $false | spl5_2),
% 2.38/0.70    inference(trivial_inequality_removal,[],[f2602])).
% 2.38/0.70  fof(f2602,plain,(
% 2.38/0.70    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) | spl5_2),
% 2.38/0.70    inference(forward_demodulation,[],[f2584,f44])).
% 2.38/0.70  fof(f44,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)))) )),
% 2.38/0.70    inference(definition_unfolding,[],[f34,f22,f22,f32])).
% 2.38/0.70  fof(f32,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f4])).
% 2.38/0.70  fof(f4,axiom,(
% 2.38/0.70    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 2.38/0.70  fof(f22,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f7])).
% 2.38/0.70  fof(f7,axiom,(
% 2.38/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.38/0.70  fof(f34,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f10])).
% 2.38/0.70  fof(f10,axiom,(
% 2.38/0.70    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 2.38/0.70  fof(f2584,plain,(
% 2.38/0.70    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k1_tarski(sK4)) | spl5_2),
% 2.38/0.70    inference(superposition,[],[f2571,f230])).
% 2.38/0.70  fof(f230,plain,(
% 2.38/0.70    ( ! [X10,X11,X9] : (k2_zfmisc_1(k2_xboole_0(k1_tarski(X9),X11),k1_tarski(X10)) = k2_xboole_0(k1_tarski(k4_tarski(X9,X10)),k2_zfmisc_1(X11,k1_tarski(X10)))) )),
% 2.38/0.70    inference(superposition,[],[f28,f87])).
% 2.38/0.70  fof(f87,plain,(
% 2.38/0.70    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f77,f36])).
% 2.38/0.70  fof(f36,plain,(
% 2.38/0.70    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.38/0.70    inference(definition_unfolding,[],[f20,f22])).
% 2.38/0.70  fof(f20,plain,(
% 2.38/0.70    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f6])).
% 2.38/0.70  fof(f6,axiom,(
% 2.38/0.70    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.38/0.70  fof(f77,plain,(
% 2.38/0.70    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_enumset1(X3,X3,X3),k1_tarski(X4))) )),
% 2.38/0.70    inference(superposition,[],[f41,f36])).
% 2.38/0.70  fof(f41,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_tarski(X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 2.38/0.70    inference(definition_unfolding,[],[f31,f22,f22])).
% 2.38/0.70  fof(f31,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f11])).
% 2.38/0.70  fof(f11,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 2.38/0.70  fof(f28,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f9])).
% 2.38/0.70  fof(f9,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.38/0.70  fof(f2571,plain,(
% 2.38/0.70    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k1_tarski(sK4))) | spl5_2),
% 2.38/0.70    inference(avatar_component_clause,[],[f2569])).
% 2.38/0.70  fof(f2569,plain,(
% 2.38/0.70    spl5_2 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k1_tarski(sK4)))),
% 2.38/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.38/0.70  fof(f2572,plain,(
% 2.38/0.70    ~spl5_2 | spl5_1),
% 2.38/0.70    inference(avatar_split_clause,[],[f2565,f117,f2569])).
% 2.38/0.70  fof(f117,plain,(
% 2.38/0.70    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)))),
% 2.38/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.38/0.70  fof(f2565,plain,(
% 2.38/0.70    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k1_tarski(sK4))) | spl5_1),
% 2.38/0.70    inference(forward_demodulation,[],[f2563,f2558])).
% 2.38/0.70  fof(f2558,plain,(
% 2.38/0.70    ( ! [X14,X12,X15,X13] : (k2_zfmisc_1(k1_enumset1(X13,X12,X15),k1_tarski(X14)) = k2_zfmisc_1(k1_enumset1(X12,X13,X15),k1_tarski(X14))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f2557,f40])).
% 2.38/0.70  fof(f40,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_tarski(X2))) )),
% 2.38/0.70    inference(definition_unfolding,[],[f27,f22])).
% 2.38/0.70  fof(f27,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f3])).
% 2.38/0.70  fof(f3,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 2.38/0.70  fof(f2557,plain,(
% 2.38/0.70    ( ! [X14,X12,X15,X13] : (k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_zfmisc_1(k1_enumset1(X13,X12,X15),k1_tarski(X14))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f2556,f2552])).
% 2.38/0.70  fof(f2552,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(k4_tarski(X3,X2))) = k2_zfmisc_1(k1_enumset1(X0,X1,X3),k1_tarski(X2))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f2551,f40])).
% 2.38/0.70  fof(f2551,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_xboole_0(k1_enumset1(X0,X0,X1),k1_tarski(X3)),k1_tarski(X2)) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(k4_tarski(X3,X2)))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f2537,f1143])).
% 2.38/0.70  fof(f1143,plain,(
% 2.38/0.70    ( ! [X41,X42,X40] : (k2_xboole_0(k1_tarski(k4_tarski(X40,X41)),k1_tarski(k4_tarski(X42,X41))) = k2_zfmisc_1(k2_xboole_0(k1_tarski(X40),k1_tarski(X42)),k1_tarski(X41))) )),
% 2.38/0.70    inference(backward_demodulation,[],[f394,f1142])).
% 2.38/0.70  fof(f1142,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),k1_tarski(X1)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k2_zfmisc_1(k1_enumset1(X2,X2,X0),k1_tarski(X1)))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f1141,f229])).
% 2.38/0.70  fof(f229,plain,(
% 2.38/0.70    ( ! [X6,X8,X7] : (k2_zfmisc_1(k2_xboole_0(X8,k1_tarski(X6)),k1_tarski(X7)) = k2_xboole_0(k2_zfmisc_1(X8,k1_tarski(X7)),k1_tarski(k4_tarski(X6,X7)))) )),
% 2.38/0.70    inference(superposition,[],[f28,f87])).
% 2.38/0.70  fof(f1141,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k2_zfmisc_1(k1_enumset1(X2,X2,X0),k1_tarski(X1))) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)),k1_tarski(k4_tarski(X2,X1)))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f1112,f36])).
% 2.38/0.70  fof(f1112,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k2_zfmisc_1(k1_enumset1(X2,X2,X0),k1_tarski(X1))) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_tarski(X1)),k1_tarski(k4_tarski(X2,X1)))) )),
% 2.38/0.70    inference(superposition,[],[f86,f78])).
% 2.38/0.70  fof(f78,plain,(
% 2.38/0.70    ( ! [X6,X7,X5] : (k1_enumset1(k4_tarski(X7,X6),k4_tarski(X7,X6),k4_tarski(X5,X6)) = k2_zfmisc_1(k1_enumset1(X5,X5,X7),k1_tarski(X6))) )),
% 2.38/0.70    inference(superposition,[],[f41,f39])).
% 2.38/0.70  fof(f39,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.38/0.70    inference(definition_unfolding,[],[f21,f22,f22])).
% 2.38/0.70  fof(f21,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f1])).
% 2.38/0.70  fof(f1,axiom,(
% 2.38/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.38/0.70  fof(f86,plain,(
% 2.38/0.70    ( ! [X21,X19,X22,X20] : (k2_xboole_0(k1_tarski(k4_tarski(X19,X20)),k1_enumset1(k4_tarski(X19,X20),k4_tarski(X21,X20),X22)) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(X19,X19,X21),k1_tarski(X20)),k1_tarski(X22))) )),
% 2.38/0.70    inference(superposition,[],[f43,f41])).
% 2.38/0.70  fof(f43,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.38/0.70    inference(definition_unfolding,[],[f33,f32])).
% 2.38/0.70  fof(f33,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f5])).
% 2.38/0.70  fof(f5,axiom,(
% 2.38/0.70    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 2.38/0.70  fof(f394,plain,(
% 2.38/0.70    ( ! [X41,X42,X40] : (k2_xboole_0(k1_tarski(k4_tarski(X40,X41)),k1_tarski(k4_tarski(X42,X41))) = k2_xboole_0(k1_tarski(k4_tarski(X40,X41)),k2_zfmisc_1(k1_enumset1(X42,X42,X40),k1_tarski(X41)))) )),
% 2.38/0.70    inference(superposition,[],[f70,f78])).
% 2.38/0.70  fof(f70,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1))) )),
% 2.38/0.70    inference(superposition,[],[f43,f36])).
% 2.38/0.70  fof(f2537,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_xboole_0(k1_enumset1(X0,X0,X1),k1_tarski(X3)),k1_tarski(X2)) = k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2))),k1_tarski(k4_tarski(X3,X2)))) )),
% 2.38/0.70    inference(superposition,[],[f229,f199])).
% 2.38/0.70  fof(f199,plain,(
% 2.38/0.70    ( ! [X10,X8,X9] : (k2_zfmisc_1(k1_enumset1(X8,X8,X10),k1_tarski(X9)) = k2_xboole_0(k1_tarski(k4_tarski(X8,X9)),k1_tarski(k4_tarski(X10,X9)))) )),
% 2.38/0.70    inference(superposition,[],[f51,f41])).
% 2.38/0.70  fof(f51,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.38/0.70    inference(superposition,[],[f40,f36])).
% 2.38/0.70  fof(f2556,plain,(
% 2.38/0.70    ( ! [X14,X12,X15,X13] : (k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(X13),k1_tarski(X12)),k1_tarski(X14)),k1_tarski(k4_tarski(X15,X14)))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f2555,f1143])).
% 2.38/0.70  fof(f2555,plain,(
% 2.38/0.70    ( ! [X14,X12,X15,X13] : (k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(X13,X14)),k1_tarski(k4_tarski(X12,X14))),k1_tarski(k4_tarski(X15,X14)))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f2540,f51])).
% 2.38/0.70  fof(f2540,plain,(
% 2.38/0.70    ( ! [X14,X12,X15,X13] : (k2_zfmisc_1(k2_xboole_0(k1_enumset1(X12,X12,X13),k1_tarski(X15)),k1_tarski(X14)) = k2_xboole_0(k1_enumset1(k4_tarski(X13,X14),k4_tarski(X13,X14),k4_tarski(X12,X14)),k1_tarski(k4_tarski(X15,X14)))) )),
% 2.38/0.70    inference(superposition,[],[f229,f78])).
% 2.38/0.70  fof(f2563,plain,(
% 2.38/0.70    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)),k1_tarski(sK4))) | spl5_1),
% 2.38/0.70    inference(backward_demodulation,[],[f119,f2562])).
% 2.38/0.70  fof(f2562,plain,(
% 2.38/0.70    ( ! [X6,X8,X7,X5] : (k1_enumset1(k4_tarski(X5,X7),k4_tarski(X6,X7),k4_tarski(X8,X7)) = k2_zfmisc_1(k1_enumset1(X5,X6,X8),k1_tarski(X7))) )),
% 2.38/0.70    inference(forward_demodulation,[],[f2544,f40])).
% 2.38/0.70  fof(f2544,plain,(
% 2.38/0.70    ( ! [X6,X8,X7,X5] : (k1_enumset1(k4_tarski(X5,X7),k4_tarski(X6,X7),k4_tarski(X8,X7)) = k2_zfmisc_1(k2_xboole_0(k1_enumset1(X5,X5,X6),k1_tarski(X8)),k1_tarski(X7))) )),
% 2.38/0.70    inference(superposition,[],[f229,f81])).
% 2.38/0.70  fof(f81,plain,(
% 2.38/0.70    ( ! [X4,X2,X5,X3] : (k1_enumset1(k4_tarski(X2,X3),k4_tarski(X4,X3),X5) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(X2,X2,X4),k1_tarski(X3)),k1_tarski(X5))) )),
% 2.38/0.70    inference(superposition,[],[f40,f41])).
% 2.38/0.70  fof(f119,plain,(
% 2.38/0.70    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) | spl5_1),
% 2.38/0.70    inference(avatar_component_clause,[],[f117])).
% 2.38/0.70  fof(f120,plain,(
% 2.38/0.70    ~spl5_1),
% 2.38/0.70    inference(avatar_split_clause,[],[f38,f117])).
% 2.38/0.70  fof(f38,plain,(
% 2.38/0.70    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)))),
% 2.38/0.70    inference(definition_unfolding,[],[f19,f24,f22,f22,f32,f25,f25,f25,f25])).
% 2.38/0.70  fof(f25,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f12])).
% 2.38/0.70  fof(f12,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.38/0.70  fof(f24,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f13])).
% 2.38/0.70  fof(f13,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.38/0.70  fof(f19,plain,(
% 2.38/0.70    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 2.38/0.70    inference(cnf_transformation,[],[f18])).
% 2.38/0.70  fof(f18,plain,(
% 2.38/0.70    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 2.38/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 2.38/0.70  fof(f17,plain,(
% 2.38/0.70    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 2.38/0.70    introduced(choice_axiom,[])).
% 2.38/0.70  fof(f16,plain,(
% 2.38/0.70    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 2.38/0.70    inference(ennf_transformation,[],[f15])).
% 2.38/0.70  fof(f15,negated_conjecture,(
% 2.38/0.70    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 2.38/0.70    inference(negated_conjecture,[],[f14])).
% 2.38/0.70  fof(f14,conjecture,(
% 2.38/0.70    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_mcart_1)).
% 2.38/0.70  % SZS output end Proof for theBenchmark
% 2.38/0.70  % (24954)------------------------------
% 2.38/0.70  % (24954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.70  % (24954)Termination reason: Refutation
% 2.38/0.70  
% 2.38/0.70  % (24954)Memory used [KB]: 12792
% 2.38/0.70  % (24954)Time elapsed: 0.235 s
% 2.38/0.70  % (24954)------------------------------
% 2.38/0.70  % (24954)------------------------------
% 2.38/0.71  % (24938)Success in time 0.338 s
%------------------------------------------------------------------------------
