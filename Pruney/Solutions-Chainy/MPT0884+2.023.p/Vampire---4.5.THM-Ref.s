%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:58 EST 2020

% Result     : Theorem 3.79s
% Output     : Refutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 427 expanded)
%              Number of leaves         :   19 ( 166 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 458 expanded)
%              Number of equality atoms :   70 ( 426 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2997,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f83,f1891,f2992,f2996])).

fof(f2996,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f2995])).

fof(f2995,plain,
    ( $false
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f2994])).

fof(f2994,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
    | spl5_4 ),
    inference(forward_demodulation,[],[f2993,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f30,f22,f39,f22])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f2993,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | spl5_4 ),
    inference(superposition,[],[f2991,f144])).

fof(f144,plain,(
    ! [X12,X10,X8,X11,X9] : k2_zfmisc_1(k1_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),X10),k1_enumset1(X11,X11,X12)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X8,X8,X8),k1_enumset1(X9,X9,X9)),k1_enumset1(X11,X11,X11)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X8,X8,X8),k1_enumset1(X9,X9,X9)),k1_enumset1(X11,X11,X11)),k1_enumset1(k4_tarski(k4_tarski(X8,X9),X12),k4_tarski(X10,X11),k4_tarski(X10,X12)))) ),
    inference(superposition,[],[f131,f45])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)))) ),
    inference(forward_demodulation,[],[f48,f45])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)))) ),
    inference(definition_unfolding,[],[f33,f22,f22,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f34,f36,f22])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f2991,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f2989])).

fof(f2989,plain,
    ( spl5_4
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2992,plain,
    ( ~ spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f2691,f1888,f2989])).

fof(f1888,plain,
    ( spl5_3
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f2691,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_3 ),
    inference(backward_demodulation,[],[f1890,f2666])).

fof(f2666,plain,(
    ! [X14,X12,X13] : k1_enumset1(X12,X13,X14) = k1_enumset1(X12,X14,X13) ),
    inference(superposition,[],[f162,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k1_enumset1(X1,X0,X1))) = k1_enumset1(X2,X0,X1) ),
    inference(forward_demodulation,[],[f91,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f27,f36,f22,f39])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X0),k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X1))) = k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k1_enumset1(X1,X0,X1))) ),
    inference(superposition,[],[f47,f54])).

fof(f54,plain,(
    ! [X2,X1] : k1_enumset1(X1,X2,X2) = k1_enumset1(X2,X1,X2) ),
    inference(superposition,[],[f44,f43])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f28,f36,f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f32,f38,f36,f22,f22])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f162,plain,(
    ! [X47,X48,X46] : k1_enumset1(X48,X46,X47) = k3_tarski(k1_enumset1(k1_enumset1(X48,X48,X48),k1_enumset1(X48,X48,X48),k1_enumset1(X46,X47,X46))) ),
    inference(superposition,[],[f98,f136])).

fof(f136,plain,(
    ! [X2,X3] : k1_enumset1(X2,X2,X3) = k1_enumset1(X2,X3,X2) ),
    inference(superposition,[],[f98,f44])).

fof(f98,plain,(
    ! [X6,X8,X7] : k1_enumset1(X6,X7,X8) = k3_tarski(k1_enumset1(k1_enumset1(X6,X6,X6),k1_enumset1(X6,X6,X6),k1_enumset1(X7,X7,X8))) ),
    inference(superposition,[],[f47,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f1890,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f1888])).

fof(f1891,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1626,f80,f1888])).

fof(f80,plain,
    ( spl5_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1626,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3))))
    | spl5_2 ),
    inference(backward_demodulation,[],[f82,f1611])).

fof(f1611,plain,(
    ! [X10,X11,X9] : k1_enumset1(X10,X9,X11) = k1_enumset1(X9,X11,X10) ),
    inference(superposition,[],[f115,f105])).

fof(f105,plain,(
    ! [X2,X3,X1] : k1_enumset1(X2,X1,X3) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X2))) ),
    inference(superposition,[],[f47,f44])).

fof(f82,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f78,f50,f80])).

fof(f50,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f78,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f77,f45])).

fof(f77,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f52,f45])).

fof(f52,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f42,f50])).

fof(f42,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    inference(definition_unfolding,[],[f20,f24,f22,f39,f22,f38,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (4698)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (4697)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (4696)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (4708)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (4695)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (4705)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (4699)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (4704)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (4704)Refutation not found, incomplete strategy% (4704)------------------------------
% 0.21/0.48  % (4704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4704)Memory used [KB]: 10618
% 0.21/0.48  % (4704)Time elapsed: 0.071 s
% 0.21/0.48  % (4704)------------------------------
% 0.21/0.48  % (4704)------------------------------
% 0.21/0.48  % (4706)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (4702)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (4701)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (4700)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (4703)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (4693)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (4707)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.31/0.52  % (4710)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.31/0.52  % (4694)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.31/0.53  % (4709)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.79/0.92  % (4699)Refutation found. Thanks to Tanya!
% 3.79/0.92  % SZS status Theorem for theBenchmark
% 3.79/0.92  % SZS output start Proof for theBenchmark
% 3.79/0.92  fof(f2997,plain,(
% 3.79/0.92    $false),
% 3.79/0.92    inference(avatar_sat_refutation,[],[f53,f83,f1891,f2992,f2996])).
% 3.79/0.92  fof(f2996,plain,(
% 3.79/0.92    spl5_4),
% 3.79/0.92    inference(avatar_contradiction_clause,[],[f2995])).
% 3.79/0.92  fof(f2995,plain,(
% 3.79/0.92    $false | spl5_4),
% 3.79/0.92    inference(trivial_inequality_removal,[],[f2994])).
% 3.79/0.92  fof(f2994,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) | spl5_4),
% 3.79/0.92    inference(forward_demodulation,[],[f2993,f45])).
% 3.79/0.92  fof(f45,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f30,f22,f39,f22])).
% 3.79/0.92  fof(f39,plain,(
% 3.79/0.92    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.79/0.92    inference(definition_unfolding,[],[f21,f22])).
% 3.79/0.92  fof(f21,plain,(
% 3.79/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f6])).
% 3.79/0.92  fof(f6,axiom,(
% 3.79/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.79/0.92  fof(f22,plain,(
% 3.79/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f7])).
% 3.79/0.92  fof(f7,axiom,(
% 3.79/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.79/0.92  fof(f30,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 3.79/0.92    inference(cnf_transformation,[],[f12])).
% 3.79/0.92  fof(f12,axiom,(
% 3.79/0.92    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 3.79/0.92  fof(f2993,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) | spl5_4),
% 3.79/0.92    inference(superposition,[],[f2991,f144])).
% 3.79/0.92  fof(f144,plain,(
% 3.79/0.92    ( ! [X12,X10,X8,X11,X9] : (k2_zfmisc_1(k1_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),X10),k1_enumset1(X11,X11,X12)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X8,X8,X8),k1_enumset1(X9,X9,X9)),k1_enumset1(X11,X11,X11)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X8,X8,X8),k1_enumset1(X9,X9,X9)),k1_enumset1(X11,X11,X11)),k1_enumset1(k4_tarski(k4_tarski(X8,X9),X12),k4_tarski(X10,X11),k4_tarski(X10,X12))))) )),
% 3.79/0.92    inference(superposition,[],[f131,f45])).
% 3.79/0.92  fof(f131,plain,(
% 3.79/0.92    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))))) )),
% 3.79/0.92    inference(forward_demodulation,[],[f48,f45])).
% 3.79/0.92  fof(f48,plain,(
% 3.79/0.92    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f33,f22,f22,f38])).
% 3.79/0.92  fof(f38,plain,(
% 3.79/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f31,f37])).
% 3.79/0.92  fof(f37,plain,(
% 3.79/0.92    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f34,f36,f22])).
% 3.79/0.92  fof(f36,plain,(
% 3.79/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f23,f22])).
% 3.79/0.92  fof(f23,plain,(
% 3.79/0.92    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f10])).
% 3.79/0.92  fof(f10,axiom,(
% 3.79/0.92    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.79/0.92  fof(f34,plain,(
% 3.79/0.92    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 3.79/0.92    inference(cnf_transformation,[],[f4])).
% 3.79/0.92  fof(f4,axiom,(
% 3.79/0.92    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 3.79/0.92  fof(f31,plain,(
% 3.79/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f9])).
% 3.79/0.92  fof(f9,axiom,(
% 3.79/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.79/0.92  fof(f33,plain,(
% 3.79/0.92    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 3.79/0.92    inference(cnf_transformation,[],[f11])).
% 3.79/0.92  fof(f11,axiom,(
% 3.79/0.92    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 3.79/0.92  fof(f2991,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_4),
% 3.79/0.92    inference(avatar_component_clause,[],[f2989])).
% 3.79/0.92  fof(f2989,plain,(
% 3.79/0.92    spl5_4 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 3.79/0.92    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.79/0.92  fof(f2992,plain,(
% 3.79/0.92    ~spl5_4 | spl5_3),
% 3.79/0.92    inference(avatar_split_clause,[],[f2691,f1888,f2989])).
% 3.79/0.92  fof(f1888,plain,(
% 3.79/0.92    spl5_3 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3))))),
% 3.79/0.92    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.79/0.92  fof(f2691,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_3),
% 3.79/0.92    inference(backward_demodulation,[],[f1890,f2666])).
% 3.79/0.92  fof(f2666,plain,(
% 3.79/0.92    ( ! [X14,X12,X13] : (k1_enumset1(X12,X13,X14) = k1_enumset1(X12,X14,X13)) )),
% 3.79/0.92    inference(superposition,[],[f162,f115])).
% 3.79/0.92  fof(f115,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k1_enumset1(X1,X0,X1))) = k1_enumset1(X2,X0,X1)) )),
% 3.79/0.92    inference(forward_demodulation,[],[f91,f43])).
% 3.79/0.92  fof(f43,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f27,f36,f22,f39])).
% 3.79/0.92  fof(f27,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.79/0.92    inference(cnf_transformation,[],[f3])).
% 3.79/0.92  fof(f3,axiom,(
% 3.79/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 3.79/0.92  fof(f91,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X0),k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X1))) = k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k1_enumset1(X1,X0,X1)))) )),
% 3.79/0.92    inference(superposition,[],[f47,f54])).
% 3.79/0.92  fof(f54,plain,(
% 3.79/0.92    ( ! [X2,X1] : (k1_enumset1(X1,X2,X2) = k1_enumset1(X2,X1,X2)) )),
% 3.79/0.92    inference(superposition,[],[f44,f43])).
% 3.79/0.92  fof(f44,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0)))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f28,f36,f22,f22])).
% 3.79/0.92  fof(f28,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f2])).
% 3.79/0.92  fof(f2,axiom,(
% 3.79/0.92    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 3.79/0.92  fof(f47,plain,(
% 3.79/0.92    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f32,f38,f36,f22,f22])).
% 3.79/0.92  fof(f32,plain,(
% 3.79/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.79/0.92    inference(cnf_transformation,[],[f1])).
% 3.79/0.92  fof(f1,axiom,(
% 3.79/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 3.79/0.92  fof(f162,plain,(
% 3.79/0.92    ( ! [X47,X48,X46] : (k1_enumset1(X48,X46,X47) = k3_tarski(k1_enumset1(k1_enumset1(X48,X48,X48),k1_enumset1(X48,X48,X48),k1_enumset1(X46,X47,X46)))) )),
% 3.79/0.92    inference(superposition,[],[f98,f136])).
% 3.79/0.92  fof(f136,plain,(
% 3.79/0.92    ( ! [X2,X3] : (k1_enumset1(X2,X2,X3) = k1_enumset1(X2,X3,X2)) )),
% 3.79/0.92    inference(superposition,[],[f98,f44])).
% 3.79/0.92  fof(f98,plain,(
% 3.79/0.92    ( ! [X6,X8,X7] : (k1_enumset1(X6,X7,X8) = k3_tarski(k1_enumset1(k1_enumset1(X6,X6,X6),k1_enumset1(X6,X6,X6),k1_enumset1(X7,X7,X8)))) )),
% 3.79/0.92    inference(superposition,[],[f47,f41])).
% 3.79/0.92  fof(f41,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)))) )),
% 3.79/0.92    inference(definition_unfolding,[],[f26,f38])).
% 3.79/0.92  fof(f26,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f8])).
% 3.79/0.92  fof(f8,axiom,(
% 3.79/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.79/0.92  fof(f1890,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)))) | spl5_3),
% 3.79/0.92    inference(avatar_component_clause,[],[f1888])).
% 3.79/0.92  fof(f1891,plain,(
% 3.79/0.92    ~spl5_3 | spl5_2),
% 3.79/0.92    inference(avatar_split_clause,[],[f1626,f80,f1888])).
% 3.79/0.92  fof(f80,plain,(
% 3.79/0.92    spl5_2 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 3.79/0.92    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.79/0.92  fof(f1626,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)))) | spl5_2),
% 3.79/0.92    inference(backward_demodulation,[],[f82,f1611])).
% 3.79/0.92  fof(f1611,plain,(
% 3.79/0.92    ( ! [X10,X11,X9] : (k1_enumset1(X10,X9,X11) = k1_enumset1(X9,X11,X10)) )),
% 3.79/0.92    inference(superposition,[],[f115,f105])).
% 3.79/0.92  fof(f105,plain,(
% 3.79/0.92    ( ! [X2,X3,X1] : (k1_enumset1(X2,X1,X3) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X2)))) )),
% 3.79/0.92    inference(superposition,[],[f47,f44])).
% 3.79/0.92  fof(f82,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_2),
% 3.79/0.92    inference(avatar_component_clause,[],[f80])).
% 3.79/0.92  fof(f83,plain,(
% 3.79/0.92    ~spl5_2 | spl5_1),
% 3.79/0.92    inference(avatar_split_clause,[],[f78,f50,f80])).
% 3.79/0.92  fof(f50,plain,(
% 3.79/0.92    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 3.79/0.92    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.79/0.92  fof(f78,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 3.79/0.92    inference(forward_demodulation,[],[f77,f45])).
% 3.79/0.92  fof(f77,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 3.79/0.92    inference(forward_demodulation,[],[f52,f45])).
% 3.79/0.92  fof(f52,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 3.79/0.92    inference(avatar_component_clause,[],[f50])).
% 3.79/0.92  fof(f53,plain,(
% 3.79/0.92    ~spl5_1),
% 3.79/0.92    inference(avatar_split_clause,[],[f42,f50])).
% 3.79/0.92  fof(f42,plain,(
% 3.79/0.92    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 3.79/0.92    inference(definition_unfolding,[],[f20,f24,f22,f39,f22,f38,f25,f25,f25,f25])).
% 3.79/0.92  fof(f25,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f13])).
% 3.79/0.92  fof(f13,axiom,(
% 3.79/0.92    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 3.79/0.92  fof(f24,plain,(
% 3.79/0.92    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.79/0.92    inference(cnf_transformation,[],[f14])).
% 3.79/0.92  fof(f14,axiom,(
% 3.79/0.92    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 3.79/0.92  fof(f20,plain,(
% 3.79/0.92    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 3.79/0.92    inference(cnf_transformation,[],[f19])).
% 3.79/0.92  fof(f19,plain,(
% 3.79/0.92    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 3.79/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 3.79/0.92  fof(f18,plain,(
% 3.79/0.92    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 3.79/0.92    introduced(choice_axiom,[])).
% 3.79/0.92  fof(f17,plain,(
% 3.79/0.92    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 3.79/0.92    inference(ennf_transformation,[],[f16])).
% 3.79/0.92  fof(f16,negated_conjecture,(
% 3.79/0.92    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 3.79/0.92    inference(negated_conjecture,[],[f15])).
% 3.79/0.92  fof(f15,conjecture,(
% 3.79/0.92    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 3.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
% 3.79/0.92  % SZS output end Proof for theBenchmark
% 3.79/0.92  % (4699)------------------------------
% 3.79/0.92  % (4699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.79/0.92  % (4699)Termination reason: Refutation
% 3.79/0.92  
% 3.79/0.92  % (4699)Memory used [KB]: 10874
% 3.79/0.92  % (4699)Time elapsed: 0.463 s
% 3.79/0.92  % (4699)------------------------------
% 3.79/0.92  % (4699)------------------------------
% 3.79/0.92  % (4692)Success in time 0.564 s
%------------------------------------------------------------------------------
