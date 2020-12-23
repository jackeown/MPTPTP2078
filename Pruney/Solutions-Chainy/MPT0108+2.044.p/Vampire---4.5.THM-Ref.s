%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:24 EST 2020

% Result     : Theorem 33.01s
% Output     : Refutation 33.01s
% Verified   : 
% Statistics : Number of formulae       :  237 (181173 expanded)
%              Number of leaves         :   16 (63044 expanded)
%              Depth                    :   58
%              Number of atoms          :  409 (216200 expanded)
%              Number of equality atoms :  233 (181169 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54700,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f57,f54646])).

fof(f54646,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f54645])).

fof(f54645,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f47,f54644])).

fof(f54644,plain,
    ( ! [X255,X256] : k5_xboole_0(X255,X256) = k4_xboole_0(k5_xboole_0(X255,k4_xboole_0(X256,X255)),k4_xboole_0(X255,k4_xboole_0(X255,X256)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f54367,f53625])).

fof(f53625,plain,
    ( ! [X158,X157] : k4_xboole_0(X157,k4_xboole_0(X157,X158)) = k4_xboole_0(X157,k5_xboole_0(X157,X158))
    | ~ spl2_2 ),
    inference(superposition,[],[f53190,f47514])).

fof(f47514,plain,
    ( ! [X118,X119] : k4_xboole_0(X118,X119) = k4_xboole_0(k5_xboole_0(X118,X119),k4_xboole_0(X119,X118))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f47510,f271])).

fof(f271,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f36,f270])).

fof(f270,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f77,f269])).

fof(f269,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f244,f95])).

fof(f95,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_2 ),
    inference(superposition,[],[f77,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f244,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f49,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f39,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f28,f28])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f26,f28])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f77,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_2 ),
    inference(superposition,[],[f62,f34])).

fof(f62,plain,
    ( ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))
    | ~ spl2_2 ),
    inference(superposition,[],[f29,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f47510,plain,
    ( ! [X118,X119] : k4_xboole_0(k5_xboole_0(X118,X119),k4_xboole_0(X119,X118)) = k5_xboole_0(k4_xboole_0(X118,X119),k1_xboole_0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f32009,f47289])).

fof(f47289,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3))
    | ~ spl2_2 ),
    inference(superposition,[],[f3517,f28230])).

fof(f28230,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8))
    | ~ spl2_2 ),
    inference(superposition,[],[f616,f27233])).

fof(f27233,plain,
    ( ! [X24,X23] : k4_xboole_0(X24,X23) = k5_xboole_0(X23,k5_xboole_0(X24,k4_xboole_0(X23,X24)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f7061,f27231])).

fof(f27231,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,X29) = k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f27230,f3367])).

fof(f3367,plain,
    ( ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X8))) = k4_xboole_0(X6,X8)
    | ~ spl2_2 ),
    inference(superposition,[],[f40,f3141])).

fof(f3141,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = X28
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3140,f22])).

fof(f3140,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,k1_xboole_0) = k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3139,f271])).

fof(f3139,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = k5_xboole_0(k4_xboole_0(X28,k1_xboole_0),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3138,f290])).

fof(f290,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f276,f22])).

fof(f276,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f111,f270])).

fof(f111,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f38,f22])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f28,f28])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3138,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = k5_xboole_0(k4_xboole_0(X28,k1_xboole_0),k4_xboole_0(X28,X28))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3029,f261])).

fof(f261,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(superposition,[],[f49,f34])).

fof(f3029,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = k5_xboole_0(k4_xboole_0(X28,k1_xboole_0),k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,X28))))
    | ~ spl2_2 ),
    inference(superposition,[],[f933,f290])).

fof(f933,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f51,f932])).

fof(f932,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f931,f40])).

fof(f931,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f930,f763])).

fof(f763,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f341,f742])).

fof(f742,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f380,f38])).

fof(f380,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f377,f22])).

fof(f377,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)
    | ~ spl2_2 ),
    inference(superposition,[],[f40,f290])).

fof(f341,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4) ),
    inference(superposition,[],[f40,f38])).

fof(f930,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f868,f40])).

fof(f868,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,k4_xboole_0(X11,X13)))
    | ~ spl2_2 ),
    inference(superposition,[],[f43,f380])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f33,f28,f28,f28])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) ),
    inference(forward_demodulation,[],[f42,f40])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f32,f28,f26,f26,f28,f28])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f27230,plain,
    ( ! [X28,X29] : k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f27047,f22])).

fof(f27047,plain,
    ( ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29),k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f38,f26641])).

fof(f26641,plain,
    ( ! [X107,X108] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X107,k4_xboole_0(X108,X107)),X108),X107)
    | ~ spl2_2 ),
    inference(superposition,[],[f26089,f3671])).

fof(f3671,plain,
    ( ! [X2,X1] : k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) = X1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3615,f600])).

fof(f600,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)
    | ~ spl2_2 ),
    inference(superposition,[],[f526,f582])).

fof(f582,plain,
    ( ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f569,f271])).

fof(f569,plain,
    ( ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = k5_xboole_0(X3,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f526,f287])).

fof(f287,plain,
    ( ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f129,f270])).

fof(f129,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f127,f95])).

fof(f127,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f86,f111])).

fof(f86,plain,(
    ! [X2,X1] : k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f75,f29])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f34,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f526,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f294,f525])).

fof(f525,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f505,f271])).

fof(f505,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f294,f293])).

fof(f293,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f75,f290])).

fof(f294,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f88,f290])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f75])).

fof(f3615,plain,
    ( ! [X2,X1] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X1),X1),k4_xboole_0(X2,X1)) = X1
    | ~ spl2_2 ),
    inference(superposition,[],[f3446,f261])).

fof(f3446,plain,
    ( ! [X15,X16] : k4_xboole_0(X16,X15) = k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X15)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3370,f593])).

fof(f593,plain,
    ( ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5
    | ~ spl2_2 ),
    inference(superposition,[],[f582,f582])).

fof(f3370,plain,
    ( ! [X15,X16] : k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X15) = k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X15)
    | ~ spl2_2 ),
    inference(superposition,[],[f115,f3141])).

fof(f115,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f34,f38])).

fof(f26089,plain,
    ( ! [X28,X29,X27] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X27,k4_xboole_0(X28,X29)))
    | ~ spl2_2 ),
    inference(superposition,[],[f25777,f1158])).

fof(f1158,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X4))
    | ~ spl2_2 ),
    inference(superposition,[],[f1121,f261])).

fof(f1121,plain,
    ( ! [X17,X18,X16] : k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,X17),X18)) = X17
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1072,f22])).

fof(f1072,plain,
    ( ! [X17,X18,X16] : k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),X18),k1_xboole_0)) = X17
    | ~ spl2_2 ),
    inference(superposition,[],[f413,f765])).

fof(f765,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f761,f293])).

fof(f761,plain,
    ( ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f695,f742])).

fof(f695,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f115,f38])).

fof(f413,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))) = X10 ),
    inference(superposition,[],[f261,f40])).

fof(f25777,plain,
    ( ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X7),X6),k4_xboole_0(X5,X6))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f21992,f25776])).

fof(f25776,plain,
    ( ! [X50,X51,X49] : k4_xboole_0(k4_xboole_0(X49,X51),X50) = k4_xboole_0(k4_xboole_0(X49,X51),k4_xboole_0(X50,k4_xboole_0(X50,X49)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f25549,f924])).

fof(f924,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f923,f763])).

fof(f923,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f865,f742])).

fof(f865,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),k4_xboole_0(X2,k4_xboole_0(X2,X4))) ),
    inference(superposition,[],[f43,f38])).

fof(f25549,plain,
    ( ! [X50,X51,X49] : k4_xboole_0(k4_xboole_0(X49,X51),k4_xboole_0(X49,k4_xboole_0(X49,X50))) = k4_xboole_0(k4_xboole_0(X49,X51),k4_xboole_0(X50,k4_xboole_0(X50,X49)))
    | ~ spl2_2 ),
    inference(superposition,[],[f924,f742])).

fof(f21992,plain,
    ( ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X7),k4_xboole_0(X6,k4_xboole_0(X6,X5))),k4_xboole_0(X5,X6))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f21823,f22])).

fof(f21823,plain,
    ( ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X7),k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0)),k4_xboole_0(X5,X6))
    | ~ spl2_2 ),
    inference(superposition,[],[f21460,f7660])).

fof(f7660,plain,(
    ! [X41,X42] : k4_xboole_0(X42,k4_xboole_0(X42,X41)) = k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X42)),k1_xboole_0) ),
    inference(superposition,[],[f344,f22])).

fof(f344,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f40,f38])).

fof(f21460,plain,
    ( ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)),X7)
    | ~ spl2_2 ),
    inference(superposition,[],[f7912,f763])).

fof(f7912,plain,
    ( ! [X35,X36,X34] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k4_xboole_0(X35,X36)))),X36)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f7679,f290])).

fof(f7679,plain,(
    ! [X35,X36,X34] : k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k4_xboole_0(X35,X36)))),X36) = k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X35,X36)),k4_xboole_0(X34,k4_xboole_0(X35,X36))) ),
    inference(superposition,[],[f344,f411])).

fof(f411,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f261,f261])).

fof(f7061,plain,
    ( ! [X24,X23] : k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X23,X24)),X23) = k5_xboole_0(X23,k5_xboole_0(X24,k4_xboole_0(X23,X24)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f6963,f22])).

fof(f6963,plain,
    ( ! [X24,X23] : k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X23,X24)),X23) = k5_xboole_0(k4_xboole_0(X23,k1_xboole_0),k5_xboole_0(X24,k4_xboole_0(X23,X24)))
    | ~ spl2_2 ),
    inference(superposition,[],[f1405,f3824])).

fof(f3824,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3752,f293])).

fof(f3752,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f34,f3236])).

fof(f3236,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = X2
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3235,f712])).

fof(f712,plain,
    ( ! [X8,X7] : k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8)) = X7
    | ~ spl2_2 ),
    inference(superposition,[],[f582,f115])).

fof(f3235,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3234,f742])).

fof(f3234,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3064,f535])).

fof(f535,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f506,f525])).

fof(f506,plain,
    ( ! [X2,X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_2 ),
    inference(superposition,[],[f294,f34])).

fof(f3064,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ spl2_2 ),
    inference(superposition,[],[f933,f711])).

fof(f711,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X6))
    | ~ spl2_2 ),
    inference(superposition,[],[f526,f115])).

fof(f1405,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),X21)
    | ~ spl2_2 ),
    inference(superposition,[],[f593,f711])).

fof(f616,plain,
    ( ! [X10,X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,X10)),X10)
    | ~ spl2_2 ),
    inference(superposition,[],[f592,f29])).

fof(f592,plain,
    ( ! [X4,X3] : k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3
    | ~ spl2_2 ),
    inference(superposition,[],[f582,f526])).

fof(f3517,plain,
    ( ! [X35,X36,X34] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35)))
    | ~ spl2_2 ),
    inference(superposition,[],[f3422,f1158])).

fof(f3422,plain,
    ( ! [X19,X20] : k1_xboole_0 = k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3421,f290])).

fof(f3421,plain,
    ( ! [X19,X20] : k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3420,f261])).

fof(f3420,plain,
    ( ! [X19,X20] : k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(X19,k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3419,f535])).

fof(f3419,plain,
    ( ! [X19,X20] : k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k5_xboole_0(X19,k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3348,f600])).

fof(f3348,plain,
    ( ! [X19,X20] : k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k5_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),X19)))
    | ~ spl2_2 ),
    inference(superposition,[],[f3141,f3141])).

fof(f32009,plain,
    ( ! [X118,X119] : k4_xboole_0(k5_xboole_0(X118,X119),k4_xboole_0(X119,X118)) = k5_xboole_0(k4_xboole_0(X118,X119),k4_xboole_0(k4_xboole_0(X119,X118),k5_xboole_0(X118,X119)))
    | ~ spl2_2 ),
    inference(superposition,[],[f28227,f28227])).

fof(f28227,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))
    | ~ spl2_2 ),
    inference(superposition,[],[f541,f27233])).

fof(f541,plain,
    ( ! [X12,X13,X11] : k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f512,f525])).

fof(f512,plain,
    ( ! [X12,X13,X11] : k5_xboole_0(k1_xboole_0,X13) = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13)))
    | ~ spl2_2 ),
    inference(superposition,[],[f294,f29])).

fof(f53190,plain,
    ( ! [X61,X62,X63] : k4_xboole_0(X62,X61) = k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f41832,f53189])).

fof(f53189,plain,
    ( ! [X253,X251,X252] : k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X253,X251)),X253)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f53188,f380])).

fof(f53188,plain,
    ( ! [X253,X251,X252] : k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X252,k4_xboole_0(X252,k4_xboole_0(X253,X251)))),X253)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f53109,f25877])).

fof(f25877,plain,
    ( ! [X85,X83,X84] : k4_xboole_0(X83,k4_xboole_0(X83,k4_xboole_0(X85,X84))) = k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(X83,X85))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f25876,f7921])).

fof(f7921,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(k4_xboole_0(X17,X18),X16)) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18))) ),
    inference(forward_demodulation,[],[f7688,f40])).

fof(f7688,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(k4_xboole_0(X17,X18),X16)) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),X18) ),
    inference(superposition,[],[f344,f38])).

fof(f25876,plain,
    ( ! [X85,X83,X84] : k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(k4_xboole_0(X83,X84),X85)) = k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(X83,X85))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f25640,f380])).

fof(f25640,plain,
    ( ! [X85,X83,X84] : k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(k4_xboole_0(X83,X84),X85)) = k4_xboole_0(k4_xboole_0(X83,k4_xboole_0(X83,k4_xboole_0(X83,X84))),k4_xboole_0(X83,X85))
    | ~ spl2_2 ),
    inference(superposition,[],[f344,f924])).

fof(f53109,plain,
    ( ! [X253,X251,X252] : k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(k4_xboole_0(X252,X251),k4_xboole_0(X252,X253))),X253)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f38222,f52942])).

fof(f52942,plain,
    ( ! [X103,X105,X104] : k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105))) = k4_xboole_0(k4_xboole_0(X103,X105),X104)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f52941,f8027])).

fof(f8027,plain,
    ( ! [X59,X60,X58] : k4_xboole_0(k4_xboole_0(X59,X60),X58) = k4_xboole_0(k4_xboole_0(X59,X60),k4_xboole_0(X59,k4_xboole_0(X59,k4_xboole_0(X58,X60))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f7751,f40])).

fof(f7751,plain,
    ( ! [X59,X60,X58] : k4_xboole_0(k4_xboole_0(X59,X60),X58) = k4_xboole_0(k4_xboole_0(X59,X60),k4_xboole_0(k4_xboole_0(X59,k4_xboole_0(X59,X58)),X60))
    | ~ spl2_2 ),
    inference(superposition,[],[f742,f344])).

fof(f52941,plain,
    ( ! [X103,X105,X104] : k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f52940,f22])).

fof(f52940,plain,
    ( ! [X103,X105,X104] : k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105))),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f52939,f34])).

fof(f52939,plain,
    ( ! [X103,X105,X104] : k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k5_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105))))),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f52938,f51294])).

fof(f51294,plain,
    ( ! [X588,X590,X589] : k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590))) = k4_xboole_0(X588,k4_xboole_0(X588,k5_xboole_0(X590,k4_xboole_0(X589,X590))))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f51290,f51293])).

fof(f51293,plain,
    ( ! [X592,X593,X591] : k4_xboole_0(X591,k4_xboole_0(X591,k5_xboole_0(X593,k4_xboole_0(X592,X593)))) = k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(X593,k4_xboole_0(X593,k4_xboole_0(X591,X592))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f51292,f380])).

fof(f51292,plain,
    ( ! [X592,X593,X591] : k4_xboole_0(X591,k4_xboole_0(X591,k5_xboole_0(X593,k4_xboole_0(X592,X593)))) = k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(X593,k4_xboole_0(X593,k4_xboole_0(X591,k4_xboole_0(X591,k4_xboole_0(X591,X592))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f51291,f40])).

fof(f51291,plain,
    ( ! [X592,X593,X591] : k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(k4_xboole_0(X593,k4_xboole_0(X593,X591)),k4_xboole_0(X591,k4_xboole_0(X591,X592)))) = k4_xboole_0(X591,k4_xboole_0(X591,k5_xboole_0(X593,k4_xboole_0(X592,X593))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f50310,f3186])).

fof(f3186,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k5_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X4,X3))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3038,f535])).

fof(f3038,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X4,X3))))
    | ~ spl2_2 ),
    inference(superposition,[],[f933,f711])).

fof(f50310,plain,
    ( ! [X592,X593,X591] : k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(k4_xboole_0(X593,k4_xboole_0(X593,X591)),k4_xboole_0(X591,k4_xboole_0(X591,X592)))) = k5_xboole_0(k4_xboole_0(X593,k4_xboole_0(X593,X591)),k4_xboole_0(X591,k4_xboole_0(X591,k4_xboole_0(X592,X593))))
    | ~ spl2_2 ),
    inference(superposition,[],[f27235,f893])).

fof(f893,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f43,f38])).

fof(f27235,plain,
    ( ! [X26,X25] : k5_xboole_0(X26,k4_xboole_0(X25,X26)) = k5_xboole_0(X25,k4_xboole_0(X26,X25))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f3760,f27231])).

fof(f3760,plain,
    ( ! [X26,X25] : k5_xboole_0(X26,k4_xboole_0(X25,X26)) = k5_xboole_0(X25,k4_xboole_0(k5_xboole_0(X26,k4_xboole_0(X25,X26)),X25))
    | ~ spl2_2 ),
    inference(superposition,[],[f712,f3236])).

fof(f51290,plain,
    ( ! [X588,X590,X589] : k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(X590,k4_xboole_0(X590,k4_xboole_0(X588,X589))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f51289,f380])).

fof(f51289,plain,
    ( ! [X588,X590,X589] : k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(X590,k4_xboole_0(X590,k4_xboole_0(X588,k4_xboole_0(X588,k4_xboole_0(X588,X589))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f51288,f40])).

fof(f51288,plain,
    ( ! [X588,X590,X589] : k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(k4_xboole_0(X590,k4_xboole_0(X590,X588)),k4_xboole_0(X588,k4_xboole_0(X588,X589)))) = k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f51287,f600])).

fof(f51287,plain,
    ( ! [X588,X590,X589] : k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(k4_xboole_0(X590,k4_xboole_0(X590,X588)),k4_xboole_0(X588,k4_xboole_0(X588,X589)))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X589,X590)),k4_xboole_0(X588,X590))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f50309,f36281])).

fof(f36281,plain,
    ( ! [X420,X422,X421] : k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(X421,X422),k4_xboole_0(X421,X420))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f36280,f33661])).

fof(f33661,plain,
    ( ! [X76,X77,X75] : k5_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X75,X77)) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f33660,f526])).

fof(f33660,plain,
    ( ! [X76,X77,X75] : k5_xboole_0(X75,k5_xboole_0(X75,k5_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X75,X77)))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f33659,f1241])).

fof(f1241,plain,
    ( ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X5),X6)) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6)
    | ~ spl2_2 ),
    inference(superposition,[],[f29,f535])).

fof(f33659,plain,
    ( ! [X76,X77,X75] : k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76)))) = k5_xboole_0(X75,k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,X77)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f33658,f1694])).

fof(f1694,plain,
    ( ! [X10,X8,X9] : k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9)))
    | ~ spl2_2 ),
    inference(superposition,[],[f608,f34])).

fof(f608,plain,
    ( ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f601,f29])).

fof(f601,plain,
    ( ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6))
    | ~ spl2_2 ),
    inference(superposition,[],[f29,f582])).

fof(f33658,plain,
    ( ! [X76,X77,X75] : k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,k4_xboole_0(X75,X77))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f33657,f932])).

fof(f33657,plain,
    ( ! [X76,X77,X75] : k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,k4_xboole_0(X75,X77))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,k4_xboole_0(X75,k4_xboole_0(X75,X76))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f33461,f40])).

fof(f33461,plain,
    ( ! [X76,X77,X75] : k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,k4_xboole_0(X75,X77))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X77)),k4_xboole_0(X75,k4_xboole_0(X75,X76))))
    | ~ spl2_2 ),
    inference(superposition,[],[f28228,f43])).

fof(f28228,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))
    | ~ spl2_2 ),
    inference(superposition,[],[f595,f27233])).

fof(f595,plain,
    ( ! [X10,X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X10,k5_xboole_0(X8,k5_xboole_0(X9,X10)))
    | ~ spl2_2 ),
    inference(superposition,[],[f582,f29])).

fof(f36280,plain,
    ( ! [X420,X422,X421] : k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X422,X420))),k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X420,X422))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f36279,f1554])).

fof(f1554,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X12))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X10)))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1553,f40])).

fof(f1553,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X12) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X10)))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1493,f1542])).

fof(f1542,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,X27))) = k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28)))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1541,f932])).

fof(f1541,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,X27))) = k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1482,f40])).

fof(f1482,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,X27))) = k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X27)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))))
    | ~ spl2_2 ),
    inference(superposition,[],[f742,f40])).

fof(f1493,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X12) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))))))
    | ~ spl2_2 ),
    inference(superposition,[],[f742,f40])).

fof(f36279,plain,
    ( ! [X420,X422,X421] : k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X422,k4_xboole_0(X420,k4_xboole_0(X420,X421))))),k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X420,X422))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f35504,f40])).

fof(f35504,plain,
    ( ! [X420,X422,X421] : k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))),k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X420,X422))))
    | ~ spl2_2 ),
    inference(superposition,[],[f28228,f876])).

fof(f876,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[],[f43,f38])).

fof(f50309,plain,
    ( ! [X588,X590,X589] : k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(k4_xboole_0(X590,k4_xboole_0(X590,X588)),k4_xboole_0(X588,k4_xboole_0(X588,X589)))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,k4_xboole_0(X589,X590))),k4_xboole_0(X590,k4_xboole_0(X590,X588)))
    | ~ spl2_2 ),
    inference(superposition,[],[f27234,f893])).

fof(f27234,plain,
    ( ! [X21,X22] : k5_xboole_0(k4_xboole_0(X22,X21),X21) = k5_xboole_0(X22,k4_xboole_0(X21,X22))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f5093,f27231])).

fof(f5093,plain,
    ( ! [X21,X22] : k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21),X21)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f4971,f22])).

fof(f4971,plain,
    ( ! [X21,X22] : k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21),k4_xboole_0(X21,k1_xboole_0))
    | ~ spl2_2 ),
    inference(superposition,[],[f713,f3824])).

fof(f713,plain,
    ( ! [X10,X9] : k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9
    | ~ spl2_2 ),
    inference(superposition,[],[f592,f115])).

fof(f52938,plain,
    ( ! [X103,X105,X104] : k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k5_xboole_0(X103,k5_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X104,X105)))),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f52604,f1694])).

fof(f52604,plain,
    ( ! [X103,X105,X104] : k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))),k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f47514,f8028])).

fof(f8028,plain,
    ( ! [X61,X62,X63] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X62,k4_xboole_0(X61,X63))),k4_xboole_0(X62,X63))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f7752,f40])).

fof(f7752,plain,
    ( ! [X61,X62,X63] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X62,X61)),X63),k4_xboole_0(X62,X63))
    | ~ spl2_2 ),
    inference(superposition,[],[f776,f344])).

fof(f776,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)
    | ~ spl2_2 ),
    inference(superposition,[],[f765,f38])).

fof(f38222,plain,
    ( ! [X253,X251,X252] : k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X252,k5_xboole_0(X251,k4_xboole_0(k4_xboole_0(X252,X253),X251)))),X253)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f38009,f27474])).

fof(f27474,plain,
    ( ! [X4,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X4,X5)),k4_xboole_0(X5,X4)) = X4
    | ~ spl2_2 ),
    inference(superposition,[],[f3671,f27235])).

fof(f38009,plain,
    ( ! [X253,X251,X252] : k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X252,k5_xboole_0(X251,k4_xboole_0(k4_xboole_0(X252,X253),X251)))),X253) = k4_xboole_0(k5_xboole_0(X251,k4_xboole_0(k4_xboole_0(X252,X253),X251)),k4_xboole_0(X251,k4_xboole_0(X252,X253)))
    | ~ spl2_2 ),
    inference(superposition,[],[f344,f27231])).

fof(f41832,plain,
    ( ! [X61,X62,X63] : k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))) = k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))),X61)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f41500,f271])).

fof(f41500,plain,
    ( ! [X61,X62,X63] : k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))),X61) = k5_xboole_0(k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))),k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f115,f21061])).

fof(f21061,plain,
    ( ! [X12,X10,X11] : k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X12,X11)))))
    | ~ spl2_2 ),
    inference(superposition,[],[f7902,f40])).

fof(f7902,plain,
    ( ! [X19,X20,X18] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),k4_xboole_0(X19,k4_xboole_0(X20,X18)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f7673,f290])).

fof(f7673,plain,(
    ! [X19,X20,X18] : k4_xboole_0(X18,X18) = k4_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),k4_xboole_0(X19,k4_xboole_0(X20,X18))) ),
    inference(superposition,[],[f344,f413])).

fof(f54367,plain,
    ( ! [X255,X256] : k5_xboole_0(X255,X256) = k4_xboole_0(k5_xboole_0(X255,k4_xboole_0(X256,X255)),k4_xboole_0(X255,k5_xboole_0(X255,X256)))
    | ~ spl2_2 ),
    inference(superposition,[],[f27474,f53952])).

fof(f53952,plain,
    ( ! [X21,X22] : k4_xboole_0(X22,X21) = k4_xboole_0(k5_xboole_0(X21,X22),X21)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f53925,f1405])).

fof(f53925,plain,
    ( ! [X21,X22] : k4_xboole_0(k5_xboole_0(X21,X22),X21) = k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f30650,f53625])).

fof(f30650,plain,
    ( ! [X21,X22] : k4_xboole_0(k5_xboole_0(X21,X22),X21) = k5_xboole_0(k4_xboole_0(X21,k5_xboole_0(X21,X22)),X22)
    | ~ spl2_2 ),
    inference(superposition,[],[f27872,f526])).

fof(f27872,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X6,X5))
    | ~ spl2_2 ),
    inference(superposition,[],[f27236,f2071])).

fof(f2071,plain,
    ( ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f2018,f29])).

fof(f2018,plain,
    ( ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24)
    | ~ spl2_2 ),
    inference(superposition,[],[f1286,f582])).

fof(f1286,plain,
    ( ! [X21,X22,X20] : k5_xboole_0(X21,X20) = k5_xboole_0(k5_xboole_0(X22,X20),k5_xboole_0(X22,X21))
    | ~ spl2_2 ),
    inference(superposition,[],[f541,f582])).

fof(f27236,plain,
    ( ! [X15,X16] : k4_xboole_0(X16,X15) = k5_xboole_0(k5_xboole_0(X16,k4_xboole_0(X15,X16)),X15)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f3756,f27231])).

fof(f3756,plain,
    ( ! [X15,X16] : k4_xboole_0(k5_xboole_0(X16,k4_xboole_0(X15,X16)),X15) = k5_xboole_0(k5_xboole_0(X16,k4_xboole_0(X15,X16)),X15)
    | ~ spl2_2 ),
    inference(superposition,[],[f115,f3236])).

fof(f47,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f57,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f52,f54])).

fof(f52,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f36,f22])).

fof(f48,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f35,f45])).

fof(f35,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f20,f26,f28])).

fof(f20,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (7812)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (7821)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (7813)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (7825)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (7811)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (7817)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (7820)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (7818)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (7823)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (7816)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (7814)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (7822)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (7822)Refutation not found, incomplete strategy% (7822)------------------------------
% 0.21/0.49  % (7822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7822)Memory used [KB]: 10490
% 0.21/0.49  % (7822)Time elapsed: 0.070 s
% 0.21/0.49  % (7822)------------------------------
% 0.21/0.49  % (7822)------------------------------
% 0.21/0.49  % (7828)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (7819)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (7826)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (7815)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (7827)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (7824)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 5.36/1.04  % (7815)Time limit reached!
% 5.36/1.04  % (7815)------------------------------
% 5.36/1.04  % (7815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.36/1.05  % (7815)Termination reason: Time limit
% 5.36/1.05  
% 5.36/1.05  % (7815)Memory used [KB]: 16502
% 5.36/1.05  % (7815)Time elapsed: 0.622 s
% 5.36/1.05  % (7815)------------------------------
% 5.36/1.05  % (7815)------------------------------
% 12.94/1.98  % (7817)Time limit reached!
% 12.94/1.98  % (7817)------------------------------
% 12.94/1.98  % (7817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.94/1.98  % (7817)Termination reason: Time limit
% 12.94/1.98  % (7817)Termination phase: Saturation
% 12.94/1.98  
% 12.94/1.98  % (7817)Memory used [KB]: 63708
% 12.94/1.98  % (7817)Time elapsed: 1.500 s
% 12.94/1.98  % (7817)------------------------------
% 12.94/1.98  % (7817)------------------------------
% 12.94/1.99  % (7816)Time limit reached!
% 12.94/1.99  % (7816)------------------------------
% 12.94/1.99  % (7816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.94/1.99  % (7816)Termination reason: Time limit
% 12.94/1.99  
% 12.94/1.99  % (7816)Memory used [KB]: 45287
% 12.94/1.99  % (7816)Time elapsed: 1.574 s
% 12.94/1.99  % (7816)------------------------------
% 12.94/1.99  % (7816)------------------------------
% 14.82/2.24  % (7813)Time limit reached!
% 14.82/2.24  % (7813)------------------------------
% 14.82/2.24  % (7813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.82/2.24  % (7813)Termination reason: Time limit
% 14.82/2.24  % (7813)Termination phase: Saturation
% 14.82/2.24  
% 14.82/2.24  % (7813)Memory used [KB]: 45798
% 14.82/2.24  % (7813)Time elapsed: 1.800 s
% 14.82/2.24  % (7813)------------------------------
% 14.82/2.24  % (7813)------------------------------
% 17.84/2.61  % (7823)Time limit reached!
% 17.84/2.61  % (7823)------------------------------
% 17.84/2.61  % (7823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.84/2.61  % (7823)Termination reason: Time limit
% 17.84/2.61  % (7823)Termination phase: Saturation
% 17.84/2.61  
% 17.84/2.61  % (7823)Memory used [KB]: 45926
% 17.84/2.61  % (7823)Time elapsed: 2.200 s
% 17.84/2.61  % (7823)------------------------------
% 17.84/2.61  % (7823)------------------------------
% 33.01/4.52  % (7821)Refutation found. Thanks to Tanya!
% 33.01/4.52  % SZS status Theorem for theBenchmark
% 33.01/4.52  % SZS output start Proof for theBenchmark
% 33.01/4.52  fof(f54700,plain,(
% 33.01/4.52    $false),
% 33.01/4.52    inference(avatar_sat_refutation,[],[f48,f57,f54646])).
% 33.01/4.52  fof(f54646,plain,(
% 33.01/4.52    spl2_1 | ~spl2_2),
% 33.01/4.52    inference(avatar_contradiction_clause,[],[f54645])).
% 33.01/4.52  fof(f54645,plain,(
% 33.01/4.52    $false | (spl2_1 | ~spl2_2)),
% 33.01/4.52    inference(subsumption_resolution,[],[f47,f54644])).
% 33.01/4.52  fof(f54644,plain,(
% 33.01/4.52    ( ! [X255,X256] : (k5_xboole_0(X255,X256) = k4_xboole_0(k5_xboole_0(X255,k4_xboole_0(X256,X255)),k4_xboole_0(X255,k4_xboole_0(X255,X256)))) ) | ~spl2_2),
% 33.01/4.52    inference(forward_demodulation,[],[f54367,f53625])).
% 33.01/4.52  fof(f53625,plain,(
% 33.01/4.52    ( ! [X158,X157] : (k4_xboole_0(X157,k4_xboole_0(X157,X158)) = k4_xboole_0(X157,k5_xboole_0(X157,X158))) ) | ~spl2_2),
% 33.01/4.52    inference(superposition,[],[f53190,f47514])).
% 33.01/4.52  fof(f47514,plain,(
% 33.01/4.52    ( ! [X118,X119] : (k4_xboole_0(X118,X119) = k4_xboole_0(k5_xboole_0(X118,X119),k4_xboole_0(X119,X118))) ) | ~spl2_2),
% 33.01/4.52    inference(forward_demodulation,[],[f47510,f271])).
% 33.01/4.52  fof(f271,plain,(
% 33.01/4.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 33.01/4.52    inference(backward_demodulation,[],[f36,f270])).
% 33.01/4.52  fof(f270,plain,(
% 33.01/4.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_2),
% 33.01/4.52    inference(backward_demodulation,[],[f77,f269])).
% 33.01/4.52  fof(f269,plain,(
% 33.01/4.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | ~spl2_2),
% 33.01/4.52    inference(forward_demodulation,[],[f244,f95])).
% 33.01/4.52  fof(f95,plain,(
% 33.01/4.52    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl2_2),
% 33.01/4.52    inference(superposition,[],[f77,f34])).
% 33.01/4.52  fof(f34,plain,(
% 33.01/4.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 33.01/4.52    inference(definition_unfolding,[],[f27,f28])).
% 33.01/4.52  fof(f28,plain,(
% 33.01/4.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 33.01/4.52    inference(cnf_transformation,[],[f9])).
% 33.01/4.52  fof(f9,axiom,(
% 33.01/4.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 33.01/4.52  fof(f27,plain,(
% 33.01/4.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 33.01/4.52    inference(cnf_transformation,[],[f3])).
% 33.01/4.52  fof(f3,axiom,(
% 33.01/4.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 33.01/4.52  fof(f244,plain,(
% 33.01/4.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) )),
% 33.01/4.52    inference(superposition,[],[f49,f22])).
% 33.01/4.52  fof(f22,plain,(
% 33.01/4.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 33.01/4.52    inference(cnf_transformation,[],[f8])).
% 33.01/4.52  fof(f8,axiom,(
% 33.01/4.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 33.01/4.52  fof(f49,plain,(
% 33.01/4.52    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 33.01/4.52    inference(backward_demodulation,[],[f39,f40])).
% 33.01/4.52  fof(f40,plain,(
% 33.01/4.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 33.01/4.52    inference(definition_unfolding,[],[f30,f28,f28])).
% 33.01/4.52  fof(f30,plain,(
% 33.01/4.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 33.01/4.52    inference(cnf_transformation,[],[f10])).
% 33.01/4.52  fof(f10,axiom,(
% 33.01/4.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 33.01/4.52  fof(f39,plain,(
% 33.01/4.52    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 33.01/4.52    inference(definition_unfolding,[],[f25,f26,f28])).
% 33.01/4.52  fof(f26,plain,(
% 33.01/4.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 33.01/4.52    inference(cnf_transformation,[],[f13])).
% 33.01/4.52  fof(f13,axiom,(
% 33.01/4.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 33.01/4.52  fof(f25,plain,(
% 33.01/4.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 33.01/4.52    inference(cnf_transformation,[],[f6])).
% 33.01/4.52  fof(f6,axiom,(
% 33.01/4.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 33.01/4.52  fof(f77,plain,(
% 33.01/4.52    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | ~spl2_2),
% 33.01/4.52    inference(superposition,[],[f62,f34])).
% 33.01/4.52  fof(f62,plain,(
% 33.01/4.52    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) ) | ~spl2_2),
% 33.01/4.52    inference(superposition,[],[f29,f56])).
% 33.01/4.52  fof(f56,plain,(
% 33.01/4.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 33.01/4.52    inference(avatar_component_clause,[],[f54])).
% 33.01/4.52  fof(f54,plain,(
% 33.01/4.52    spl2_2 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 33.01/4.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 33.01/4.52  fof(f29,plain,(
% 33.01/4.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 33.01/4.52    inference(cnf_transformation,[],[f12])).
% 33.01/4.52  fof(f12,axiom,(
% 33.01/4.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 33.01/4.52  fof(f36,plain,(
% 33.01/4.52    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 33.01/4.52    inference(definition_unfolding,[],[f21,f26])).
% 33.01/4.52  fof(f21,plain,(
% 33.01/4.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 33.01/4.52    inference(cnf_transformation,[],[f5])).
% 33.01/4.52  fof(f5,axiom,(
% 33.01/4.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 33.01/4.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 33.01/4.52  fof(f47510,plain,(
% 33.01/4.52    ( ! [X118,X119] : (k4_xboole_0(k5_xboole_0(X118,X119),k4_xboole_0(X119,X118)) = k5_xboole_0(k4_xboole_0(X118,X119),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.52    inference(backward_demodulation,[],[f32009,f47289])).
% 33.01/4.52  fof(f47289,plain,(
% 33.01/4.52    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3))) ) | ~spl2_2),
% 33.01/4.52    inference(superposition,[],[f3517,f28230])).
% 33.01/4.52  fof(f28230,plain,(
% 33.01/4.52    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8))) ) | ~spl2_2),
% 33.01/4.52    inference(superposition,[],[f616,f27233])).
% 33.01/4.52  fof(f27233,plain,(
% 33.01/4.52    ( ! [X24,X23] : (k4_xboole_0(X24,X23) = k5_xboole_0(X23,k5_xboole_0(X24,k4_xboole_0(X23,X24)))) ) | ~spl2_2),
% 33.01/4.52    inference(backward_demodulation,[],[f7061,f27231])).
% 33.01/4.52  fof(f27231,plain,(
% 33.01/4.52    ( ! [X28,X29] : (k4_xboole_0(X28,X29) = k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29)) ) | ~spl2_2),
% 33.01/4.52    inference(forward_demodulation,[],[f27230,f3367])).
% 33.01/4.52  fof(f3367,plain,(
% 33.01/4.52    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X8))) = k4_xboole_0(X6,X8)) ) | ~spl2_2),
% 33.01/4.52    inference(superposition,[],[f40,f3141])).
% 33.01/4.52  fof(f3141,plain,(
% 33.01/4.52    ( ! [X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = X28) ) | ~spl2_2),
% 33.01/4.52    inference(forward_demodulation,[],[f3140,f22])).
% 33.01/4.52  fof(f3140,plain,(
% 33.01/4.52    ( ! [X28,X29] : (k4_xboole_0(X28,k1_xboole_0) = k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28))))) ) | ~spl2_2),
% 33.01/4.52    inference(forward_demodulation,[],[f3139,f271])).
% 33.01/4.53  fof(f3139,plain,(
% 33.01/4.53    ( ! [X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = k5_xboole_0(k4_xboole_0(X28,k1_xboole_0),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3138,f290])).
% 33.01/4.53  fof(f290,plain,(
% 33.01/4.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f276,f22])).
% 33.01/4.53  fof(f276,plain,(
% 33.01/4.53    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f111,f270])).
% 33.01/4.53  fof(f111,plain,(
% 33.01/4.53    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 33.01/4.53    inference(superposition,[],[f38,f22])).
% 33.01/4.53  fof(f38,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 33.01/4.53    inference(definition_unfolding,[],[f24,f28,f28])).
% 33.01/4.53  fof(f24,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 33.01/4.53    inference(cnf_transformation,[],[f1])).
% 33.01/4.53  fof(f1,axiom,(
% 33.01/4.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 33.01/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 33.01/4.53  fof(f3138,plain,(
% 33.01/4.53    ( ! [X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = k5_xboole_0(k4_xboole_0(X28,k1_xboole_0),k4_xboole_0(X28,X28))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3029,f261])).
% 33.01/4.53  fof(f261,plain,(
% 33.01/4.53    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 33.01/4.53    inference(superposition,[],[f49,f34])).
% 33.01/4.53  fof(f3029,plain,(
% 33.01/4.53    ( ! [X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k5_xboole_0(X28,k4_xboole_0(X29,X28)))) = k5_xboole_0(k4_xboole_0(X28,k1_xboole_0),k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,X28))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f933,f290])).
% 33.01/4.53  fof(f933,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f51,f932])).
% 33.01/4.53  fof(f932,plain,(
% 33.01/4.53    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f931,f40])).
% 33.01/4.53  fof(f931,plain,(
% 33.01/4.53    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f930,f763])).
% 33.01/4.53  fof(f763,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f341,f742])).
% 33.01/4.53  fof(f742,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f380,f38])).
% 33.01/4.53  fof(f380,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f377,f22])).
% 33.01/4.53  fof(f377,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f40,f290])).
% 33.01/4.53  fof(f341,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) )),
% 33.01/4.53    inference(superposition,[],[f40,f38])).
% 33.01/4.53  fof(f930,plain,(
% 33.01/4.53    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f868,f40])).
% 33.01/4.53  fof(f868,plain,(
% 33.01/4.53    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,k4_xboole_0(X11,X13)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f43,f380])).
% 33.01/4.53  fof(f43,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 33.01/4.53    inference(definition_unfolding,[],[f33,f28,f28,f28])).
% 33.01/4.53  fof(f33,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 33.01/4.53    inference(cnf_transformation,[],[f11])).
% 33.01/4.53  fof(f11,axiom,(
% 33.01/4.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 33.01/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 33.01/4.53  fof(f51,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) )),
% 33.01/4.53    inference(forward_demodulation,[],[f42,f40])).
% 33.01/4.53  fof(f42,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 33.01/4.53    inference(definition_unfolding,[],[f32,f28,f26,f26,f28,f28])).
% 33.01/4.53  fof(f32,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 33.01/4.53    inference(cnf_transformation,[],[f7])).
% 33.01/4.53  fof(f7,axiom,(
% 33.01/4.53    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 33.01/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 33.01/4.53  fof(f27230,plain,(
% 33.01/4.53    ( ! [X28,X29] : (k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f27047,f22])).
% 33.01/4.53  fof(f27047,plain,(
% 33.01/4.53    ( ! [X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(X29,X28)),X29),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f38,f26641])).
% 33.01/4.53  fof(f26641,plain,(
% 33.01/4.53    ( ! [X107,X108] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X107,k4_xboole_0(X108,X107)),X108),X107)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f26089,f3671])).
% 33.01/4.53  fof(f3671,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) = X1) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3615,f600])).
% 33.01/4.53  fof(f600,plain,(
% 33.01/4.53    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f526,f582])).
% 33.01/4.53  fof(f582,plain,(
% 33.01/4.53    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f569,f271])).
% 33.01/4.53  fof(f569,plain,(
% 33.01/4.53    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = k5_xboole_0(X3,k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f526,f287])).
% 33.01/4.53  fof(f287,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f129,f270])).
% 33.01/4.53  fof(f129,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f127,f95])).
% 33.01/4.53  fof(f127,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2)))) )),
% 33.01/4.53    inference(backward_demodulation,[],[f86,f111])).
% 33.01/4.53  fof(f86,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 33.01/4.53    inference(superposition,[],[f75,f29])).
% 33.01/4.53  fof(f75,plain,(
% 33.01/4.53    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 33.01/4.53    inference(superposition,[],[f34,f37])).
% 33.01/4.53  fof(f37,plain,(
% 33.01/4.53    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 33.01/4.53    inference(definition_unfolding,[],[f23,f28])).
% 33.01/4.53  fof(f23,plain,(
% 33.01/4.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 33.01/4.53    inference(cnf_transformation,[],[f16])).
% 33.01/4.53  fof(f16,plain,(
% 33.01/4.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 33.01/4.53    inference(rectify,[],[f2])).
% 33.01/4.53  fof(f2,axiom,(
% 33.01/4.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 33.01/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 33.01/4.53  fof(f526,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f294,f525])).
% 33.01/4.53  fof(f525,plain,(
% 33.01/4.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f505,f271])).
% 33.01/4.53  fof(f505,plain,(
% 33.01/4.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f294,f293])).
% 33.01/4.53  fof(f293,plain,(
% 33.01/4.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f75,f290])).
% 33.01/4.53  fof(f294,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f88,f290])).
% 33.01/4.53  fof(f88,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 33.01/4.53    inference(superposition,[],[f29,f75])).
% 33.01/4.53  fof(f3615,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X1),X1),k4_xboole_0(X2,X1)) = X1) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f3446,f261])).
% 33.01/4.53  fof(f3446,plain,(
% 33.01/4.53    ( ! [X15,X16] : (k4_xboole_0(X16,X15) = k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X15)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3370,f593])).
% 33.01/4.53  fof(f593,plain,(
% 33.01/4.53    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f582,f582])).
% 33.01/4.53  fof(f3370,plain,(
% 33.01/4.53    ( ! [X15,X16] : (k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X15) = k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X15)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f115,f3141])).
% 33.01/4.53  fof(f115,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 33.01/4.53    inference(superposition,[],[f34,f38])).
% 33.01/4.53  fof(f26089,plain,(
% 33.01/4.53    ( ! [X28,X29,X27] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X27,k4_xboole_0(X28,X29)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f25777,f1158])).
% 33.01/4.53  fof(f1158,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X4))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f1121,f261])).
% 33.01/4.53  fof(f1121,plain,(
% 33.01/4.53    ( ! [X17,X18,X16] : (k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,X17),X18)) = X17) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f1072,f22])).
% 33.01/4.53  fof(f1072,plain,(
% 33.01/4.53    ( ! [X17,X18,X16] : (k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),X18),k1_xboole_0)) = X17) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f413,f765])).
% 33.01/4.53  fof(f765,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f761,f293])).
% 33.01/4.53  fof(f761,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X1)) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f695,f742])).
% 33.01/4.53  fof(f695,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) )),
% 33.01/4.53    inference(superposition,[],[f115,f38])).
% 33.01/4.53  fof(f413,plain,(
% 33.01/4.53    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))) = X10) )),
% 33.01/4.53    inference(superposition,[],[f261,f40])).
% 33.01/4.53  fof(f25777,plain,(
% 33.01/4.53    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X7),X6),k4_xboole_0(X5,X6))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f21992,f25776])).
% 33.01/4.53  fof(f25776,plain,(
% 33.01/4.53    ( ! [X50,X51,X49] : (k4_xboole_0(k4_xboole_0(X49,X51),X50) = k4_xboole_0(k4_xboole_0(X49,X51),k4_xboole_0(X50,k4_xboole_0(X50,X49)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f25549,f924])).
% 33.01/4.53  fof(f924,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X4)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f923,f763])).
% 33.01/4.53  fof(f923,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X4)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f865,f742])).
% 33.01/4.53  fof(f865,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),k4_xboole_0(X2,k4_xboole_0(X2,X4)))) )),
% 33.01/4.53    inference(superposition,[],[f43,f38])).
% 33.01/4.53  fof(f25549,plain,(
% 33.01/4.53    ( ! [X50,X51,X49] : (k4_xboole_0(k4_xboole_0(X49,X51),k4_xboole_0(X49,k4_xboole_0(X49,X50))) = k4_xboole_0(k4_xboole_0(X49,X51),k4_xboole_0(X50,k4_xboole_0(X50,X49)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f924,f742])).
% 33.01/4.53  fof(f21992,plain,(
% 33.01/4.53    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X7),k4_xboole_0(X6,k4_xboole_0(X6,X5))),k4_xboole_0(X5,X6))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f21823,f22])).
% 33.01/4.53  fof(f21823,plain,(
% 33.01/4.53    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X7),k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0)),k4_xboole_0(X5,X6))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f21460,f7660])).
% 33.01/4.53  fof(f7660,plain,(
% 33.01/4.53    ( ! [X41,X42] : (k4_xboole_0(X42,k4_xboole_0(X42,X41)) = k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X42)),k1_xboole_0)) )),
% 33.01/4.53    inference(superposition,[],[f344,f22])).
% 33.01/4.53  fof(f344,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 33.01/4.53    inference(superposition,[],[f40,f38])).
% 33.01/4.53  fof(f21460,plain,(
% 33.01/4.53    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)),X7)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f7912,f763])).
% 33.01/4.53  fof(f7912,plain,(
% 33.01/4.53    ( ! [X35,X36,X34] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k4_xboole_0(X35,X36)))),X36)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f7679,f290])).
% 33.01/4.53  fof(f7679,plain,(
% 33.01/4.53    ( ! [X35,X36,X34] : (k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k4_xboole_0(X35,X36)))),X36) = k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X35,X36)),k4_xboole_0(X34,k4_xboole_0(X35,X36)))) )),
% 33.01/4.53    inference(superposition,[],[f344,f411])).
% 33.01/4.53  fof(f411,plain,(
% 33.01/4.53    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)) )),
% 33.01/4.53    inference(superposition,[],[f261,f261])).
% 33.01/4.53  fof(f7061,plain,(
% 33.01/4.53    ( ! [X24,X23] : (k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X23,X24)),X23) = k5_xboole_0(X23,k5_xboole_0(X24,k4_xboole_0(X23,X24)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f6963,f22])).
% 33.01/4.53  fof(f6963,plain,(
% 33.01/4.53    ( ! [X24,X23] : (k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X23,X24)),X23) = k5_xboole_0(k4_xboole_0(X23,k1_xboole_0),k5_xboole_0(X24,k4_xboole_0(X23,X24)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f1405,f3824])).
% 33.01/4.53  fof(f3824,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3752,f293])).
% 33.01/4.53  fof(f3752,plain,(
% 33.01/4.53    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f34,f3236])).
% 33.01/4.53  fof(f3236,plain,(
% 33.01/4.53    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = X2) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3235,f712])).
% 33.01/4.53  fof(f712,plain,(
% 33.01/4.53    ( ! [X8,X7] : (k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8)) = X7) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f582,f115])).
% 33.01/4.53  fof(f3235,plain,(
% 33.01/4.53    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3234,f742])).
% 33.01/4.53  fof(f3234,plain,(
% 33.01/4.53    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3064,f535])).
% 33.01/4.53  fof(f535,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f506,f525])).
% 33.01/4.53  fof(f506,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f294,f34])).
% 33.01/4.53  fof(f3064,plain,(
% 33.01/4.53    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f933,f711])).
% 33.01/4.53  fof(f711,plain,(
% 33.01/4.53    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f526,f115])).
% 33.01/4.53  fof(f1405,plain,(
% 33.01/4.53    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),X21)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f593,f711])).
% 33.01/4.53  fof(f616,plain,(
% 33.01/4.53    ( ! [X10,X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,X10)),X10)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f592,f29])).
% 33.01/4.53  fof(f592,plain,(
% 33.01/4.53    ( ! [X4,X3] : (k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f582,f526])).
% 33.01/4.53  fof(f3517,plain,(
% 33.01/4.53    ( ! [X35,X36,X34] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f3422,f1158])).
% 33.01/4.53  fof(f3422,plain,(
% 33.01/4.53    ( ! [X19,X20] : (k1_xboole_0 = k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3421,f290])).
% 33.01/4.53  fof(f3421,plain,(
% 33.01/4.53    ( ! [X19,X20] : (k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3420,f261])).
% 33.01/4.53  fof(f3420,plain,(
% 33.01/4.53    ( ! [X19,X20] : (k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(X19,k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3419,f535])).
% 33.01/4.53  fof(f3419,plain,(
% 33.01/4.53    ( ! [X19,X20] : (k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k5_xboole_0(X19,k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3348,f600])).
% 33.01/4.53  fof(f3348,plain,(
% 33.01/4.53    ( ! [X19,X20] : (k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))) = k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k4_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),k5_xboole_0(k4_xboole_0(X19,k5_xboole_0(X19,k4_xboole_0(X20,X19))),X19)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f3141,f3141])).
% 33.01/4.53  fof(f32009,plain,(
% 33.01/4.53    ( ! [X118,X119] : (k4_xboole_0(k5_xboole_0(X118,X119),k4_xboole_0(X119,X118)) = k5_xboole_0(k4_xboole_0(X118,X119),k4_xboole_0(k4_xboole_0(X119,X118),k5_xboole_0(X118,X119)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f28227,f28227])).
% 33.01/4.53  fof(f28227,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f541,f27233])).
% 33.01/4.53  fof(f541,plain,(
% 33.01/4.53    ( ! [X12,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f512,f525])).
% 33.01/4.53  fof(f512,plain,(
% 33.01/4.53    ( ! [X12,X13,X11] : (k5_xboole_0(k1_xboole_0,X13) = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f294,f29])).
% 33.01/4.53  fof(f53190,plain,(
% 33.01/4.53    ( ! [X61,X62,X63] : (k4_xboole_0(X62,X61) = k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62)))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f41832,f53189])).
% 33.01/4.53  fof(f53189,plain,(
% 33.01/4.53    ( ! [X253,X251,X252] : (k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X253,X251)),X253)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f53188,f380])).
% 33.01/4.53  fof(f53188,plain,(
% 33.01/4.53    ( ! [X253,X251,X252] : (k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X252,k4_xboole_0(X252,k4_xboole_0(X253,X251)))),X253)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f53109,f25877])).
% 33.01/4.53  fof(f25877,plain,(
% 33.01/4.53    ( ! [X85,X83,X84] : (k4_xboole_0(X83,k4_xboole_0(X83,k4_xboole_0(X85,X84))) = k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(X83,X85))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f25876,f7921])).
% 33.01/4.53  fof(f7921,plain,(
% 33.01/4.53    ( ! [X17,X18,X16] : (k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(k4_xboole_0(X17,X18),X16)) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18)))) )),
% 33.01/4.53    inference(forward_demodulation,[],[f7688,f40])).
% 33.01/4.53  fof(f7688,plain,(
% 33.01/4.53    ( ! [X17,X18,X16] : (k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(k4_xboole_0(X17,X18),X16)) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),X18)) )),
% 33.01/4.53    inference(superposition,[],[f344,f38])).
% 33.01/4.53  fof(f25876,plain,(
% 33.01/4.53    ( ! [X85,X83,X84] : (k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(k4_xboole_0(X83,X84),X85)) = k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(X83,X85))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f25640,f380])).
% 33.01/4.53  fof(f25640,plain,(
% 33.01/4.53    ( ! [X85,X83,X84] : (k4_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(k4_xboole_0(X83,X84),X85)) = k4_xboole_0(k4_xboole_0(X83,k4_xboole_0(X83,k4_xboole_0(X83,X84))),k4_xboole_0(X83,X85))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f344,f924])).
% 33.01/4.53  fof(f53109,plain,(
% 33.01/4.53    ( ! [X253,X251,X252] : (k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(k4_xboole_0(X252,X251),k4_xboole_0(X252,X253))),X253)) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f38222,f52942])).
% 33.01/4.53  fof(f52942,plain,(
% 33.01/4.53    ( ! [X103,X105,X104] : (k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105))) = k4_xboole_0(k4_xboole_0(X103,X105),X104)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f52941,f8027])).
% 33.01/4.53  fof(f8027,plain,(
% 33.01/4.53    ( ! [X59,X60,X58] : (k4_xboole_0(k4_xboole_0(X59,X60),X58) = k4_xboole_0(k4_xboole_0(X59,X60),k4_xboole_0(X59,k4_xboole_0(X59,k4_xboole_0(X58,X60))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f7751,f40])).
% 33.01/4.53  fof(f7751,plain,(
% 33.01/4.53    ( ! [X59,X60,X58] : (k4_xboole_0(k4_xboole_0(X59,X60),X58) = k4_xboole_0(k4_xboole_0(X59,X60),k4_xboole_0(k4_xboole_0(X59,k4_xboole_0(X59,X58)),X60))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f742,f344])).
% 33.01/4.53  fof(f52941,plain,(
% 33.01/4.53    ( ! [X103,X105,X104] : (k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f52940,f22])).
% 33.01/4.53  fof(f52940,plain,(
% 33.01/4.53    ( ! [X103,X105,X104] : (k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105))),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f52939,f34])).
% 33.01/4.53  fof(f52939,plain,(
% 33.01/4.53    ( ! [X103,X105,X104] : (k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k5_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X103,k5_xboole_0(X105,k4_xboole_0(X104,X105))))),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f52938,f51294])).
% 33.01/4.53  fof(f51294,plain,(
% 33.01/4.53    ( ! [X588,X590,X589] : (k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590))) = k4_xboole_0(X588,k4_xboole_0(X588,k5_xboole_0(X590,k4_xboole_0(X589,X590))))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f51290,f51293])).
% 33.01/4.53  fof(f51293,plain,(
% 33.01/4.53    ( ! [X592,X593,X591] : (k4_xboole_0(X591,k4_xboole_0(X591,k5_xboole_0(X593,k4_xboole_0(X592,X593)))) = k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(X593,k4_xboole_0(X593,k4_xboole_0(X591,X592))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f51292,f380])).
% 33.01/4.53  fof(f51292,plain,(
% 33.01/4.53    ( ! [X592,X593,X591] : (k4_xboole_0(X591,k4_xboole_0(X591,k5_xboole_0(X593,k4_xboole_0(X592,X593)))) = k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(X593,k4_xboole_0(X593,k4_xboole_0(X591,k4_xboole_0(X591,k4_xboole_0(X591,X592))))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f51291,f40])).
% 33.01/4.53  fof(f51291,plain,(
% 33.01/4.53    ( ! [X592,X593,X591] : (k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(k4_xboole_0(X593,k4_xboole_0(X593,X591)),k4_xboole_0(X591,k4_xboole_0(X591,X592)))) = k4_xboole_0(X591,k4_xboole_0(X591,k5_xboole_0(X593,k4_xboole_0(X592,X593))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f50310,f3186])).
% 33.01/4.53  fof(f3186,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k5_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X4,X3))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f3038,f535])).
% 33.01/4.53  fof(f3038,plain,(
% 33.01/4.53    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X4,X3))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f933,f711])).
% 33.01/4.53  fof(f50310,plain,(
% 33.01/4.53    ( ! [X592,X593,X591] : (k5_xboole_0(k4_xboole_0(X591,k4_xboole_0(X591,X592)),k4_xboole_0(k4_xboole_0(X593,k4_xboole_0(X593,X591)),k4_xboole_0(X591,k4_xboole_0(X591,X592)))) = k5_xboole_0(k4_xboole_0(X593,k4_xboole_0(X593,X591)),k4_xboole_0(X591,k4_xboole_0(X591,k4_xboole_0(X592,X593))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f27235,f893])).
% 33.01/4.53  fof(f893,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 33.01/4.53    inference(superposition,[],[f43,f38])).
% 33.01/4.53  fof(f27235,plain,(
% 33.01/4.53    ( ! [X26,X25] : (k5_xboole_0(X26,k4_xboole_0(X25,X26)) = k5_xboole_0(X25,k4_xboole_0(X26,X25))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f3760,f27231])).
% 33.01/4.53  fof(f3760,plain,(
% 33.01/4.53    ( ! [X26,X25] : (k5_xboole_0(X26,k4_xboole_0(X25,X26)) = k5_xboole_0(X25,k4_xboole_0(k5_xboole_0(X26,k4_xboole_0(X25,X26)),X25))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f712,f3236])).
% 33.01/4.53  fof(f51290,plain,(
% 33.01/4.53    ( ! [X588,X590,X589] : (k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(X590,k4_xboole_0(X590,k4_xboole_0(X588,X589))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f51289,f380])).
% 33.01/4.53  fof(f51289,plain,(
% 33.01/4.53    ( ! [X588,X590,X589] : (k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(X590,k4_xboole_0(X590,k4_xboole_0(X588,k4_xboole_0(X588,k4_xboole_0(X588,X589))))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f51288,f40])).
% 33.01/4.53  fof(f51288,plain,(
% 33.01/4.53    ( ! [X588,X590,X589] : (k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(k4_xboole_0(X590,k4_xboole_0(X590,X588)),k4_xboole_0(X588,k4_xboole_0(X588,X589)))) = k5_xboole_0(k4_xboole_0(X588,X590),k4_xboole_0(X588,k4_xboole_0(X589,X590)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f51287,f600])).
% 33.01/4.53  fof(f51287,plain,(
% 33.01/4.53    ( ! [X588,X590,X589] : (k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(k4_xboole_0(X590,k4_xboole_0(X590,X588)),k4_xboole_0(X588,k4_xboole_0(X588,X589)))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X589,X590)),k4_xboole_0(X588,X590))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f50309,f36281])).
% 33.01/4.53  fof(f36281,plain,(
% 33.01/4.53    ( ! [X420,X422,X421] : (k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(X421,X422),k4_xboole_0(X421,X420))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f36280,f33661])).
% 33.01/4.53  fof(f33661,plain,(
% 33.01/4.53    ( ! [X76,X77,X75] : (k5_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X75,X77)) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f33660,f526])).
% 33.01/4.53  fof(f33660,plain,(
% 33.01/4.53    ( ! [X76,X77,X75] : (k5_xboole_0(X75,k5_xboole_0(X75,k5_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X75,X77)))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f33659,f1241])).
% 33.01/4.53  fof(f1241,plain,(
% 33.01/4.53    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X5),X6)) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f29,f535])).
% 33.01/4.53  fof(f33659,plain,(
% 33.01/4.53    ( ! [X76,X77,X75] : (k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76)))) = k5_xboole_0(X75,k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,X77)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f33658,f1694])).
% 33.01/4.53  fof(f1694,plain,(
% 33.01/4.53    ( ! [X10,X8,X9] : (k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f608,f34])).
% 33.01/4.53  fof(f608,plain,(
% 33.01/4.53    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f601,f29])).
% 33.01/4.53  fof(f601,plain,(
% 33.01/4.53    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f29,f582])).
% 33.01/4.53  fof(f33658,plain,(
% 33.01/4.53    ( ! [X76,X77,X75] : (k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,k4_xboole_0(X75,X77))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,X76))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f33657,f932])).
% 33.01/4.53  fof(f33657,plain,(
% 33.01/4.53    ( ! [X76,X77,X75] : (k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,k4_xboole_0(X75,X77))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X77,k4_xboole_0(X75,k4_xboole_0(X75,X76))))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f33461,f40])).
% 33.01/4.53  fof(f33461,plain,(
% 33.01/4.53    ( ! [X76,X77,X75] : (k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k4_xboole_0(X75,k4_xboole_0(X75,X77))) = k5_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,k4_xboole_0(X76,X77))),k4_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X77)),k4_xboole_0(X75,k4_xboole_0(X75,X76))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f28228,f43])).
% 33.01/4.53  fof(f28228,plain,(
% 33.01/4.53    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f595,f27233])).
% 33.01/4.53  fof(f595,plain,(
% 33.01/4.53    ( ! [X10,X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(X10,k5_xboole_0(X8,k5_xboole_0(X9,X10)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f582,f29])).
% 33.01/4.53  fof(f36280,plain,(
% 33.01/4.53    ( ! [X420,X422,X421] : (k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X422,X420))),k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X420,X422))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f36279,f1554])).
% 33.01/4.53  fof(f1554,plain,(
% 33.01/4.53    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X12))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X10)))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f1553,f40])).
% 33.01/4.53  fof(f1553,plain,(
% 33.01/4.53    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X12) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X10)))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f1493,f1542])).
% 33.01/4.53  fof(f1542,plain,(
% 33.01/4.53    ( ! [X28,X26,X27] : (k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,X27))) = k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28)))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f1541,f932])).
% 33.01/4.53  fof(f1541,plain,(
% 33.01/4.53    ( ! [X28,X26,X27] : (k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,X27))) = k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f1482,f40])).
% 33.01/4.53  fof(f1482,plain,(
% 33.01/4.53    ( ! [X28,X26,X27] : (k4_xboole_0(X28,k4_xboole_0(X26,k4_xboole_0(X26,X27))) = k4_xboole_0(X28,k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X27)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28)))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f742,f40])).
% 33.01/4.53  fof(f1493,plain,(
% 33.01/4.53    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X12) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f742,f40])).
% 33.01/4.53  fof(f36279,plain,(
% 33.01/4.53    ( ! [X420,X422,X421] : (k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X422,k4_xboole_0(X420,k4_xboole_0(X420,X421))))),k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X420,X422))))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f35504,f40])).
% 33.01/4.53  fof(f35504,plain,(
% 33.01/4.53    ( ! [X420,X422,X421] : (k5_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X421,k4_xboole_0(X421,X422)),k4_xboole_0(X420,k4_xboole_0(X420,X421))),k4_xboole_0(X421,k4_xboole_0(X421,k4_xboole_0(X420,X422))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f28228,f876])).
% 33.01/4.53  fof(f876,plain,(
% 33.01/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 33.01/4.53    inference(superposition,[],[f43,f38])).
% 33.01/4.53  fof(f50309,plain,(
% 33.01/4.53    ( ! [X588,X590,X589] : (k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,X589)),k4_xboole_0(k4_xboole_0(X590,k4_xboole_0(X590,X588)),k4_xboole_0(X588,k4_xboole_0(X588,X589)))) = k5_xboole_0(k4_xboole_0(X588,k4_xboole_0(X588,k4_xboole_0(X589,X590))),k4_xboole_0(X590,k4_xboole_0(X590,X588)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f27234,f893])).
% 33.01/4.53  fof(f27234,plain,(
% 33.01/4.53    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X22,X21),X21) = k5_xboole_0(X22,k4_xboole_0(X21,X22))) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f5093,f27231])).
% 33.01/4.53  fof(f5093,plain,(
% 33.01/4.53    ( ! [X21,X22] : (k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21),X21)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f4971,f22])).
% 33.01/4.53  fof(f4971,plain,(
% 33.01/4.53    ( ! [X21,X22] : (k5_xboole_0(X22,k4_xboole_0(X21,X22)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21),k4_xboole_0(X21,k1_xboole_0))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f713,f3824])).
% 33.01/4.53  fof(f713,plain,(
% 33.01/4.53    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f592,f115])).
% 33.01/4.53  fof(f52938,plain,(
% 33.01/4.53    ( ! [X103,X105,X104] : (k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k5_xboole_0(X103,k5_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X104,X105)))),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f52604,f1694])).
% 33.01/4.53  fof(f52604,plain,(
% 33.01/4.53    ( ! [X103,X105,X104] : (k4_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X103,X105),k4_xboole_0(X103,k4_xboole_0(X103,k4_xboole_0(X104,X105)))),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f47514,f8028])).
% 33.01/4.53  fof(f8028,plain,(
% 33.01/4.53    ( ! [X61,X62,X63] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X62,k4_xboole_0(X61,X63))),k4_xboole_0(X62,X63))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f7752,f40])).
% 33.01/4.53  fof(f7752,plain,(
% 33.01/4.53    ( ! [X61,X62,X63] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X62,X61)),X63),k4_xboole_0(X62,X63))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f776,f344])).
% 33.01/4.53  fof(f776,plain,(
% 33.01/4.53    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f765,f38])).
% 33.01/4.53  fof(f38222,plain,(
% 33.01/4.53    ( ! [X253,X251,X252] : (k4_xboole_0(X252,X253) = k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X252,k5_xboole_0(X251,k4_xboole_0(k4_xboole_0(X252,X253),X251)))),X253)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f38009,f27474])).
% 33.01/4.53  fof(f27474,plain,(
% 33.01/4.53    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X4,X5)),k4_xboole_0(X5,X4)) = X4) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f3671,f27235])).
% 33.01/4.53  fof(f38009,plain,(
% 33.01/4.53    ( ! [X253,X251,X252] : (k4_xboole_0(k4_xboole_0(X252,k4_xboole_0(X252,k5_xboole_0(X251,k4_xboole_0(k4_xboole_0(X252,X253),X251)))),X253) = k4_xboole_0(k5_xboole_0(X251,k4_xboole_0(k4_xboole_0(X252,X253),X251)),k4_xboole_0(X251,k4_xboole_0(X252,X253)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f344,f27231])).
% 33.01/4.53  fof(f41832,plain,(
% 33.01/4.53    ( ! [X61,X62,X63] : (k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))) = k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))),X61)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f41500,f271])).
% 33.01/4.53  fof(f41500,plain,(
% 33.01/4.53    ( ! [X61,X62,X63] : (k4_xboole_0(k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))),X61) = k5_xboole_0(k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X63,X62))),k1_xboole_0)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f115,f21061])).
% 33.01/4.53  fof(f21061,plain,(
% 33.01/4.53    ( ! [X12,X10,X11] : (k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X12,X11)))))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f7902,f40])).
% 33.01/4.53  fof(f7902,plain,(
% 33.01/4.53    ( ! [X19,X20,X18] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),k4_xboole_0(X19,k4_xboole_0(X20,X18)))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f7673,f290])).
% 33.01/4.53  fof(f7673,plain,(
% 33.01/4.53    ( ! [X19,X20,X18] : (k4_xboole_0(X18,X18) = k4_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),k4_xboole_0(X19,k4_xboole_0(X20,X18)))) )),
% 33.01/4.53    inference(superposition,[],[f344,f413])).
% 33.01/4.53  fof(f54367,plain,(
% 33.01/4.53    ( ! [X255,X256] : (k5_xboole_0(X255,X256) = k4_xboole_0(k5_xboole_0(X255,k4_xboole_0(X256,X255)),k4_xboole_0(X255,k5_xboole_0(X255,X256)))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f27474,f53952])).
% 33.01/4.53  fof(f53952,plain,(
% 33.01/4.53    ( ! [X21,X22] : (k4_xboole_0(X22,X21) = k4_xboole_0(k5_xboole_0(X21,X22),X21)) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f53925,f1405])).
% 33.01/4.53  fof(f53925,plain,(
% 33.01/4.53    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X21,X22),X21) = k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22)) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f30650,f53625])).
% 33.01/4.53  fof(f30650,plain,(
% 33.01/4.53    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X21,X22),X21) = k5_xboole_0(k4_xboole_0(X21,k5_xboole_0(X21,X22)),X22)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f27872,f526])).
% 33.01/4.53  fof(f27872,plain,(
% 33.01/4.53    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X6,X5))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f27236,f2071])).
% 33.01/4.53  fof(f2071,plain,(
% 33.01/4.53    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24))) ) | ~spl2_2),
% 33.01/4.53    inference(forward_demodulation,[],[f2018,f29])).
% 33.01/4.53  fof(f2018,plain,(
% 33.01/4.53    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f1286,f582])).
% 33.01/4.53  fof(f1286,plain,(
% 33.01/4.53    ( ! [X21,X22,X20] : (k5_xboole_0(X21,X20) = k5_xboole_0(k5_xboole_0(X22,X20),k5_xboole_0(X22,X21))) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f541,f582])).
% 33.01/4.53  fof(f27236,plain,(
% 33.01/4.53    ( ! [X15,X16] : (k4_xboole_0(X16,X15) = k5_xboole_0(k5_xboole_0(X16,k4_xboole_0(X15,X16)),X15)) ) | ~spl2_2),
% 33.01/4.53    inference(backward_demodulation,[],[f3756,f27231])).
% 33.01/4.53  fof(f3756,plain,(
% 33.01/4.53    ( ! [X15,X16] : (k4_xboole_0(k5_xboole_0(X16,k4_xboole_0(X15,X16)),X15) = k5_xboole_0(k5_xboole_0(X16,k4_xboole_0(X15,X16)),X15)) ) | ~spl2_2),
% 33.01/4.53    inference(superposition,[],[f115,f3236])).
% 33.01/4.53  fof(f47,plain,(
% 33.01/4.53    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 33.01/4.53    inference(avatar_component_clause,[],[f45])).
% 33.01/4.53  fof(f45,plain,(
% 33.01/4.53    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 33.01/4.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 33.01/4.53  fof(f57,plain,(
% 33.01/4.53    spl2_2),
% 33.01/4.53    inference(avatar_split_clause,[],[f52,f54])).
% 33.01/4.53  fof(f52,plain,(
% 33.01/4.53    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 33.01/4.53    inference(superposition,[],[f36,f22])).
% 33.01/4.53  fof(f48,plain,(
% 33.01/4.53    ~spl2_1),
% 33.01/4.53    inference(avatar_split_clause,[],[f35,f45])).
% 33.01/4.53  fof(f35,plain,(
% 33.01/4.53    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 33.01/4.53    inference(definition_unfolding,[],[f20,f26,f28])).
% 33.01/4.53  fof(f20,plain,(
% 33.01/4.53    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 33.01/4.53    inference(cnf_transformation,[],[f19])).
% 33.01/4.53  fof(f19,plain,(
% 33.01/4.53    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 33.01/4.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 33.01/4.53  fof(f18,plain,(
% 33.01/4.53    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 33.01/4.53    introduced(choice_axiom,[])).
% 33.01/4.53  fof(f17,plain,(
% 33.01/4.53    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 33.01/4.53    inference(ennf_transformation,[],[f15])).
% 33.01/4.53  fof(f15,negated_conjecture,(
% 33.01/4.53    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 33.01/4.53    inference(negated_conjecture,[],[f14])).
% 33.01/4.53  fof(f14,conjecture,(
% 33.01/4.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 33.01/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 33.01/4.53  % SZS output end Proof for theBenchmark
% 33.01/4.53  % (7821)------------------------------
% 33.01/4.53  % (7821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.01/4.53  % (7821)Termination reason: Refutation
% 33.01/4.53  
% 33.01/4.53  % (7821)Memory used [KB]: 132407
% 33.01/4.53  % (7821)Time elapsed: 4.076 s
% 33.01/4.53  % (7821)------------------------------
% 33.01/4.53  % (7821)------------------------------
% 33.01/4.54  % (7810)Success in time 4.176 s
%------------------------------------------------------------------------------
