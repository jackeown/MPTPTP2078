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
% DateTime   : Thu Dec  3 12:32:23 EST 2020

% Result     : Theorem 28.52s
% Output     : Refutation 28.52s
% Verified   : 
% Statistics : Number of formulae       :  187 (124698 expanded)
%              Number of leaves         :   15 (42605 expanded)
%              Depth                    :   49
%              Number of atoms          :  191 (124703 expanded)
%              Number of equality atoms :  184 (124695 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55034,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f55013])).

fof(f55013,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f55011])).

fof(f55011,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f45,f55010])).

fof(f55010,plain,(
    ! [X288,X287] : k5_xboole_0(X287,X288) = k4_xboole_0(k5_xboole_0(X287,k4_xboole_0(X288,X287)),k4_xboole_0(X287,k4_xboole_0(X287,X288))) ),
    inference(forward_demodulation,[],[f54348,f54750])).

fof(f54750,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k4_xboole_0(X33,X34)) = k4_xboole_0(X33,k5_xboole_0(X33,X34)) ),
    inference(forward_demodulation,[],[f54749,f232])).

fof(f232,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f217,f227])).

fof(f227,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f216,f54])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f35,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f216,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f131,f132])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f77,f121])).

fof(f121,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(superposition,[],[f101,f50])).

fof(f101,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(superposition,[],[f47,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f38,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f27,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f25,f27])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f32,f36])).

fof(f131,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f87,f121])).

fof(f87,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2)) ),
    inference(superposition,[],[f29,f77])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f217,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f131,f32])).

fof(f54749,plain,(
    ! [X33,X34] : k5_xboole_0(X33,k4_xboole_0(X33,X34)) = k4_xboole_0(X33,k5_xboole_0(X33,X34)) ),
    inference(forward_demodulation,[],[f54251,f28118])).

fof(f28118,plain,(
    ! [X103,X104] : k4_xboole_0(X103,X104) = k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X104,X103)) ),
    inference(forward_demodulation,[],[f28114,f227])).

fof(f28114,plain,(
    ! [X103,X104] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X103,X104)) = k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X104,X103)) ),
    inference(backward_demodulation,[],[f27355,f27854])).

fof(f27854,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f1874,f25591])).

fof(f25591,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15)) ),
    inference(superposition,[],[f290,f25216])).

fof(f25216,plain,(
    ! [X83,X82] : k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(X83,X82)) ),
    inference(superposition,[],[f22175,f322])).

fof(f322,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    inference(superposition,[],[f290,f290])).

fof(f22175,plain,(
    ! [X21,X22] : k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,X22),X22)) = k4_xboole_0(X22,k5_xboole_0(X21,X22)) ),
    inference(backward_demodulation,[],[f22153,f22174])).

fof(f22174,plain,(
    ! [X66,X65] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k4_xboole_0(X66,k5_xboole_0(X65,X66)) ),
    inference(forward_demodulation,[],[f22173,f32])).

fof(f22173,plain,(
    ! [X66,X65] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k5_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(X66,k5_xboole_0(X65,X66)))) ),
    inference(forward_demodulation,[],[f22172,f1355])).

fof(f1355,plain,(
    ! [X43,X41,X42] : k5_xboole_0(X43,k4_xboole_0(X41,k4_xboole_0(X41,X42))) = k5_xboole_0(X42,k5_xboole_0(X43,k4_xboole_0(X42,X41))) ),
    inference(superposition,[],[f325,f548])).

fof(f548,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5) ),
    inference(superposition,[],[f231,f297])).

fof(f297,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f109,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f27,f27])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f109,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f39,f101])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f28,f25,f27])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f231,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f228,f227])).

fof(f228,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f188,f227])).

fof(f188,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f140])).

fof(f140,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    inference(superposition,[],[f132,f60])).

fof(f60,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f29,f54])).

fof(f325,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12))) ),
    inference(superposition,[],[f290,f29])).

fof(f22172,plain,(
    ! [X66,X65] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k5_xboole_0(k5_xboole_0(X65,X66),k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66))) ),
    inference(forward_demodulation,[],[f22046,f121])).

fof(f22046,plain,(
    ! [X66,X65] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X65,X66),k1_xboole_0),k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66))) ),
    inference(superposition,[],[f548,f21848])).

fof(f21848,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2))) ),
    inference(forward_demodulation,[],[f21847,f330])).

fof(f330,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f231,f290])).

fof(f21847,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2)) ),
    inference(forward_demodulation,[],[f21573,f4496])).

fof(f4496,plain,(
    ! [X83,X84,X82] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X84),X83) = k5_xboole_0(X82,k4_xboole_0(X84,k4_xboole_0(X84,k5_xboole_0(X82,X83)))) ),
    inference(superposition,[],[f338,f427])).

fof(f427,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f322,f89])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f32,f37])).

fof(f338,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6))) ),
    inference(forward_demodulation,[],[f331,f29])).

fof(f331,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6)) ),
    inference(superposition,[],[f29,f290])).

fof(f21573,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2))))) ),
    inference(superposition,[],[f65,f232])).

fof(f65,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,k5_xboole_0(X2,X3))))) ),
    inference(superposition,[],[f36,f29])).

fof(f22153,plain,(
    ! [X21,X22] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,X22),X22)) ),
    inference(forward_demodulation,[],[f22152,f1349])).

fof(f1349,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X25,X23) = k5_xboole_0(k5_xboole_0(X24,X23),k5_xboole_0(X25,X24)) ),
    inference(superposition,[],[f325,f290])).

fof(f22152,plain,(
    ! [X21,X22] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22)) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22)) ),
    inference(forward_demodulation,[],[f22028,f121])).

fof(f22028,plain,(
    ! [X21,X22] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22)) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k4_xboole_0(k5_xboole_0(X21,X22),k1_xboole_0)) ),
    inference(superposition,[],[f89,f21848])).

fof(f290,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f278,f54])).

fof(f278,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f231,f133])).

fof(f133,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f84,f121])).

fof(f84,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0))) ),
    inference(superposition,[],[f77,f29])).

fof(f1874,plain,(
    ! [X24,X23,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X22,X23))) ),
    inference(superposition,[],[f36,f1730])).

fof(f1730,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16)) ),
    inference(superposition,[],[f1676,f101])).

fof(f1676,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21 ),
    inference(forward_demodulation,[],[f1608,f121])).

fof(f1608,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21 ),
    inference(superposition,[],[f1460,f446])).

fof(f446,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(backward_demodulation,[],[f91,f426])).

fof(f426,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9 ),
    inference(superposition,[],[f321,f89])).

fof(f321,plain,(
    ! [X4,X3] : k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3 ),
    inference(superposition,[],[f290,f231])).

fof(f91,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ),
    inference(superposition,[],[f36,f37])).

fof(f1460,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X26,X27)))) = X27 ),
    inference(superposition,[],[f101,f40])).

fof(f27355,plain,(
    ! [X103,X104] : k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X104,X103)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X104,X103),k5_xboole_0(X103,X104)),k4_xboole_0(X103,X104)) ),
    inference(superposition,[],[f25584,f25216])).

fof(f25584,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,X13)) ),
    inference(superposition,[],[f25216,f330])).

fof(f54251,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k5_xboole_0(X33,X34)) = k5_xboole_0(X33,k4_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(X34,X33))) ),
    inference(superposition,[],[f89,f53739])).

fof(f53739,plain,(
    ! [X61,X60] : k4_xboole_0(X61,X60) = k4_xboole_0(k5_xboole_0(X60,X61),X60) ),
    inference(forward_demodulation,[],[f53738,f124])).

fof(f124,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7) ),
    inference(superposition,[],[f101,f101])).

fof(f53738,plain,(
    ! [X61,X60] : k4_xboole_0(k4_xboole_0(X61,X60),X60) = k4_xboole_0(k5_xboole_0(X60,X61),X60) ),
    inference(forward_demodulation,[],[f53737,f28844])).

fof(f28844,plain,(
    ! [X47,X48,X49] : k4_xboole_0(k4_xboole_0(X47,X48),X49) = k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X48,X47),X49))) ),
    inference(forward_demodulation,[],[f28694,f121])).

fof(f28694,plain,(
    ! [X47,X48,X49] : k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X48,X47),X49))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X47,X48),k1_xboole_0),X49) ),
    inference(superposition,[],[f40,f27854])).

fof(f53737,plain,(
    ! [X61,X60] : k4_xboole_0(k5_xboole_0(X60,X61),X60) = k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k5_xboole_0(X60,X61),X60))) ),
    inference(forward_demodulation,[],[f53355,f121])).

fof(f53355,plain,(
    ! [X61,X60] : k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k5_xboole_0(X60,X61),X60))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X60,X61),X60),k1_xboole_0) ),
    inference(superposition,[],[f37,f52032])).

fof(f52032,plain,(
    ! [X177,X176] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X176,X177),X176),k4_xboole_0(X177,X176)) ),
    inference(superposition,[],[f51231,f28111])).

fof(f28111,plain,(
    ! [X105,X106] : k4_xboole_0(X106,X105) = k4_xboole_0(k5_xboole_0(X105,X106),k4_xboole_0(X105,X106)) ),
    inference(forward_demodulation,[],[f28108,f227])).

fof(f28108,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,X106),k4_xboole_0(X105,X106)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X106,X105)) ),
    inference(backward_demodulation,[],[f27356,f27853])).

fof(f27853,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,X0)) ),
    inference(superposition,[],[f1887,f25591])).

fof(f1887,plain,(
    ! [X64,X62,X63] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X62,X63),k5_xboole_0(k4_xboole_0(X63,X64),k4_xboole_0(X62,X63))) ),
    inference(superposition,[],[f337,f1730])).

fof(f337,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,k4_xboole_0(X10,X9))) ),
    inference(backward_demodulation,[],[f127,f330])).

fof(f127,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(k4_xboole_0(X10,X9),X9)) ),
    inference(superposition,[],[f36,f101])).

fof(f27356,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,X106),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),k5_xboole_0(X105,X106)),k4_xboole_0(X106,X105)) ),
    inference(superposition,[],[f25584,f25217])).

fof(f25217,plain,(
    ! [X85,X84] : k4_xboole_0(X85,X84) = k5_xboole_0(k5_xboole_0(X84,X85),k4_xboole_0(X84,X85)) ),
    inference(superposition,[],[f22175,f321])).

fof(f51231,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f50850,f1730])).

fof(f50850,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f50849,f231])).

fof(f50849,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X3,X2)),X4)) ),
    inference(forward_demodulation,[],[f50848,f25591])).

fof(f50848,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4)) ),
    inference(forward_demodulation,[],[f50847,f1354])).

fof(f1354,plain,(
    ! [X39,X38,X40] : k5_xboole_0(X40,k4_xboole_0(X38,k4_xboole_0(X38,X39))) = k5_xboole_0(X38,k5_xboole_0(X40,k4_xboole_0(X38,X39))) ),
    inference(superposition,[],[f325,f309])).

fof(f309,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f231,f109])).

fof(f50847,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) ),
    inference(forward_demodulation,[],[f50572,f121])).

fof(f50572,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k1_xboole_0)),X4)) ),
    inference(superposition,[],[f42342,f19320])).

fof(f19320,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f19319,f50])).

fof(f19319,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,X36)) ),
    inference(forward_demodulation,[],[f19318,f121])).

fof(f19318,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f19317,f50])).

fof(f19317,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,X35)))) ),
    inference(forward_demodulation,[],[f19316,f5052])).

fof(f5052,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,X30))) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,X28))))) ),
    inference(backward_demodulation,[],[f1543,f5044])).

fof(f5044,plain,(
    ! [X70,X72,X71] : k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,X71))) = k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,k4_xboole_0(X71,X72))))) ),
    inference(backward_demodulation,[],[f1563,f4755])).

fof(f4755,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))))) ),
    inference(superposition,[],[f48,f40])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f41,f40])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f31,f27,f27,f27,f27])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1563,plain,(
    ! [X70,X72,X71] : k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,X71))) = k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,X72))))))) ),
    inference(forward_demodulation,[],[f1475,f40])).

fof(f1475,plain,(
    ! [X70,X72,X71] : k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,X71))) = k4_xboole_0(X72,k4_xboole_0(k4_xboole_0(X70,k4_xboole_0(X70,X71)),k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,X72))))) ),
    inference(superposition,[],[f513,f40])).

fof(f513,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f512,f89])).

fof(f512,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f494,f121])).

fof(f494,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0)) ),
    inference(superposition,[],[f89,f449])).

fof(f449,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f446,f37])).

fof(f1543,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,k4_xboole_0(X28,k4_xboole_0(X28,X29))))))) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,X30))) ),
    inference(forward_demodulation,[],[f1447,f40])).

fof(f1447,plain,(
    ! [X30,X28,X29] : k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(X28,X29)),X30) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,k4_xboole_0(X28,k4_xboole_0(X28,X29))))))) ),
    inference(superposition,[],[f40,f513])).

fof(f19316,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X35,X36)))))) ),
    inference(forward_demodulation,[],[f19315,f40])).

fof(f19315,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36)))) ),
    inference(forward_demodulation,[],[f19061,f121])).

fof(f19061,plain,(
    ! [X35,X36] : k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0) ),
    inference(superposition,[],[f37,f923])).

fof(f923,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f922,f50])).

fof(f922,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X10) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f921,f121])).

fof(f921,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f920,f50])).

fof(f920,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X9))) ),
    inference(forward_demodulation,[],[f878,f40])).

fof(f878,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(superposition,[],[f513,f513])).

fof(f42342,plain,(
    ! [X61,X62,X60] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X60,X62),k4_xboole_0(k5_xboole_0(X60,k4_xboole_0(X61,X60)),X62)) ),
    inference(superposition,[],[f449,f1504])).

fof(f1504,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22) ),
    inference(forward_demodulation,[],[f1419,f121])).

fof(f1419,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22) ),
    inference(superposition,[],[f40,f36])).

fof(f54348,plain,(
    ! [X288,X287] : k5_xboole_0(X287,X288) = k4_xboole_0(k5_xboole_0(X287,k4_xboole_0(X288,X287)),k4_xboole_0(X287,k5_xboole_0(X287,X288))) ),
    inference(superposition,[],[f31711,f53739])).

fof(f31711,plain,(
    ! [X275,X274] : k4_xboole_0(k5_xboole_0(X275,k4_xboole_0(X274,X275)),k4_xboole_0(X275,X274)) = X274 ),
    inference(forward_demodulation,[],[f31710,f54])).

fof(f31710,plain,(
    ! [X275,X274] : k5_xboole_0(X274,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X275,k4_xboole_0(X274,X275)),k4_xboole_0(X275,X274)) ),
    inference(forward_demodulation,[],[f31497,f18199])).

fof(f18199,plain,(
    ! [X103,X105,X104] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X103,X105),k5_xboole_0(X103,k4_xboole_0(X104,X103))) ),
    inference(superposition,[],[f18079,f621])).

fof(f621,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9 ),
    inference(forward_demodulation,[],[f620,f321])).

fof(f620,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f606,f121])).

fof(f606,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0)) ),
    inference(superposition,[],[f89,f337])).

fof(f18079,plain,(
    ! [X41,X42,X40] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X40,X41),X42),X40) ),
    inference(forward_demodulation,[],[f17964,f121])).

fof(f17964,plain,(
    ! [X41,X42,X40] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X40,X41),X42),k1_xboole_0),X40) ),
    inference(superposition,[],[f17752,f446])).

fof(f17752,plain,(
    ! [X57,X58,X56] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(X56,X57))),X56) ),
    inference(forward_demodulation,[],[f17607,f121])).

fof(f17607,plain,(
    ! [X57,X58,X56] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k1_xboole_0))),X56) ),
    inference(superposition,[],[f5042,f446])).

fof(f5042,plain,(
    ! [X66,X64,X65] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,k4_xboole_0(X65,X66)))),X66) ),
    inference(backward_demodulation,[],[f1561,f4755])).

fof(f1561,plain,(
    ! [X66,X64,X65] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,X66)))))),X66) ),
    inference(forward_demodulation,[],[f1473,f40])).

fof(f1473,plain,(
    ! [X66,X64,X65] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,X65)),k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,X66)))),X66) ),
    inference(superposition,[],[f449,f40])).

fof(f31497,plain,(
    ! [X275,X274] : k5_xboole_0(X274,k4_xboole_0(k4_xboole_0(X275,X274),k5_xboole_0(X275,k4_xboole_0(X274,X275)))) = k4_xboole_0(k5_xboole_0(X275,k4_xboole_0(X274,X275)),k4_xboole_0(X275,X274)) ),
    inference(superposition,[],[f22175,f25800])).

fof(f25800,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(forward_demodulation,[],[f25580,f330])).

fof(f25580,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),X4)) ),
    inference(superposition,[],[f25216,f2226])).

fof(f2226,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24)) ),
    inference(forward_demodulation,[],[f2168,f29])).

fof(f2168,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24) ),
    inference(superposition,[],[f805,f290])).

fof(f805,plain,(
    ! [X21,X22,X20] : k5_xboole_0(X21,X20) = k5_xboole_0(k5_xboole_0(X22,X20),k5_xboole_0(X22,X21)) ),
    inference(superposition,[],[f236,f290])).

fof(f236,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) = X10 ),
    inference(forward_demodulation,[],[f221,f227])).

fof(f221,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) ),
    inference(superposition,[],[f131,f29])).

fof(f45,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f33,f43])).

fof(f33,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f25,f27])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:39:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (25737)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (25728)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (25724)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (25725)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (25733)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (25723)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (25726)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (25734)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (25727)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (25735)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (25736)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (25733)Refutation not found, incomplete strategy% (25733)------------------------------
% 0.20/0.48  % (25733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25733)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (25733)Memory used [KB]: 10490
% 0.20/0.48  % (25733)Time elapsed: 0.066 s
% 0.20/0.48  % (25733)------------------------------
% 0.20/0.48  % (25733)------------------------------
% 0.20/0.49  % (25731)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (25722)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (25738)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (25732)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (25729)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (25730)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (25739)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 4.74/1.02  % (25726)Time limit reached!
% 4.74/1.02  % (25726)------------------------------
% 4.74/1.02  % (25726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.02  % (25726)Termination reason: Time limit
% 4.74/1.02  
% 4.74/1.02  % (25726)Memory used [KB]: 21748
% 4.74/1.02  % (25726)Time elapsed: 0.602 s
% 4.74/1.02  % (25726)------------------------------
% 4.74/1.02  % (25726)------------------------------
% 12.44/1.95  % (25728)Time limit reached!
% 12.44/1.95  % (25728)------------------------------
% 12.44/1.95  % (25728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.44/1.95  % (25728)Termination reason: Time limit
% 12.44/1.95  % (25728)Termination phase: Saturation
% 12.44/1.95  
% 12.44/1.95  % (25728)Memory used [KB]: 40937
% 12.44/1.95  % (25728)Time elapsed: 1.500 s
% 12.44/1.95  % (25728)------------------------------
% 12.44/1.95  % (25728)------------------------------
% 12.44/1.97  % (25727)Time limit reached!
% 12.44/1.97  % (25727)------------------------------
% 12.44/1.97  % (25727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.44/1.97  % (25727)Termination reason: Time limit
% 12.44/1.97  % (25727)Termination phase: Saturation
% 12.44/1.97  
% 12.44/1.97  % (25727)Memory used [KB]: 44135
% 12.44/1.97  % (25727)Time elapsed: 1.500 s
% 12.44/1.97  % (25727)------------------------------
% 12.44/1.97  % (25727)------------------------------
% 14.30/2.22  % (25724)Time limit reached!
% 14.30/2.22  % (25724)------------------------------
% 14.30/2.22  % (25724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.96/2.23  % (25724)Termination reason: Time limit
% 14.96/2.23  
% 14.96/2.23  % (25724)Memory used [KB]: 44519
% 14.96/2.23  % (25724)Time elapsed: 1.804 s
% 14.96/2.23  % (25724)------------------------------
% 14.96/2.23  % (25724)------------------------------
% 17.85/2.63  % (25734)Time limit reached!
% 17.85/2.63  % (25734)------------------------------
% 17.85/2.63  % (25734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.85/2.63  % (25734)Termination reason: Time limit
% 17.85/2.63  
% 17.85/2.63  % (25734)Memory used [KB]: 67802
% 17.85/2.63  % (25734)Time elapsed: 2.206 s
% 17.85/2.63  % (25734)------------------------------
% 17.85/2.63  % (25734)------------------------------
% 28.52/3.94  % (25732)Refutation found. Thanks to Tanya!
% 28.52/3.94  % SZS status Theorem for theBenchmark
% 28.52/3.94  % SZS output start Proof for theBenchmark
% 28.52/3.94  fof(f55034,plain,(
% 28.52/3.94    $false),
% 28.52/3.94    inference(avatar_sat_refutation,[],[f46,f55013])).
% 28.52/3.94  fof(f55013,plain,(
% 28.52/3.94    spl2_1),
% 28.52/3.94    inference(avatar_contradiction_clause,[],[f55011])).
% 28.52/3.94  fof(f55011,plain,(
% 28.52/3.94    $false | spl2_1),
% 28.52/3.94    inference(subsumption_resolution,[],[f45,f55010])).
% 28.52/3.94  fof(f55010,plain,(
% 28.52/3.94    ( ! [X288,X287] : (k5_xboole_0(X287,X288) = k4_xboole_0(k5_xboole_0(X287,k4_xboole_0(X288,X287)),k4_xboole_0(X287,k4_xboole_0(X287,X288)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f54348,f54750])).
% 28.52/3.94  fof(f54750,plain,(
% 28.52/3.94    ( ! [X33,X34] : (k4_xboole_0(X33,k4_xboole_0(X33,X34)) = k4_xboole_0(X33,k5_xboole_0(X33,X34))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f54749,f232])).
% 28.52/3.94  fof(f232,plain,(
% 28.52/3.94    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f217,f227])).
% 28.52/3.94  fof(f227,plain,(
% 28.52/3.94    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 28.52/3.94    inference(forward_demodulation,[],[f216,f54])).
% 28.52/3.94  fof(f54,plain,(
% 28.52/3.94    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 28.52/3.94    inference(backward_demodulation,[],[f35,f50])).
% 28.52/3.94  fof(f50,plain,(
% 28.52/3.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 28.52/3.94    inference(superposition,[],[f36,f34])).
% 28.52/3.94  fof(f34,plain,(
% 28.52/3.94    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 28.52/3.94    inference(definition_unfolding,[],[f20,f25])).
% 28.52/3.94  fof(f25,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 28.52/3.94    inference(cnf_transformation,[],[f12])).
% 28.52/3.94  fof(f12,axiom,(
% 28.52/3.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 28.52/3.94  fof(f20,plain,(
% 28.52/3.94    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 28.52/3.94    inference(cnf_transformation,[],[f5])).
% 28.52/3.94  fof(f5,axiom,(
% 28.52/3.94    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 28.52/3.94  fof(f36,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 28.52/3.94    inference(definition_unfolding,[],[f22,f25])).
% 28.52/3.94  fof(f22,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 28.52/3.94    inference(cnf_transformation,[],[f7])).
% 28.52/3.94  fof(f7,axiom,(
% 28.52/3.94    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 28.52/3.94  fof(f35,plain,(
% 28.52/3.94    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 28.52/3.94    inference(definition_unfolding,[],[f21,f25])).
% 28.52/3.94  fof(f21,plain,(
% 28.52/3.94    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 28.52/3.94    inference(cnf_transformation,[],[f15])).
% 28.52/3.94  fof(f15,plain,(
% 28.52/3.94    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 28.52/3.94    inference(rectify,[],[f2])).
% 28.52/3.94  fof(f2,axiom,(
% 28.52/3.94    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 28.52/3.94  fof(f216,plain,(
% 28.52/3.94    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 28.52/3.94    inference(superposition,[],[f131,f132])).
% 28.52/3.94  fof(f132,plain,(
% 28.52/3.94    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 28.52/3.94    inference(backward_demodulation,[],[f77,f121])).
% 28.52/3.94  fof(f121,plain,(
% 28.52/3.94    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 28.52/3.94    inference(superposition,[],[f101,f50])).
% 28.52/3.94  fof(f101,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 28.52/3.94    inference(superposition,[],[f47,f32])).
% 28.52/3.94  fof(f32,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 28.52/3.94    inference(definition_unfolding,[],[f26,f27])).
% 28.52/3.94  fof(f27,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 28.52/3.94    inference(cnf_transformation,[],[f8])).
% 28.52/3.94  fof(f8,axiom,(
% 28.52/3.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 28.52/3.94  fof(f26,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 28.52/3.94    inference(cnf_transformation,[],[f3])).
% 28.52/3.94  fof(f3,axiom,(
% 28.52/3.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 28.52/3.94  fof(f47,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 28.52/3.94    inference(backward_demodulation,[],[f38,f40])).
% 28.52/3.94  fof(f40,plain,(
% 28.52/3.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 28.52/3.94    inference(definition_unfolding,[],[f30,f27,f27])).
% 28.52/3.94  fof(f30,plain,(
% 28.52/3.94    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 28.52/3.94    inference(cnf_transformation,[],[f9])).
% 28.52/3.94  fof(f9,axiom,(
% 28.52/3.94    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 28.52/3.94  fof(f38,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 28.52/3.94    inference(definition_unfolding,[],[f24,f25,f27])).
% 28.52/3.94  fof(f24,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 28.52/3.94    inference(cnf_transformation,[],[f6])).
% 28.52/3.94  fof(f6,axiom,(
% 28.52/3.94    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 28.52/3.94  fof(f77,plain,(
% 28.52/3.94    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 28.52/3.94    inference(superposition,[],[f32,f36])).
% 28.52/3.94  fof(f131,plain,(
% 28.52/3.94    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f87,f121])).
% 28.52/3.94  fof(f87,plain,(
% 28.52/3.94    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2))) )),
% 28.52/3.94    inference(superposition,[],[f29,f77])).
% 28.52/3.94  fof(f29,plain,(
% 28.52/3.94    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 28.52/3.94    inference(cnf_transformation,[],[f11])).
% 28.52/3.94  fof(f11,axiom,(
% 28.52/3.94    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 28.52/3.94  fof(f217,plain,(
% 28.52/3.94    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 28.52/3.94    inference(superposition,[],[f131,f32])).
% 28.52/3.94  fof(f54749,plain,(
% 28.52/3.94    ( ! [X33,X34] : (k5_xboole_0(X33,k4_xboole_0(X33,X34)) = k4_xboole_0(X33,k5_xboole_0(X33,X34))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f54251,f28118])).
% 28.52/3.94  fof(f28118,plain,(
% 28.52/3.94    ( ! [X103,X104] : (k4_xboole_0(X103,X104) = k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X104,X103))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f28114,f227])).
% 28.52/3.94  fof(f28114,plain,(
% 28.52/3.94    ( ! [X103,X104] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X103,X104)) = k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X104,X103))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f27355,f27854])).
% 28.52/3.94  fof(f27854,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 28.52/3.94    inference(superposition,[],[f1874,f25591])).
% 28.52/3.94  fof(f25591,plain,(
% 28.52/3.94    ( ! [X14,X15] : (k5_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15))) )),
% 28.52/3.94    inference(superposition,[],[f290,f25216])).
% 28.52/3.94  fof(f25216,plain,(
% 28.52/3.94    ( ! [X83,X82] : (k4_xboole_0(X82,X83) = k5_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(X83,X82))) )),
% 28.52/3.94    inference(superposition,[],[f22175,f322])).
% 28.52/3.94  fof(f322,plain,(
% 28.52/3.94    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) )),
% 28.52/3.94    inference(superposition,[],[f290,f290])).
% 28.52/3.94  fof(f22175,plain,(
% 28.52/3.94    ( ! [X21,X22] : (k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,X22),X22)) = k4_xboole_0(X22,k5_xboole_0(X21,X22))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f22153,f22174])).
% 28.52/3.94  fof(f22174,plain,(
% 28.52/3.94    ( ! [X66,X65] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k4_xboole_0(X66,k5_xboole_0(X65,X66))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f22173,f32])).
% 28.52/3.94  fof(f22173,plain,(
% 28.52/3.94    ( ! [X66,X65] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k5_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(X66,k5_xboole_0(X65,X66))))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f22172,f1355])).
% 28.52/3.94  fof(f1355,plain,(
% 28.52/3.94    ( ! [X43,X41,X42] : (k5_xboole_0(X43,k4_xboole_0(X41,k4_xboole_0(X41,X42))) = k5_xboole_0(X42,k5_xboole_0(X43,k4_xboole_0(X42,X41)))) )),
% 28.52/3.94    inference(superposition,[],[f325,f548])).
% 28.52/3.94  fof(f548,plain,(
% 28.52/3.94    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5)) )),
% 28.52/3.94    inference(superposition,[],[f231,f297])).
% 28.52/3.94  fof(f297,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 28.52/3.94    inference(superposition,[],[f109,f37])).
% 28.52/3.94  fof(f37,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 28.52/3.94    inference(definition_unfolding,[],[f23,f27,f27])).
% 28.52/3.94  fof(f23,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 28.52/3.94    inference(cnf_transformation,[],[f1])).
% 28.52/3.94  fof(f1,axiom,(
% 28.52/3.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 28.52/3.94  fof(f109,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 28.52/3.94    inference(backward_demodulation,[],[f39,f101])).
% 28.52/3.94  fof(f39,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 28.52/3.94    inference(definition_unfolding,[],[f28,f25,f27])).
% 28.52/3.94  fof(f28,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 28.52/3.94    inference(cnf_transformation,[],[f10])).
% 28.52/3.94  fof(f10,axiom,(
% 28.52/3.94    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 28.52/3.94  fof(f231,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 28.52/3.94    inference(forward_demodulation,[],[f228,f227])).
% 28.52/3.94  fof(f228,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = X1) )),
% 28.52/3.94    inference(backward_demodulation,[],[f188,f227])).
% 28.52/3.94  fof(f188,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1))) )),
% 28.52/3.94    inference(superposition,[],[f29,f140])).
% 28.52/3.94  fof(f140,plain,(
% 28.52/3.94    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) )),
% 28.52/3.94    inference(superposition,[],[f132,f60])).
% 28.52/3.94  fof(f60,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X2,X3)) )),
% 28.52/3.94    inference(superposition,[],[f29,f54])).
% 28.52/3.94  fof(f325,plain,(
% 28.52/3.94    ( ! [X12,X10,X11] : (k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12)))) )),
% 28.52/3.94    inference(superposition,[],[f290,f29])).
% 28.52/3.94  fof(f22172,plain,(
% 28.52/3.94    ( ! [X66,X65] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k5_xboole_0(k5_xboole_0(X65,X66),k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f22046,f121])).
% 28.52/3.94  fof(f22046,plain,(
% 28.52/3.94    ( ! [X66,X65] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)),k5_xboole_0(X65,X66)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X65,X66),k1_xboole_0),k5_xboole_0(X66,k4_xboole_0(k5_xboole_0(X65,X66),X66)))) )),
% 28.52/3.94    inference(superposition,[],[f548,f21848])).
% 28.52/3.94  fof(f21848,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f21847,f330])).
% 28.52/3.94  fof(f330,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 28.52/3.94    inference(superposition,[],[f231,f290])).
% 28.52/3.94  fof(f21847,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f21573,f4496])).
% 28.52/3.94  fof(f4496,plain,(
% 28.52/3.94    ( ! [X83,X84,X82] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X82,X83),X84),X83) = k5_xboole_0(X82,k4_xboole_0(X84,k4_xboole_0(X84,k5_xboole_0(X82,X83))))) )),
% 28.52/3.94    inference(superposition,[],[f338,f427])).
% 28.52/3.94  fof(f427,plain,(
% 28.52/3.94    ( ! [X12,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 28.52/3.94    inference(superposition,[],[f322,f89])).
% 28.52/3.94  fof(f89,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 28.52/3.94    inference(superposition,[],[f32,f37])).
% 28.52/3.94  fof(f338,plain,(
% 28.52/3.94    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f331,f29])).
% 28.52/3.94  fof(f331,plain,(
% 28.52/3.94    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6))) )),
% 28.52/3.94    inference(superposition,[],[f29,f290])).
% 28.52/3.94  fof(f21573,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))) )),
% 28.52/3.94    inference(superposition,[],[f65,f232])).
% 28.52/3.94  fof(f65,plain,(
% 28.52/3.94    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,k5_xboole_0(X2,X3)))))) )),
% 28.52/3.94    inference(superposition,[],[f36,f29])).
% 28.52/3.94  fof(f22153,plain,(
% 28.52/3.94    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22)) = k5_xboole_0(X21,k4_xboole_0(k5_xboole_0(X21,X22),X22))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f22152,f1349])).
% 28.52/3.94  fof(f1349,plain,(
% 28.52/3.94    ( ! [X24,X23,X25] : (k5_xboole_0(X25,X23) = k5_xboole_0(k5_xboole_0(X24,X23),k5_xboole_0(X25,X24))) )),
% 28.52/3.94    inference(superposition,[],[f325,f290])).
% 28.52/3.94  fof(f22152,plain,(
% 28.52/3.94    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22)) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f22028,f121])).
% 28.52/3.94  fof(f22028,plain,(
% 28.52/3.94    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k5_xboole_0(X21,X22)) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(k5_xboole_0(X21,X22),X22)),k4_xboole_0(k5_xboole_0(X21,X22),k1_xboole_0))) )),
% 28.52/3.94    inference(superposition,[],[f89,f21848])).
% 28.52/3.94  fof(f290,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2) )),
% 28.52/3.94    inference(forward_demodulation,[],[f278,f54])).
% 28.52/3.94  fof(f278,plain,(
% 28.52/3.94    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X2,X3))) )),
% 28.52/3.94    inference(superposition,[],[f231,f133])).
% 28.52/3.94  fof(f133,plain,(
% 28.52/3.94    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f84,f121])).
% 28.52/3.94  fof(f84,plain,(
% 28.52/3.94    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0)))) )),
% 28.52/3.94    inference(superposition,[],[f77,f29])).
% 28.52/3.94  fof(f1874,plain,(
% 28.52/3.94    ( ! [X24,X23,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X22,X23)))) )),
% 28.52/3.94    inference(superposition,[],[f36,f1730])).
% 28.52/3.94  fof(f1730,plain,(
% 28.52/3.94    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))) )),
% 28.52/3.94    inference(superposition,[],[f1676,f101])).
% 28.52/3.94  fof(f1676,plain,(
% 28.52/3.94    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21) )),
% 28.52/3.94    inference(forward_demodulation,[],[f1608,f121])).
% 28.52/3.94  fof(f1608,plain,(
% 28.52/3.94    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21) )),
% 28.52/3.94    inference(superposition,[],[f1460,f446])).
% 28.52/3.94  fof(f446,plain,(
% 28.52/3.94    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 28.52/3.94    inference(backward_demodulation,[],[f91,f426])).
% 28.52/3.94  fof(f426,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9) )),
% 28.52/3.94    inference(superposition,[],[f321,f89])).
% 28.52/3.94  fof(f321,plain,(
% 28.52/3.94    ( ! [X4,X3] : (k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3) )),
% 28.52/3.94    inference(superposition,[],[f290,f231])).
% 28.52/3.94  fof(f91,plain,(
% 28.52/3.94    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))))) )),
% 28.52/3.94    inference(superposition,[],[f36,f37])).
% 28.52/3.94  fof(f1460,plain,(
% 28.52/3.94    ( ! [X26,X27,X25] : (k4_xboole_0(X27,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X26,X27)))) = X27) )),
% 28.52/3.94    inference(superposition,[],[f101,f40])).
% 28.52/3.94  fof(f27355,plain,(
% 28.52/3.94    ( ! [X103,X104] : (k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X104,X103)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X104,X103),k5_xboole_0(X103,X104)),k4_xboole_0(X103,X104))) )),
% 28.52/3.94    inference(superposition,[],[f25584,f25216])).
% 28.52/3.94  fof(f25584,plain,(
% 28.52/3.94    ( ! [X12,X13] : (k4_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,X13))) )),
% 28.52/3.94    inference(superposition,[],[f25216,f330])).
% 28.52/3.94  fof(f54251,plain,(
% 28.52/3.94    ( ! [X33,X34] : (k4_xboole_0(X33,k5_xboole_0(X33,X34)) = k5_xboole_0(X33,k4_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(X34,X33)))) )),
% 28.52/3.94    inference(superposition,[],[f89,f53739])).
% 28.52/3.94  fof(f53739,plain,(
% 28.52/3.94    ( ! [X61,X60] : (k4_xboole_0(X61,X60) = k4_xboole_0(k5_xboole_0(X60,X61),X60)) )),
% 28.52/3.94    inference(forward_demodulation,[],[f53738,f124])).
% 28.52/3.94  fof(f124,plain,(
% 28.52/3.94    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)) )),
% 28.52/3.94    inference(superposition,[],[f101,f101])).
% 28.52/3.94  fof(f53738,plain,(
% 28.52/3.94    ( ! [X61,X60] : (k4_xboole_0(k4_xboole_0(X61,X60),X60) = k4_xboole_0(k5_xboole_0(X60,X61),X60)) )),
% 28.52/3.94    inference(forward_demodulation,[],[f53737,f28844])).
% 28.52/3.94  fof(f28844,plain,(
% 28.52/3.94    ( ! [X47,X48,X49] : (k4_xboole_0(k4_xboole_0(X47,X48),X49) = k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X48,X47),X49)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f28694,f121])).
% 28.52/3.94  fof(f28694,plain,(
% 28.52/3.94    ( ! [X47,X48,X49] : (k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X48,X47),X49))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X47,X48),k1_xboole_0),X49)) )),
% 28.52/3.94    inference(superposition,[],[f40,f27854])).
% 28.52/3.94  fof(f53737,plain,(
% 28.52/3.94    ( ! [X61,X60] : (k4_xboole_0(k5_xboole_0(X60,X61),X60) = k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k5_xboole_0(X60,X61),X60)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f53355,f121])).
% 28.52/3.94  fof(f53355,plain,(
% 28.52/3.94    ( ! [X61,X60] : (k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k4_xboole_0(X61,X60),k4_xboole_0(k5_xboole_0(X60,X61),X60))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X60,X61),X60),k1_xboole_0)) )),
% 28.52/3.94    inference(superposition,[],[f37,f52032])).
% 28.52/3.94  fof(f52032,plain,(
% 28.52/3.94    ( ! [X177,X176] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X176,X177),X176),k4_xboole_0(X177,X176))) )),
% 28.52/3.94    inference(superposition,[],[f51231,f28111])).
% 28.52/3.94  fof(f28111,plain,(
% 28.52/3.94    ( ! [X105,X106] : (k4_xboole_0(X106,X105) = k4_xboole_0(k5_xboole_0(X105,X106),k4_xboole_0(X105,X106))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f28108,f227])).
% 28.52/3.94  fof(f28108,plain,(
% 28.52/3.94    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,X106),k4_xboole_0(X105,X106)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X106,X105))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f27356,f27853])).
% 28.52/3.94  fof(f27853,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,X0))) )),
% 28.52/3.94    inference(superposition,[],[f1887,f25591])).
% 28.52/3.94  fof(f1887,plain,(
% 28.52/3.94    ( ! [X64,X62,X63] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X62,X63),k5_xboole_0(k4_xboole_0(X63,X64),k4_xboole_0(X62,X63)))) )),
% 28.52/3.94    inference(superposition,[],[f337,f1730])).
% 28.52/3.94  fof(f337,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,k4_xboole_0(X10,X9)))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f127,f330])).
% 28.52/3.94  fof(f127,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(k4_xboole_0(X10,X9),X9))) )),
% 28.52/3.94    inference(superposition,[],[f36,f101])).
% 28.52/3.94  fof(f27356,plain,(
% 28.52/3.94    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,X106),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),k5_xboole_0(X105,X106)),k4_xboole_0(X106,X105))) )),
% 28.52/3.94    inference(superposition,[],[f25584,f25217])).
% 28.52/3.94  fof(f25217,plain,(
% 28.52/3.94    ( ! [X85,X84] : (k4_xboole_0(X85,X84) = k5_xboole_0(k5_xboole_0(X84,X85),k4_xboole_0(X84,X85))) )),
% 28.52/3.94    inference(superposition,[],[f22175,f321])).
% 28.52/3.94  fof(f51231,plain,(
% 28.52/3.94    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X6)))) )),
% 28.52/3.94    inference(superposition,[],[f50850,f1730])).
% 28.52/3.94  fof(f50850,plain,(
% 28.52/3.94    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f50849,f231])).
% 28.52/3.94  fof(f50849,plain,(
% 28.52/3.94    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X3,X2)),X4))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f50848,f25591])).
% 28.52/3.94  fof(f50848,plain,(
% 28.52/3.94    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f50847,f1354])).
% 28.52/3.94  fof(f1354,plain,(
% 28.52/3.94    ( ! [X39,X38,X40] : (k5_xboole_0(X40,k4_xboole_0(X38,k4_xboole_0(X38,X39))) = k5_xboole_0(X38,k5_xboole_0(X40,k4_xboole_0(X38,X39)))) )),
% 28.52/3.94    inference(superposition,[],[f325,f309])).
% 28.52/3.94  fof(f309,plain,(
% 28.52/3.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 28.52/3.94    inference(superposition,[],[f231,f109])).
% 28.52/3.94  fof(f50847,plain,(
% 28.52/3.94    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f50572,f121])).
% 28.52/3.94  fof(f50572,plain,(
% 28.52/3.94    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k1_xboole_0)),X4))) )),
% 28.52/3.94    inference(superposition,[],[f42342,f19320])).
% 28.52/3.94  fof(f19320,plain,(
% 28.52/3.94    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k1_xboole_0)) )),
% 28.52/3.94    inference(forward_demodulation,[],[f19319,f50])).
% 28.52/3.94  fof(f19319,plain,(
% 28.52/3.94    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,X36))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f19318,f121])).
% 28.52/3.94  fof(f19318,plain,(
% 28.52/3.94    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k1_xboole_0)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f19317,f50])).
% 28.52/3.94  fof(f19317,plain,(
% 28.52/3.94    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,X35))))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f19316,f5052])).
% 28.52/3.94  fof(f5052,plain,(
% 28.52/3.94    ( ! [X30,X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,X30))) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,X28)))))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f1543,f5044])).
% 28.52/3.94  fof(f5044,plain,(
% 28.52/3.94    ( ! [X70,X72,X71] : (k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,X71))) = k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,k4_xboole_0(X71,X72)))))) )),
% 28.52/3.94    inference(backward_demodulation,[],[f1563,f4755])).
% 28.52/3.94  fof(f4755,plain,(
% 28.52/3.94    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) )),
% 28.52/3.94    inference(superposition,[],[f48,f40])).
% 28.52/3.94  fof(f48,plain,(
% 28.52/3.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f41,f40])).
% 28.52/3.94  fof(f41,plain,(
% 28.52/3.94    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 28.52/3.94    inference(definition_unfolding,[],[f31,f27,f27,f27,f27])).
% 28.52/3.94  fof(f31,plain,(
% 28.52/3.94    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 28.52/3.94    inference(cnf_transformation,[],[f4])).
% 28.52/3.94  fof(f4,axiom,(
% 28.52/3.94    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 28.52/3.94  fof(f1563,plain,(
% 28.52/3.94    ( ! [X70,X72,X71] : (k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,X71))) = k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,X72)))))))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f1475,f40])).
% 28.52/3.94  fof(f1475,plain,(
% 28.52/3.94    ( ! [X70,X72,X71] : (k4_xboole_0(X72,k4_xboole_0(X70,k4_xboole_0(X70,X71))) = k4_xboole_0(X72,k4_xboole_0(k4_xboole_0(X70,k4_xboole_0(X70,X71)),k4_xboole_0(X70,k4_xboole_0(X70,k4_xboole_0(X71,X72)))))) )),
% 28.52/3.94    inference(superposition,[],[f513,f40])).
% 28.52/3.94  fof(f513,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f512,f89])).
% 28.52/3.94  fof(f512,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f494,f121])).
% 28.52/3.94  fof(f494,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0))) )),
% 28.52/3.94    inference(superposition,[],[f89,f449])).
% 28.52/3.94  fof(f449,plain,(
% 28.52/3.94    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) )),
% 28.52/3.94    inference(superposition,[],[f446,f37])).
% 28.52/3.94  fof(f1543,plain,(
% 28.52/3.94    ( ! [X30,X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,k4_xboole_0(X28,k4_xboole_0(X28,X29))))))) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,X30)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f1447,f40])).
% 28.52/3.94  fof(f1447,plain,(
% 28.52/3.94    ( ! [X30,X28,X29] : (k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(X28,X29)),X30) = k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,k4_xboole_0(X28,k4_xboole_0(X28,X29)))))))) )),
% 28.52/3.94    inference(superposition,[],[f40,f513])).
% 28.52/3.94  fof(f19316,plain,(
% 28.52/3.94    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X35,X36))))))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f19315,f40])).
% 28.52/3.94  fof(f19315,plain,(
% 28.52/3.94    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36))))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f19061,f121])).
% 28.52/3.94  fof(f19061,plain,(
% 28.52/3.94    ( ! [X35,X36] : (k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0)) )),
% 28.52/3.94    inference(superposition,[],[f37,f923])).
% 28.52/3.94  fof(f923,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f922,f50])).
% 28.52/3.94  fof(f922,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k4_xboole_0(X10,X10) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f921,f121])).
% 28.52/3.94  fof(f921,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f920,f50])).
% 28.52/3.94  fof(f920,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X9)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f878,f40])).
% 28.52/3.94  fof(f878,plain,(
% 28.52/3.94    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 28.52/3.94    inference(superposition,[],[f513,f513])).
% 28.52/3.94  fof(f42342,plain,(
% 28.52/3.94    ( ! [X61,X62,X60] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X60,X62),k4_xboole_0(k5_xboole_0(X60,k4_xboole_0(X61,X60)),X62))) )),
% 28.52/3.94    inference(superposition,[],[f449,f1504])).
% 28.52/3.94  fof(f1504,plain,(
% 28.52/3.94    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)) )),
% 28.52/3.94    inference(forward_demodulation,[],[f1419,f121])).
% 28.52/3.94  fof(f1419,plain,(
% 28.52/3.94    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22)) )),
% 28.52/3.94    inference(superposition,[],[f40,f36])).
% 28.52/3.94  fof(f54348,plain,(
% 28.52/3.94    ( ! [X288,X287] : (k5_xboole_0(X287,X288) = k4_xboole_0(k5_xboole_0(X287,k4_xboole_0(X288,X287)),k4_xboole_0(X287,k5_xboole_0(X287,X288)))) )),
% 28.52/3.94    inference(superposition,[],[f31711,f53739])).
% 28.52/3.94  fof(f31711,plain,(
% 28.52/3.94    ( ! [X275,X274] : (k4_xboole_0(k5_xboole_0(X275,k4_xboole_0(X274,X275)),k4_xboole_0(X275,X274)) = X274) )),
% 28.52/3.94    inference(forward_demodulation,[],[f31710,f54])).
% 28.52/3.94  fof(f31710,plain,(
% 28.52/3.94    ( ! [X275,X274] : (k5_xboole_0(X274,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X275,k4_xboole_0(X274,X275)),k4_xboole_0(X275,X274))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f31497,f18199])).
% 28.52/3.94  fof(f18199,plain,(
% 28.52/3.94    ( ! [X103,X105,X104] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X103,X105),k5_xboole_0(X103,k4_xboole_0(X104,X103)))) )),
% 28.52/3.94    inference(superposition,[],[f18079,f621])).
% 28.52/3.94  fof(f621,plain,(
% 28.52/3.94    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9) )),
% 28.52/3.94    inference(forward_demodulation,[],[f620,f321])).
% 28.52/3.94  fof(f620,plain,(
% 28.52/3.94    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f606,f121])).
% 28.52/3.94  fof(f606,plain,(
% 28.52/3.94    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0))) )),
% 28.52/3.94    inference(superposition,[],[f89,f337])).
% 28.52/3.94  fof(f18079,plain,(
% 28.52/3.94    ( ! [X41,X42,X40] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X40,X41),X42),X40)) )),
% 28.52/3.94    inference(forward_demodulation,[],[f17964,f121])).
% 28.52/3.94  fof(f17964,plain,(
% 28.52/3.94    ( ! [X41,X42,X40] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X40,X41),X42),k1_xboole_0),X40)) )),
% 28.52/3.94    inference(superposition,[],[f17752,f446])).
% 28.52/3.94  fof(f17752,plain,(
% 28.52/3.94    ( ! [X57,X58,X56] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(X56,X57))),X56)) )),
% 28.52/3.94    inference(forward_demodulation,[],[f17607,f121])).
% 28.52/3.94  fof(f17607,plain,(
% 28.52/3.94    ( ! [X57,X58,X56] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k1_xboole_0))),X56)) )),
% 28.52/3.94    inference(superposition,[],[f5042,f446])).
% 28.52/3.94  fof(f5042,plain,(
% 28.52/3.94    ( ! [X66,X64,X65] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,k4_xboole_0(X65,X66)))),X66)) )),
% 28.52/3.94    inference(backward_demodulation,[],[f1561,f4755])).
% 28.52/3.94  fof(f1561,plain,(
% 28.52/3.94    ( ! [X66,X64,X65] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,X66)))))),X66)) )),
% 28.52/3.94    inference(forward_demodulation,[],[f1473,f40])).
% 28.52/3.94  fof(f1473,plain,(
% 28.52/3.94    ( ! [X66,X64,X65] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,X65)),k4_xboole_0(X64,k4_xboole_0(X64,k4_xboole_0(X65,X66)))),X66)) )),
% 28.52/3.94    inference(superposition,[],[f449,f40])).
% 28.52/3.94  fof(f31497,plain,(
% 28.52/3.94    ( ! [X275,X274] : (k5_xboole_0(X274,k4_xboole_0(k4_xboole_0(X275,X274),k5_xboole_0(X275,k4_xboole_0(X274,X275)))) = k4_xboole_0(k5_xboole_0(X275,k4_xboole_0(X274,X275)),k4_xboole_0(X275,X274))) )),
% 28.52/3.94    inference(superposition,[],[f22175,f25800])).
% 28.52/3.94  fof(f25800,plain,(
% 28.52/3.94    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f25580,f330])).
% 28.52/3.94  fof(f25580,plain,(
% 28.52/3.94    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),X4))) )),
% 28.52/3.94    inference(superposition,[],[f25216,f2226])).
% 28.52/3.94  fof(f2226,plain,(
% 28.52/3.94    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24))) )),
% 28.52/3.94    inference(forward_demodulation,[],[f2168,f29])).
% 28.52/3.94  fof(f2168,plain,(
% 28.52/3.94    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24)) )),
% 28.52/3.94    inference(superposition,[],[f805,f290])).
% 28.52/3.94  fof(f805,plain,(
% 28.52/3.94    ( ! [X21,X22,X20] : (k5_xboole_0(X21,X20) = k5_xboole_0(k5_xboole_0(X22,X20),k5_xboole_0(X22,X21))) )),
% 28.52/3.94    inference(superposition,[],[f236,f290])).
% 28.52/3.94  fof(f236,plain,(
% 28.52/3.94    ( ! [X10,X8,X9] : (k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) = X10) )),
% 28.52/3.94    inference(forward_demodulation,[],[f221,f227])).
% 28.52/3.94  fof(f221,plain,(
% 28.52/3.94    ( ! [X10,X8,X9] : (k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10)))) )),
% 28.52/3.94    inference(superposition,[],[f131,f29])).
% 28.52/3.94  fof(f45,plain,(
% 28.52/3.94    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 28.52/3.94    inference(avatar_component_clause,[],[f43])).
% 28.52/3.94  fof(f43,plain,(
% 28.52/3.94    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 28.52/3.94    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 28.52/3.94  fof(f46,plain,(
% 28.52/3.94    ~spl2_1),
% 28.52/3.94    inference(avatar_split_clause,[],[f33,f43])).
% 28.52/3.94  fof(f33,plain,(
% 28.52/3.94    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 28.52/3.94    inference(definition_unfolding,[],[f19,f25,f27])).
% 28.52/3.94  fof(f19,plain,(
% 28.52/3.94    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 28.52/3.94    inference(cnf_transformation,[],[f18])).
% 28.52/3.94  fof(f18,plain,(
% 28.52/3.94    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 28.52/3.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 28.52/3.94  fof(f17,plain,(
% 28.52/3.94    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 28.52/3.94    introduced(choice_axiom,[])).
% 28.52/3.94  fof(f16,plain,(
% 28.52/3.94    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 28.52/3.94    inference(ennf_transformation,[],[f14])).
% 28.52/3.94  fof(f14,negated_conjecture,(
% 28.52/3.94    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 28.52/3.94    inference(negated_conjecture,[],[f13])).
% 28.52/3.94  fof(f13,conjecture,(
% 28.52/3.94    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 28.52/3.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 28.52/3.94  % SZS output end Proof for theBenchmark
% 28.52/3.94  % (25732)------------------------------
% 28.52/3.94  % (25732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.52/3.94  % (25732)Termination reason: Refutation
% 28.52/3.94  
% 28.52/3.94  % (25732)Memory used [KB]: 83282
% 28.52/3.94  % (25732)Time elapsed: 3.458 s
% 28.52/3.94  % (25732)------------------------------
% 28.52/3.94  % (25732)------------------------------
% 28.52/3.95  % (25716)Success in time 3.595 s
%------------------------------------------------------------------------------
