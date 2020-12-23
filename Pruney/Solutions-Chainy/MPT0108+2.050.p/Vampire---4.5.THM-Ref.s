%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:25 EST 2020

% Result     : Theorem 36.45s
% Output     : Refutation 36.45s
% Verified   : 
% Statistics : Number of formulae       :  162 (69704 expanded)
%              Number of leaves         :   13 (23118 expanded)
%              Depth                    :   42
%              Number of atoms          :  167 (75340 expanded)
%              Number of equality atoms :  166 (75339 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49646,plain,(
    $false ),
    inference(subsumption_resolution,[],[f49645,f29016])).

fof(f29016,plain,(
    ! [X10,X11] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X11,X10)) ),
    inference(forward_demodulation,[],[f28869,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f71,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_xboole_0(k1_xboole_0,X0) != X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f27,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f71,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f62,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f48,f32])).

fof(f48,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f28,f41])).

fof(f41,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f34,f21])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f28869,plain,(
    ! [X10,X11] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X10,X11))) = k4_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X11,X10)) ),
    inference(superposition,[],[f35,f28281])).

fof(f28281,plain,(
    ! [X206,X207] : k5_xboole_0(X207,X206) = k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) ),
    inference(forward_demodulation,[],[f28280,f275])).

fof(f275,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f252,f91])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f34,f78])).

fof(f252,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f149,f147])).

fof(f147,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f142,f21])).

fof(f142,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f32,f127])).

fof(f127,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f113,f78])).

fof(f113,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f35,f21])).

fof(f149,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f147])).

fof(f28280,plain,(
    ! [X206,X207] : k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X207,X206)) ),
    inference(forward_demodulation,[],[f28031,f78])).

fof(f28031,plain,(
    ! [X206,X207] : k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X206,X207)),k5_xboole_0(X207,X206)) ),
    inference(superposition,[],[f23035,f1034])).

fof(f1034,plain,(
    ! [X0,X1] : k5_xboole_0(X1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f720,f147])).

fof(f720,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24)) ),
    inference(superposition,[],[f292,f334])).

fof(f334,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f320,f91])).

fof(f320,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f277,f148])).

fof(f148,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f147,f28])).

fof(f277,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f149,f275])).

fof(f292,plain,(
    ! [X14,X12,X13] : k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14))) = X14 ),
    inference(forward_demodulation,[],[f261,f275])).

fof(f261,plain,(
    ! [X14,X12,X13] : k5_xboole_0(k1_xboole_0,X14) = k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14))) ),
    inference(superposition,[],[f149,f28])).

fof(f23035,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X6,X5)) ),
    inference(superposition,[],[f22534,f1117])).

fof(f1117,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24)) ),
    inference(forward_demodulation,[],[f1063,f28])).

fof(f1063,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24) ),
    inference(superposition,[],[f720,f334])).

fof(f22534,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f292,f22276])).

fof(f22276,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = X7 ),
    inference(forward_demodulation,[],[f22275,f2847])).

fof(f2847,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,X17)) = X17 ),
    inference(forward_demodulation,[],[f2846,f91])).

fof(f2846,plain,(
    ! [X17,X16] : k5_xboole_0(X17,k1_xboole_0) = k4_xboole_0(X17,k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f2824,f127])).

fof(f2824,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,X17)) = k5_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X17))) ),
    inference(superposition,[],[f119,f2772])).

fof(f2772,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f2728,f91])).

fof(f2728,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f39,f127])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f119,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f32,f35])).

fof(f22275,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X7)) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f22274,f2793])).

fof(f2793,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)))) = k4_xboole_0(X7,X5) ),
    inference(backward_demodulation,[],[f2774,f2741])).

fof(f2741,plain,(
    ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X10,X11)),X10) = k4_xboole_0(X12,X10) ),
    inference(superposition,[],[f39,f365])).

fof(f365,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(superposition,[],[f344,f32])).

fof(f344,plain,(
    ! [X4,X3] : k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3 ),
    inference(superposition,[],[f334,f277])).

fof(f2774,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)))) ),
    inference(forward_demodulation,[],[f2730,f889])).

fof(f889,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f361,f32])).

fof(f361,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f353,f28])).

fof(f353,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5)) ),
    inference(superposition,[],[f28,f334])).

fof(f2730,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5)))) ),
    inference(superposition,[],[f39,f35])).

fof(f22274,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))))) ),
    inference(forward_demodulation,[],[f21980,f21])).

fof(f21980,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))))) = k4_xboole_0(k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),k1_xboole_0) ),
    inference(superposition,[],[f35,f19447])).

fof(f19447,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X4))),X4) ),
    inference(superposition,[],[f2793,f127])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49645,plain,(
    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f49644,f29016])).

fof(f49644,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) != k4_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1033,f49643])).

fof(f49643,plain,(
    ! [X249,X248] : k5_xboole_0(X248,X249) = k4_xboole_0(k5_xboole_0(X249,k4_xboole_0(X248,X249)),k4_xboole_0(X249,k4_xboole_0(X249,X248))) ),
    inference(forward_demodulation,[],[f49352,f49528])).

fof(f49528,plain,(
    ! [X41,X40] : k4_xboole_0(X41,k4_xboole_0(X41,X40)) = k4_xboole_0(X41,k5_xboole_0(X40,X41)) ),
    inference(forward_demodulation,[],[f49527,f286])).

fof(f286,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f253,f275])).

fof(f253,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f149,f32])).

fof(f49527,plain,(
    ! [X41,X40] : k5_xboole_0(X41,k4_xboole_0(X41,X40)) = k4_xboole_0(X41,k5_xboole_0(X40,X41)) ),
    inference(forward_demodulation,[],[f49277,f46469])).

fof(f46469,plain,(
    ! [X111,X112] : k4_xboole_0(X112,X111) = k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) ),
    inference(forward_demodulation,[],[f46465,f91])).

fof(f46465,plain,(
    ! [X111,X112] : k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k1_xboole_0) ),
    inference(backward_demodulation,[],[f33244,f46200])).

fof(f46200,plain,(
    ! [X118,X117] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X117,X118),k5_xboole_0(X117,X118)) ),
    inference(superposition,[],[f46088,f345])).

fof(f345,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    inference(superposition,[],[f334,f334])).

fof(f46088,plain,(
    ! [X31,X32] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32) ),
    inference(forward_demodulation,[],[f45901,f78])).

fof(f45901,plain,(
    ! [X31,X32] : k4_xboole_0(k1_xboole_0,X32) = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32) ),
    inference(superposition,[],[f2791,f22837])).

fof(f22837,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(backward_demodulation,[],[f22171,f22546])).

fof(f22546,plain,(
    ! [X33,X32] : k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X33,X32)) ),
    inference(superposition,[],[f936,f22276])).

fof(f936,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12))) ),
    inference(forward_demodulation,[],[f909,f28])).

fof(f909,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12)) ),
    inference(superposition,[],[f361,f352])).

fof(f352,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f277,f334])).

fof(f22171,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(k4_xboole_0(X10,X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f22170,f15357])).

fof(f15357,plain,(
    ! [X92,X90,X91] : k5_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(X90,k4_xboole_0(X91,X92))) = k4_xboole_0(X90,k5_xboole_0(k4_xboole_0(X91,X92),k4_xboole_0(X90,X91))) ),
    inference(forward_demodulation,[],[f15277,f3163])).

fof(f3163,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X34,X35)),k4_xboole_0(X33,X34)) = k4_xboole_0(X36,k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X33,X34))) ),
    inference(superposition,[],[f39,f2785])).

fof(f2785,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,X25) = k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26)) ),
    inference(forward_demodulation,[],[f2737,f91])).

fof(f2737,plain,(
    ! [X26,X27,X25] : k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26)) = k4_xboole_0(X27,k5_xboole_0(X25,k1_xboole_0)) ),
    inference(superposition,[],[f39,f468])).

fof(f468,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f467,f147])).

fof(f467,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f447,f403])).

fof(f403,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f447,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f119,f35])).

fof(f15277,plain,(
    ! [X92,X90,X91] : k4_xboole_0(k4_xboole_0(X90,k4_xboole_0(X91,X92)),k4_xboole_0(X90,X91)) = k5_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(X90,k4_xboole_0(X91,X92))) ),
    inference(superposition,[],[f382,f2741])).

fof(f382,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f345,f32])).

fof(f22170,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X10,X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f22169,f891])).

fof(f891,plain,(
    ! [X14,X15,X16] : k5_xboole_0(X16,k4_xboole_0(X14,X15)) = k5_xboole_0(X14,k5_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15)))) ),
    inference(superposition,[],[f361,f286])).

fof(f22169,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X9))))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f22168,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f24,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f22168,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f21936,f1573])).

fof(f1573,plain,(
    ! [X64,X65,X63] : k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(X65,k5_xboole_0(X64,X63)) ),
    inference(forward_demodulation,[],[f1519,f91])).

fof(f1519,plain,(
    ! [X64,X65,X63] : k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(k5_xboole_0(X65,k1_xboole_0),k5_xboole_0(X64,X63)) ),
    inference(superposition,[],[f371,f1179])).

fof(f1179,plain,(
    ! [X26,X25] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X25,X26),k5_xboole_0(X26,X25)) ),
    inference(superposition,[],[f334,f1034])).

fof(f371,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),X11) ),
    inference(superposition,[],[f344,f28])).

fof(f21936,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(superposition,[],[f19447,f36])).

fof(f2791,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,X14) ),
    inference(backward_demodulation,[],[f2780,f2741])).

fof(f2780,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X14,X15)),X14) ),
    inference(forward_demodulation,[],[f2779,f2774])).

fof(f2779,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)))) ),
    inference(forward_demodulation,[],[f2778,f889])).

fof(f2778,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,k4_xboole_0(X15,X14)))) ),
    inference(forward_demodulation,[],[f2733,f352])).

fof(f2733,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15))) ),
    inference(superposition,[],[f39,f403])).

fof(f33244,plain,(
    ! [X111,X112] : k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k4_xboole_0(k4_xboole_0(X111,X112),k5_xboole_0(X111,X112))) ),
    inference(superposition,[],[f26144,f23035])).

fof(f26144,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15)) ),
    inference(superposition,[],[f697,f22538])).

fof(f22538,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) ),
    inference(superposition,[],[f387,f22276])).

fof(f387,plain,(
    ! [X10,X11,X9] : k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),k5_xboole_0(X9,X10)) = X11 ),
    inference(superposition,[],[f345,f28])).

fof(f697,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = X4 ),
    inference(superposition,[],[f292,f352])).

fof(f49277,plain,(
    ! [X41,X40] : k4_xboole_0(X41,k5_xboole_0(X40,X41)) = k5_xboole_0(X41,k4_xboole_0(k5_xboole_0(X40,X41),k4_xboole_0(X40,X41))) ),
    inference(superposition,[],[f119,f46594])).

fof(f46594,plain,(
    ! [X33,X34] : k4_xboole_0(X34,X33) = k4_xboole_0(k5_xboole_0(X34,X33),X33) ),
    inference(backward_demodulation,[],[f27963,f46593])).

fof(f46593,plain,(
    ! [X237,X238] : k4_xboole_0(X238,X237) = k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238) ),
    inference(forward_demodulation,[],[f46592,f403])).

fof(f46592,plain,(
    ! [X237,X238] : k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238) = k4_xboole_0(X238,k4_xboole_0(X237,k4_xboole_0(X237,X238))) ),
    inference(forward_demodulation,[],[f46591,f22836])).

fof(f22836,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(X15,X14))) ),
    inference(backward_demodulation,[],[f19635,f22546])).

fof(f19635,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15)))) ),
    inference(forward_demodulation,[],[f19634,f15357])).

fof(f19634,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X14)))) ),
    inference(forward_demodulation,[],[f19633,f891])).

fof(f19633,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X14)))))) ),
    inference(forward_demodulation,[],[f19632,f37])).

fof(f19632,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14)))) ),
    inference(forward_demodulation,[],[f19412,f1573])).

fof(f19412,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14),k4_xboole_0(X14,X15)))) ),
    inference(superposition,[],[f2793,f36])).

fof(f46591,plain,(
    ! [X237,X238] : k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238) = k4_xboole_0(X238,k4_xboole_0(X237,k5_xboole_0(X238,X237))) ),
    inference(forward_demodulation,[],[f46325,f275])).

fof(f46325,plain,(
    ! [X237,X238] : k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X238,k4_xboole_0(X237,k5_xboole_0(X238,X237)))) ),
    inference(superposition,[],[f22546,f46088])).

fof(f27963,plain,(
    ! [X33,X34] : k4_xboole_0(k5_xboole_0(X34,X33),X33) = k5_xboole_0(k4_xboole_0(X33,k5_xboole_0(X34,X33)),X34) ),
    inference(superposition,[],[f23035,f334])).

fof(f49352,plain,(
    ! [X249,X248] : k5_xboole_0(X248,X249) = k4_xboole_0(k5_xboole_0(X249,k4_xboole_0(X248,X249)),k4_xboole_0(X249,k5_xboole_0(X248,X249))) ),
    inference(superposition,[],[f28271,f46594])).

fof(f28271,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = X106 ),
    inference(forward_demodulation,[],[f28270,f91])).

fof(f28270,plain,(
    ! [X105,X106] : k5_xboole_0(X106,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) ),
    inference(forward_demodulation,[],[f28269,f468])).

fof(f28269,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(X106,k4_xboole_0(k4_xboole_0(X105,X106),X105)) ),
    inference(forward_demodulation,[],[f28268,f352])).

fof(f28268,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106) ),
    inference(forward_demodulation,[],[f28267,f3274])).

fof(f3274,plain,(
    ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(X27,X26),X28) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) ),
    inference(forward_demodulation,[],[f3273,f91])).

fof(f3273,plain,(
    ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3245,f127])).

fof(f3245,plain,(
    ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k4_xboole_0(X26,X26)) ),
    inference(superposition,[],[f119,f3120])).

fof(f3120,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X18,X17),X19)) = X17 ),
    inference(superposition,[],[f2785,f2847])).

fof(f28267,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106),X106) ),
    inference(forward_demodulation,[],[f27993,f39])).

fof(f27993,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),k5_xboole_0(X105,k4_xboole_0(X106,X105))),X106) ),
    inference(superposition,[],[f23035,f23072])).

fof(f23072,plain,(
    ! [X35,X36] : k5_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(X35,k4_xboole_0(X36,X35))) = X36 ),
    inference(superposition,[],[f345,f22534])).

fof(f1033,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f27])).

fof(f33,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f23,f24])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:58:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (6778)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6779)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (6774)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6780)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (6802)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6798)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (6801)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (6798)Refutation not found, incomplete strategy% (6798)------------------------------
% 0.21/0.54  % (6798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6798)Memory used [KB]: 1663
% 0.21/0.54  % (6798)Time elapsed: 0.125 s
% 0.21/0.54  % (6798)------------------------------
% 0.21/0.54  % (6798)------------------------------
% 0.21/0.55  % (6800)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (6773)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (6787)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (6799)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (6773)Refutation not found, incomplete strategy% (6773)------------------------------
% 0.21/0.55  % (6773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6773)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6773)Memory used [KB]: 1663
% 0.21/0.55  % (6773)Time elapsed: 0.133 s
% 0.21/0.55  % (6773)------------------------------
% 0.21/0.55  % (6773)------------------------------
% 0.21/0.55  % (6794)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (6804)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (6793)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (6792)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (6791)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (6792)Refutation not found, incomplete strategy% (6792)------------------------------
% 0.21/0.55  % (6792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6792)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6792)Memory used [KB]: 10618
% 0.21/0.55  % (6792)Time elapsed: 0.137 s
% 0.21/0.55  % (6792)------------------------------
% 0.21/0.55  % (6792)------------------------------
% 0.21/0.55  % (6777)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (6776)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (6776)Refutation not found, incomplete strategy% (6776)------------------------------
% 0.21/0.56  % (6776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6776)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6776)Memory used [KB]: 10618
% 0.21/0.56  % (6776)Time elapsed: 0.144 s
% 0.21/0.56  % (6776)------------------------------
% 0.21/0.56  % (6776)------------------------------
% 0.21/0.56  % (6790)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (6795)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (6795)Refutation not found, incomplete strategy% (6795)------------------------------
% 0.21/0.56  % (6795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6795)Memory used [KB]: 10618
% 0.21/0.56  % (6795)Time elapsed: 0.149 s
% 0.21/0.56  % (6795)------------------------------
% 0.21/0.56  % (6795)------------------------------
% 0.21/0.56  % (6803)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (6783)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (6782)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (6785)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (6788)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (6783)Refutation not found, incomplete strategy% (6783)------------------------------
% 0.21/0.56  % (6783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6783)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6783)Memory used [KB]: 10618
% 0.21/0.56  % (6783)Time elapsed: 0.145 s
% 0.21/0.56  % (6783)------------------------------
% 0.21/0.56  % (6783)------------------------------
% 0.21/0.56  % (6786)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (6784)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (6789)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (6796)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (6796)Refutation not found, incomplete strategy% (6796)------------------------------
% 0.21/0.58  % (6796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (6796)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (6796)Memory used [KB]: 1663
% 0.21/0.58  % (6796)Time elapsed: 0.157 s
% 0.21/0.58  % (6796)------------------------------
% 0.21/0.58  % (6796)------------------------------
% 1.66/0.59  % (6797)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.82/0.60  % (6797)Refutation not found, incomplete strategy% (6797)------------------------------
% 1.82/0.60  % (6797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (6797)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.60  
% 1.82/0.60  % (6797)Memory used [KB]: 10618
% 1.82/0.60  % (6797)Time elapsed: 0.128 s
% 1.82/0.60  % (6797)------------------------------
% 1.82/0.60  % (6797)------------------------------
% 2.00/0.68  % (6825)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.00/0.69  % (6826)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.00/0.69  % (6828)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.00/0.69  % (6831)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.00/0.70  % (6827)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.00/0.71  % (6829)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.00/0.72  % (6824)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.72  % (6824)Refutation not found, incomplete strategy% (6824)------------------------------
% 2.00/0.72  % (6824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.72  % (6824)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.72  
% 2.00/0.72  % (6824)Memory used [KB]: 6140
% 2.00/0.72  % (6824)Time elapsed: 0.125 s
% 2.00/0.72  % (6824)------------------------------
% 2.00/0.72  % (6824)------------------------------
% 2.72/0.75  % (6830)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.16/0.84  % (6779)Time limit reached!
% 3.16/0.84  % (6779)------------------------------
% 3.16/0.84  % (6779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.84  % (6779)Termination reason: Time limit
% 3.16/0.84  
% 3.16/0.84  % (6779)Memory used [KB]: 9338
% 3.16/0.84  % (6779)Time elapsed: 0.426 s
% 3.16/0.84  % (6779)------------------------------
% 3.16/0.84  % (6779)------------------------------
% 3.93/0.91  % (6832)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.93/0.93  % (6774)Time limit reached!
% 3.93/0.93  % (6774)------------------------------
% 3.93/0.93  % (6774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.93  % (6774)Termination reason: Time limit
% 3.93/0.93  
% 3.93/0.93  % (6774)Memory used [KB]: 9083
% 3.93/0.93  % (6774)Time elapsed: 0.514 s
% 3.93/0.93  % (6774)------------------------------
% 3.93/0.93  % (6774)------------------------------
% 4.12/0.94  % (6787)Time limit reached!
% 4.12/0.94  % (6787)------------------------------
% 4.12/0.94  % (6787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.94  % (6787)Termination reason: Time limit
% 4.12/0.94  % (6787)Termination phase: Saturation
% 4.12/0.94  
% 4.12/0.94  % (6787)Memory used [KB]: 10618
% 4.12/0.94  % (6787)Time elapsed: 0.500 s
% 4.12/0.94  % (6787)------------------------------
% 4.12/0.94  % (6787)------------------------------
% 4.12/0.95  % (6785)Time limit reached!
% 4.12/0.95  % (6785)------------------------------
% 4.12/0.95  % (6785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.95  % (6785)Termination reason: Time limit
% 4.12/0.95  
% 4.12/0.95  % (6785)Memory used [KB]: 24434
% 4.12/0.95  % (6785)Time elapsed: 0.541 s
% 4.12/0.95  % (6785)------------------------------
% 4.12/0.95  % (6785)------------------------------
% 4.12/0.97  % (6833)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.12/0.99  % (6828)Time limit reached!
% 4.12/0.99  % (6828)------------------------------
% 4.12/0.99  % (6828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.99  % (6828)Termination reason: Time limit
% 4.12/0.99  
% 4.12/0.99  % (6828)Memory used [KB]: 14072
% 4.12/0.99  % (6828)Time elapsed: 0.403 s
% 4.12/0.99  % (6828)------------------------------
% 4.12/0.99  % (6828)------------------------------
% 4.12/1.00  % (6827)Time limit reached!
% 4.12/1.00  % (6827)------------------------------
% 4.12/1.00  % (6827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/1.00  % (6827)Termination reason: Time limit
% 4.12/1.00  
% 4.12/1.00  % (6827)Memory used [KB]: 8059
% 4.12/1.00  % (6827)Time elapsed: 0.415 s
% 4.12/1.00  % (6827)------------------------------
% 4.12/1.00  % (6827)------------------------------
% 4.12/1.01  % (6803)Time limit reached!
% 4.12/1.01  % (6803)------------------------------
% 4.12/1.01  % (6803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/1.01  % (6803)Termination reason: Time limit
% 4.12/1.01  % (6803)Termination phase: Saturation
% 4.12/1.01  
% 4.12/1.01  % (6803)Memory used [KB]: 10490
% 4.12/1.01  % (6803)Time elapsed: 0.600 s
% 4.12/1.01  % (6803)------------------------------
% 4.12/1.01  % (6803)------------------------------
% 4.77/1.06  % (6835)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.77/1.07  % (6835)Refutation not found, incomplete strategy% (6835)------------------------------
% 4.77/1.07  % (6835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.07  % (6835)Termination reason: Refutation not found, incomplete strategy
% 4.77/1.07  
% 4.77/1.07  % (6835)Memory used [KB]: 1663
% 4.77/1.07  % (6835)Time elapsed: 0.093 s
% 4.77/1.07  % (6835)------------------------------
% 4.77/1.07  % (6835)------------------------------
% 4.77/1.07  % (6834)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.77/1.07  % (6834)Refutation not found, incomplete strategy% (6834)------------------------------
% 4.77/1.07  % (6834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.07  % (6834)Termination reason: Refutation not found, incomplete strategy
% 4.77/1.07  
% 4.77/1.07  % (6834)Memory used [KB]: 6140
% 4.77/1.07  % (6834)Time elapsed: 0.120 s
% 4.77/1.07  % (6834)------------------------------
% 4.77/1.07  % (6834)------------------------------
% 4.77/1.07  % (6836)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.77/1.08  % (6791)Time limit reached!
% 4.77/1.08  % (6791)------------------------------
% 4.77/1.08  % (6791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.08  % (6791)Termination reason: Time limit
% 4.77/1.08  
% 4.77/1.08  % (6791)Memory used [KB]: 16758
% 4.77/1.08  % (6791)Time elapsed: 0.667 s
% 4.77/1.08  % (6791)------------------------------
% 4.77/1.08  % (6791)------------------------------
% 4.77/1.09  % (6782)Time limit reached!
% 4.77/1.09  % (6782)------------------------------
% 4.77/1.09  % (6782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.09  % (6782)Termination reason: Time limit
% 4.77/1.09  % (6782)Termination phase: Saturation
% 4.77/1.09  
% 4.77/1.09  % (6782)Memory used [KB]: 11001
% 4.77/1.09  % (6782)Time elapsed: 0.600 s
% 4.77/1.09  % (6782)------------------------------
% 4.77/1.09  % (6782)------------------------------
% 5.21/1.11  % (6837)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.21/1.11  % (6837)Refutation not found, incomplete strategy% (6837)------------------------------
% 5.21/1.11  % (6837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.21/1.11  % (6837)Termination reason: Refutation not found, incomplete strategy
% 5.21/1.11  
% 5.21/1.11  % (6837)Memory used [KB]: 1663
% 5.21/1.11  % (6837)Time elapsed: 0.102 s
% 5.21/1.11  % (6837)------------------------------
% 5.21/1.11  % (6837)------------------------------
% 5.21/1.15  % (6839)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.21/1.15  % (6839)Refutation not found, incomplete strategy% (6839)------------------------------
% 5.21/1.15  % (6839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.21/1.15  % (6839)Termination reason: Refutation not found, incomplete strategy
% 5.21/1.15  
% 5.21/1.15  % (6839)Memory used [KB]: 6140
% 5.21/1.15  % (6839)Time elapsed: 0.120 s
% 5.21/1.15  % (6839)------------------------------
% 5.21/1.15  % (6839)------------------------------
% 5.21/1.17  % (6838)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.39/1.18  % (6840)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.39/1.20  % (6841)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.39/1.21  % (6842)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.64/1.22  % (6843)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.83/1.24  % (6844)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.50/1.32  % (6845)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.79/1.48  % (6840)Time limit reached!
% 8.79/1.48  % (6840)------------------------------
% 8.79/1.48  % (6840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.79/1.48  % (6840)Termination reason: Time limit
% 8.79/1.48  % (6840)Termination phase: Saturation
% 8.79/1.48  
% 8.79/1.48  % (6840)Memory used [KB]: 4093
% 8.79/1.48  % (6840)Time elapsed: 0.400 s
% 8.79/1.48  % (6840)------------------------------
% 8.79/1.48  % (6840)------------------------------
% 8.79/1.50  % (6836)Time limit reached!
% 8.79/1.50  % (6836)------------------------------
% 8.79/1.50  % (6836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.79/1.50  % (6836)Termination reason: Time limit
% 8.79/1.50  
% 8.79/1.50  % (6836)Memory used [KB]: 4477
% 8.79/1.50  % (6836)Time elapsed: 0.528 s
% 8.79/1.50  % (6836)------------------------------
% 8.79/1.50  % (6836)------------------------------
% 9.18/1.54  % (6843)Time limit reached!
% 9.18/1.54  % (6843)------------------------------
% 9.18/1.54  % (6843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.18/1.54  % (6843)Termination reason: Time limit
% 9.18/1.54  
% 9.18/1.54  % (6843)Memory used [KB]: 4349
% 9.18/1.54  % (6843)Time elapsed: 0.437 s
% 9.18/1.54  % (6843)------------------------------
% 9.18/1.54  % (6843)------------------------------
% 9.79/1.62  % (6848)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 9.79/1.64  % (6846)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.79/1.65  % (6847)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.41/1.75  % (6799)Time limit reached!
% 10.41/1.75  % (6799)------------------------------
% 10.41/1.75  % (6799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.41/1.75  % (6799)Termination reason: Time limit
% 10.41/1.75  
% 10.41/1.75  % (6799)Memory used [KB]: 21364
% 10.41/1.75  % (6799)Time elapsed: 1.337 s
% 10.41/1.75  % (6799)------------------------------
% 10.41/1.75  % (6799)------------------------------
% 11.41/1.82  % (6830)Time limit reached!
% 11.41/1.82  % (6830)------------------------------
% 11.41/1.82  % (6830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.41/1.82  % (6830)Termination reason: Time limit
% 11.41/1.82  
% 11.41/1.82  % (6830)Memory used [KB]: 11897
% 11.41/1.82  % (6830)Time elapsed: 1.209 s
% 11.41/1.82  % (6830)------------------------------
% 11.41/1.82  % (6830)------------------------------
% 12.10/1.91  % (6849)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 12.10/1.91  % (6849)Refutation not found, incomplete strategy% (6849)------------------------------
% 12.10/1.91  % (6849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.10/1.91  % (6849)Termination reason: Refutation not found, incomplete strategy
% 12.10/1.91  
% 12.10/1.91  % (6849)Memory used [KB]: 6140
% 12.10/1.91  % (6849)Time elapsed: 0.129 s
% 12.10/1.91  % (6849)------------------------------
% 12.10/1.91  % (6849)------------------------------
% 12.10/1.96  % (6801)Time limit reached!
% 12.10/1.96  % (6801)------------------------------
% 12.10/1.96  % (6801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.10/1.96  % (6801)Termination reason: Time limit
% 12.10/1.96  % (6801)Termination phase: Saturation
% 12.10/1.96  
% 12.10/1.96  % (6801)Memory used [KB]: 128697
% 12.10/1.96  % (6801)Time elapsed: 1.200 s
% 12.10/1.96  % (6801)------------------------------
% 12.10/1.96  % (6801)------------------------------
% 12.10/1.97  % (6802)Time limit reached!
% 12.10/1.97  % (6802)------------------------------
% 12.10/1.97  % (6802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.10/1.97  % (6802)Termination reason: Time limit
% 12.10/1.97  
% 12.10/1.97  % (6802)Memory used [KB]: 17526
% 12.10/1.97  % (6802)Time elapsed: 1.553 s
% 12.10/1.97  % (6802)------------------------------
% 12.10/1.97  % (6802)------------------------------
% 12.10/1.98  % (6850)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.72/2.02  % (6848)Time limit reached!
% 12.72/2.02  % (6848)------------------------------
% 12.72/2.02  % (6848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.72/2.02  % (6848)Termination reason: Time limit
% 12.72/2.02  % (6848)Termination phase: Saturation
% 12.72/2.02  
% 12.72/2.02  % (6848)Memory used [KB]: 14583
% 12.72/2.02  % (6848)Time elapsed: 0.400 s
% 12.72/2.02  % (6848)------------------------------
% 12.72/2.02  % (6848)------------------------------
% 12.72/2.03  % (6786)Time limit reached!
% 12.72/2.03  % (6786)------------------------------
% 12.72/2.03  % (6786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.72/2.03  % (6786)Termination reason: Time limit
% 12.72/2.03  
% 12.72/2.03  % (6786)Memory used [KB]: 28784
% 12.72/2.03  % (6786)Time elapsed: 1.620 s
% 12.72/2.03  % (6786)------------------------------
% 12.72/2.03  % (6786)------------------------------
% 12.72/2.05  % (6851)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 13.39/2.07  % (6851)Refutation not found, incomplete strategy% (6851)------------------------------
% 13.39/2.07  % (6851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.39/2.07  % (6851)Termination reason: Refutation not found, incomplete strategy
% 13.39/2.07  
% 13.39/2.07  % (6851)Memory used [KB]: 10618
% 13.39/2.07  % (6851)Time elapsed: 0.132 s
% 13.39/2.07  % (6851)------------------------------
% 13.39/2.07  % (6851)------------------------------
% 14.66/2.29  % (6778)Time limit reached!
% 14.66/2.29  % (6778)------------------------------
% 14.66/2.29  % (6778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.66/2.29  % (6778)Termination reason: Time limit
% 14.66/2.29  
% 14.66/2.29  % (6778)Memory used [KB]: 139443
% 14.66/2.29  % (6778)Time elapsed: 1.796 s
% 14.66/2.29  % (6778)------------------------------
% 14.66/2.29  % (6778)------------------------------
% 15.29/2.29  % (6790)Time limit reached!
% 15.29/2.29  % (6790)------------------------------
% 15.29/2.29  % (6790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.29/2.29  % (6790)Termination reason: Time limit
% 15.29/2.29  % (6790)Termination phase: Saturation
% 15.29/2.29  
% 15.29/2.29  % (6790)Memory used [KB]: 198418
% 15.29/2.29  % (6790)Time elapsed: 1.300 s
% 15.29/2.29  % (6790)------------------------------
% 15.29/2.29  % (6790)------------------------------
% 15.29/2.30  % (6789)Time limit reached!
% 15.29/2.30  % (6789)------------------------------
% 15.29/2.30  % (6789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.29/2.30  % (6789)Termination reason: Time limit
% 15.29/2.30  
% 15.29/2.30  % (6789)Memory used [KB]: 22643
% 15.29/2.30  % (6789)Time elapsed: 1.807 s
% 15.29/2.30  % (6789)------------------------------
% 15.29/2.30  % (6789)------------------------------
% 15.29/2.31  % (6826)Time limit reached!
% 15.29/2.31  % (6826)------------------------------
% 15.29/2.31  % (6826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.29/2.31  % (6826)Termination reason: Time limit
% 15.29/2.31  
% 15.29/2.31  % (6826)Memory used [KB]: 24306
% 15.29/2.31  % (6826)Time elapsed: 1.728 s
% 15.29/2.31  % (6826)------------------------------
% 15.29/2.31  % (6826)------------------------------
% 15.29/2.31  % (6850)Time limit reached!
% 15.29/2.31  % (6850)------------------------------
% 15.29/2.31  % (6850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.29/2.31  % (6850)Termination reason: Time limit
% 15.29/2.31  
% 15.29/2.31  % (6850)Memory used [KB]: 19445
% 15.29/2.31  % (6850)Time elapsed: 0.426 s
% 15.29/2.31  % (6850)------------------------------
% 15.29/2.31  % (6850)------------------------------
% 16.22/2.41  % (6842)Time limit reached!
% 16.22/2.41  % (6842)------------------------------
% 16.22/2.41  % (6842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.22/2.41  % (6842)Termination reason: Time limit
% 16.22/2.41  % (6842)Termination phase: Saturation
% 16.22/2.41  
% 16.22/2.41  % (6842)Memory used [KB]: 17654
% 16.22/2.41  % (6842)Time elapsed: 1.300 s
% 16.22/2.41  % (6842)------------------------------
% 16.22/2.41  % (6842)------------------------------
% 16.29/2.42  % (6780)Time limit reached!
% 16.29/2.42  % (6780)------------------------------
% 16.29/2.42  % (6780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.43  % (6780)Termination reason: Time limit
% 16.29/2.43  
% 16.29/2.43  % (6780)Memory used [KB]: 27760
% 16.29/2.43  % (6780)Time elapsed: 2.002 s
% 16.29/2.43  % (6780)------------------------------
% 16.29/2.43  % (6780)------------------------------
% 16.29/2.46  % (6793)Time limit reached!
% 16.29/2.46  % (6793)------------------------------
% 16.29/2.46  % (6793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.46  % (6793)Termination reason: Time limit
% 16.29/2.46  % (6793)Termination phase: Saturation
% 16.29/2.46  
% 16.29/2.46  % (6793)Memory used [KB]: 36076
% 16.29/2.46  % (6793)Time elapsed: 2.0000 s
% 16.29/2.46  % (6793)------------------------------
% 16.29/2.46  % (6793)------------------------------
% 17.79/2.66  % (6832)Time limit reached!
% 17.79/2.66  % (6832)------------------------------
% 17.79/2.66  % (6832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.66  % (6832)Termination reason: Time limit
% 17.79/2.66  
% 17.79/2.66  % (6832)Memory used [KB]: 73047
% 17.79/2.66  % (6832)Time elapsed: 1.855 s
% 17.79/2.66  % (6832)------------------------------
% 17.79/2.66  % (6832)------------------------------
% 21.63/3.08  % (6794)Time limit reached!
% 21.63/3.08  % (6794)------------------------------
% 21.63/3.08  % (6794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.63/3.08  % (6794)Termination reason: Time limit
% 21.63/3.08  % (6794)Termination phase: Saturation
% 21.63/3.08  
% 21.63/3.08  % (6794)Memory used [KB]: 74071
% 21.63/3.08  % (6794)Time elapsed: 2.600 s
% 21.63/3.08  % (6794)------------------------------
% 21.63/3.08  % (6794)------------------------------
% 24.40/3.43  % (6825)Time limit reached!
% 24.40/3.43  % (6825)------------------------------
% 24.40/3.43  % (6825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.40/3.44  % (6825)Termination reason: Time limit
% 24.40/3.44  % (6825)Termination phase: Saturation
% 24.40/3.44  
% 24.40/3.44  % (6825)Memory used [KB]: 44647
% 24.40/3.44  % (6825)Time elapsed: 2.800 s
% 24.40/3.44  % (6825)------------------------------
% 24.40/3.44  % (6825)------------------------------
% 24.40/3.45  % (6788)Time limit reached!
% 24.40/3.45  % (6788)------------------------------
% 24.40/3.45  % (6788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.40/3.45  % (6788)Termination reason: Time limit
% 24.40/3.45  
% 24.40/3.45  % (6788)Memory used [KB]: 16502
% 24.40/3.45  % (6788)Time elapsed: 3.026 s
% 24.40/3.45  % (6788)------------------------------
% 24.40/3.45  % (6788)------------------------------
% 31.67/4.34  % (6804)Time limit reached!
% 31.67/4.34  % (6804)------------------------------
% 31.67/4.34  % (6804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.67/4.35  % (6804)Termination reason: Time limit
% 31.67/4.35  % (6804)Termination phase: Saturation
% 31.67/4.35  
% 31.67/4.35  % (6804)Memory used [KB]: 77525
% 31.67/4.35  % (6804)Time elapsed: 3.900 s
% 31.67/4.35  % (6804)------------------------------
% 31.67/4.35  % (6804)------------------------------
% 32.94/4.54  % (6838)Time limit reached!
% 32.94/4.54  % (6838)------------------------------
% 32.94/4.54  % (6838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 32.94/4.54  % (6838)Termination reason: Time limit
% 32.94/4.54  % (6838)Termination phase: Saturation
% 32.94/4.54  
% 32.94/4.54  % (6838)Memory used [KB]: 80595
% 32.94/4.54  % (6838)Time elapsed: 3.500 s
% 32.94/4.54  % (6838)------------------------------
% 32.94/4.54  % (6838)------------------------------
% 36.45/4.97  % (6831)Refutation found. Thanks to Tanya!
% 36.45/4.97  % SZS status Theorem for theBenchmark
% 36.45/4.97  % SZS output start Proof for theBenchmark
% 36.45/4.97  fof(f49646,plain,(
% 36.45/4.97    $false),
% 36.45/4.97    inference(subsumption_resolution,[],[f49645,f29016])).
% 36.45/4.97  fof(f29016,plain,(
% 36.45/4.97    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X11,X10))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f28869,f78])).
% 36.45/4.97  fof(f78,plain,(
% 36.45/4.97    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 36.45/4.97    inference(unit_resulting_resolution,[],[f71,f42])).
% 36.45/4.97  fof(f42,plain,(
% 36.45/4.97    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) != X0 | k1_xboole_0 = X0) )),
% 36.45/4.97    inference(superposition,[],[f27,f21])).
% 36.45/4.97  fof(f21,plain,(
% 36.45/4.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 36.45/4.97    inference(cnf_transformation,[],[f6])).
% 36.45/4.97  fof(f6,axiom,(
% 36.45/4.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 36.45/4.97  fof(f27,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 36.45/4.97    inference(cnf_transformation,[],[f16])).
% 36.45/4.97  fof(f16,plain,(
% 36.45/4.97    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 36.45/4.97    inference(ennf_transformation,[],[f5])).
% 36.45/4.97  fof(f5,axiom,(
% 36.45/4.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 36.45/4.97  fof(f71,plain,(
% 36.45/4.97    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 36.45/4.97    inference(superposition,[],[f62,f32])).
% 36.45/4.97  fof(f32,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 36.45/4.97    inference(definition_unfolding,[],[f25,f24])).
% 36.45/4.97  fof(f24,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 36.45/4.97    inference(cnf_transformation,[],[f9])).
% 36.45/4.97  fof(f9,axiom,(
% 36.45/4.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 36.45/4.97  fof(f25,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 36.45/4.97    inference(cnf_transformation,[],[f2])).
% 36.45/4.97  fof(f2,axiom,(
% 36.45/4.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 36.45/4.97  fof(f62,plain,(
% 36.45/4.97    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 36.45/4.97    inference(superposition,[],[f48,f32])).
% 36.45/4.97  fof(f48,plain,(
% 36.45/4.97    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) )),
% 36.45/4.97    inference(superposition,[],[f28,f41])).
% 36.45/4.97  fof(f41,plain,(
% 36.45/4.97    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 36.45/4.97    inference(superposition,[],[f34,f21])).
% 36.45/4.97  fof(f34,plain,(
% 36.45/4.97    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 36.45/4.97    inference(definition_unfolding,[],[f20,f23])).
% 36.45/4.97  fof(f23,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 36.45/4.97    inference(cnf_transformation,[],[f12])).
% 36.45/4.97  fof(f12,axiom,(
% 36.45/4.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 36.45/4.97  fof(f20,plain,(
% 36.45/4.97    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 36.45/4.97    inference(cnf_transformation,[],[f4])).
% 36.45/4.97  fof(f4,axiom,(
% 36.45/4.97    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 36.45/4.97  fof(f28,plain,(
% 36.45/4.97    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 36.45/4.97    inference(cnf_transformation,[],[f11])).
% 36.45/4.97  fof(f11,axiom,(
% 36.45/4.97    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 36.45/4.97  fof(f28869,plain,(
% 36.45/4.97    ( ! [X10,X11] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X10,X11))) = k4_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X11,X10))) )),
% 36.45/4.97    inference(superposition,[],[f35,f28281])).
% 36.45/4.97  fof(f28281,plain,(
% 36.45/4.97    ( ! [X206,X207] : (k5_xboole_0(X207,X206) = k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f28280,f275])).
% 36.45/4.97  fof(f275,plain,(
% 36.45/4.97    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 36.45/4.97    inference(forward_demodulation,[],[f252,f91])).
% 36.45/4.97  fof(f91,plain,(
% 36.45/4.97    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 36.45/4.97    inference(backward_demodulation,[],[f34,f78])).
% 36.45/4.97  fof(f252,plain,(
% 36.45/4.97    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 36.45/4.97    inference(superposition,[],[f149,f147])).
% 36.45/4.97  fof(f147,plain,(
% 36.45/4.97    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f142,f21])).
% 36.45/4.97  fof(f142,plain,(
% 36.45/4.97    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 36.45/4.97    inference(superposition,[],[f32,f127])).
% 36.45/4.97  fof(f127,plain,(
% 36.45/4.97    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f113,f78])).
% 36.45/4.97  fof(f113,plain,(
% 36.45/4.97    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 36.45/4.97    inference(superposition,[],[f35,f21])).
% 36.45/4.97  fof(f149,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 36.45/4.97    inference(superposition,[],[f28,f147])).
% 36.45/4.97  fof(f28280,plain,(
% 36.45/4.97    ( ! [X206,X207] : (k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X207,X206))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f28031,f78])).
% 36.45/4.97  fof(f28031,plain,(
% 36.45/4.97    ( ! [X206,X207] : (k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X206,X207)),k5_xboole_0(X207,X206))) )),
% 36.45/4.97    inference(superposition,[],[f23035,f1034])).
% 36.45/4.97  fof(f1034,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) )),
% 36.45/4.97    inference(superposition,[],[f720,f147])).
% 36.45/4.97  fof(f720,plain,(
% 36.45/4.97    ( ! [X24,X23,X25] : (k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24))) )),
% 36.45/4.97    inference(superposition,[],[f292,f334])).
% 36.45/4.97  fof(f334,plain,(
% 36.45/4.97    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3) )),
% 36.45/4.97    inference(forward_demodulation,[],[f320,f91])).
% 36.45/4.97  fof(f320,plain,(
% 36.45/4.97    ( ! [X4,X3] : (k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4))) )),
% 36.45/4.97    inference(superposition,[],[f277,f148])).
% 36.45/4.97  fof(f148,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 36.45/4.97    inference(superposition,[],[f147,f28])).
% 36.45/4.97  fof(f277,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 36.45/4.97    inference(backward_demodulation,[],[f149,f275])).
% 36.45/4.97  fof(f292,plain,(
% 36.45/4.97    ( ! [X14,X12,X13] : (k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14))) = X14) )),
% 36.45/4.97    inference(forward_demodulation,[],[f261,f275])).
% 36.45/4.97  fof(f261,plain,(
% 36.45/4.97    ( ! [X14,X12,X13] : (k5_xboole_0(k1_xboole_0,X14) = k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14)))) )),
% 36.45/4.97    inference(superposition,[],[f149,f28])).
% 36.45/4.97  fof(f23035,plain,(
% 36.45/4.97    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X6,X5))) )),
% 36.45/4.97    inference(superposition,[],[f22534,f1117])).
% 36.45/4.97  fof(f1117,plain,(
% 36.45/4.97    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f1063,f28])).
% 36.45/4.97  fof(f1063,plain,(
% 36.45/4.97    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24)) )),
% 36.45/4.97    inference(superposition,[],[f720,f334])).
% 36.45/4.97  fof(f22534,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 36.45/4.97    inference(superposition,[],[f292,f22276])).
% 36.45/4.97  fof(f22276,plain,(
% 36.45/4.97    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = X7) )),
% 36.45/4.97    inference(forward_demodulation,[],[f22275,f2847])).
% 36.45/4.97  fof(f2847,plain,(
% 36.45/4.97    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,X17)) = X17) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2846,f91])).
% 36.45/4.97  fof(f2846,plain,(
% 36.45/4.97    ( ! [X17,X16] : (k5_xboole_0(X17,k1_xboole_0) = k4_xboole_0(X17,k4_xboole_0(X16,X17))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2824,f127])).
% 36.45/4.97  fof(f2824,plain,(
% 36.45/4.97    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,X17)) = k5_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X17)))) )),
% 36.45/4.97    inference(superposition,[],[f119,f2772])).
% 36.45/4.97  fof(f2772,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2728,f91])).
% 36.45/4.97  fof(f2728,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) )),
% 36.45/4.97    inference(superposition,[],[f39,f127])).
% 36.45/4.97  fof(f39,plain,(
% 36.45/4.97    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 36.45/4.97    inference(definition_unfolding,[],[f31,f23])).
% 36.45/4.97  fof(f31,plain,(
% 36.45/4.97    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 36.45/4.97    inference(cnf_transformation,[],[f7])).
% 36.45/4.97  fof(f7,axiom,(
% 36.45/4.97    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 36.45/4.97  fof(f119,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 36.45/4.97    inference(superposition,[],[f32,f35])).
% 36.45/4.97  fof(f22275,plain,(
% 36.45/4.97    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X7)) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f22274,f2793])).
% 36.45/4.97  fof(f2793,plain,(
% 36.45/4.97    ( ! [X6,X7,X5] : (k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)))) = k4_xboole_0(X7,X5)) )),
% 36.45/4.97    inference(backward_demodulation,[],[f2774,f2741])).
% 36.45/4.97  fof(f2741,plain,(
% 36.45/4.97    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X10,X11)),X10) = k4_xboole_0(X12,X10)) )),
% 36.45/4.97    inference(superposition,[],[f39,f365])).
% 36.45/4.97  fof(f365,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1) )),
% 36.45/4.97    inference(superposition,[],[f344,f32])).
% 36.45/4.97  fof(f344,plain,(
% 36.45/4.97    ( ! [X4,X3] : (k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3) )),
% 36.45/4.97    inference(superposition,[],[f334,f277])).
% 36.45/4.97  fof(f2774,plain,(
% 36.45/4.97    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2730,f889])).
% 36.45/4.97  fof(f889,plain,(
% 36.45/4.97    ( ! [X10,X8,X9] : (k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9)))) )),
% 36.45/4.97    inference(superposition,[],[f361,f32])).
% 36.45/4.97  fof(f361,plain,(
% 36.45/4.97    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f353,f28])).
% 36.45/4.97  fof(f353,plain,(
% 36.45/4.97    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) )),
% 36.45/4.97    inference(superposition,[],[f28,f334])).
% 36.45/4.97  fof(f2730,plain,(
% 36.45/4.97    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))))) )),
% 36.45/4.97    inference(superposition,[],[f39,f35])).
% 36.45/4.97  fof(f22274,plain,(
% 36.45/4.97    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7)))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f21980,f21])).
% 36.45/4.97  fof(f21980,plain,(
% 36.45/4.97    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))))) = k4_xboole_0(k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),k1_xboole_0)) )),
% 36.45/4.97    inference(superposition,[],[f35,f19447])).
% 36.45/4.97  fof(f19447,plain,(
% 36.45/4.97    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X4))),X4)) )),
% 36.45/4.97    inference(superposition,[],[f2793,f127])).
% 36.45/4.97  fof(f35,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 36.45/4.97    inference(definition_unfolding,[],[f22,f24,f24])).
% 36.45/4.97  fof(f22,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 36.45/4.97    inference(cnf_transformation,[],[f1])).
% 36.45/4.97  fof(f1,axiom,(
% 36.45/4.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 36.45/4.97  fof(f49645,plain,(
% 36.45/4.97    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0))),
% 36.45/4.97    inference(forward_demodulation,[],[f49644,f29016])).
% 36.45/4.97  fof(f49644,plain,(
% 36.45/4.97    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) != k4_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))),
% 36.45/4.97    inference(backward_demodulation,[],[f1033,f49643])).
% 36.45/4.97  fof(f49643,plain,(
% 36.45/4.97    ( ! [X249,X248] : (k5_xboole_0(X248,X249) = k4_xboole_0(k5_xboole_0(X249,k4_xboole_0(X248,X249)),k4_xboole_0(X249,k4_xboole_0(X249,X248)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f49352,f49528])).
% 36.45/4.97  fof(f49528,plain,(
% 36.45/4.97    ( ! [X41,X40] : (k4_xboole_0(X41,k4_xboole_0(X41,X40)) = k4_xboole_0(X41,k5_xboole_0(X40,X41))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f49527,f286])).
% 36.45/4.97  fof(f286,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f253,f275])).
% 36.45/4.97  fof(f253,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 36.45/4.97    inference(superposition,[],[f149,f32])).
% 36.45/4.97  fof(f49527,plain,(
% 36.45/4.97    ( ! [X41,X40] : (k5_xboole_0(X41,k4_xboole_0(X41,X40)) = k4_xboole_0(X41,k5_xboole_0(X40,X41))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f49277,f46469])).
% 36.45/4.97  fof(f46469,plain,(
% 36.45/4.97    ( ! [X111,X112] : (k4_xboole_0(X112,X111) = k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f46465,f91])).
% 36.45/4.97  fof(f46465,plain,(
% 36.45/4.97    ( ! [X111,X112] : (k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k1_xboole_0)) )),
% 36.45/4.97    inference(backward_demodulation,[],[f33244,f46200])).
% 36.45/4.97  fof(f46200,plain,(
% 36.45/4.97    ( ! [X118,X117] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X117,X118),k5_xboole_0(X117,X118))) )),
% 36.45/4.97    inference(superposition,[],[f46088,f345])).
% 36.45/4.97  fof(f345,plain,(
% 36.45/4.97    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) )),
% 36.45/4.97    inference(superposition,[],[f334,f334])).
% 36.45/4.97  fof(f46088,plain,(
% 36.45/4.97    ( ! [X31,X32] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f45901,f78])).
% 36.45/4.97  fof(f45901,plain,(
% 36.45/4.97    ( ! [X31,X32] : (k4_xboole_0(k1_xboole_0,X32) = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32)) )),
% 36.45/4.97    inference(superposition,[],[f2791,f22837])).
% 36.45/4.97  fof(f22837,plain,(
% 36.45/4.97    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 36.45/4.97    inference(backward_demodulation,[],[f22171,f22546])).
% 36.45/4.97  fof(f22546,plain,(
% 36.45/4.97    ( ! [X33,X32] : (k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X33,X32))) )),
% 36.45/4.97    inference(superposition,[],[f936,f22276])).
% 36.45/4.97  fof(f936,plain,(
% 36.45/4.97    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f909,f28])).
% 36.45/4.97  fof(f909,plain,(
% 36.45/4.97    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12))) )),
% 36.45/4.97    inference(superposition,[],[f361,f352])).
% 36.45/4.97  fof(f352,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 36.45/4.97    inference(superposition,[],[f277,f334])).
% 36.45/4.97  fof(f22171,plain,(
% 36.45/4.97    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(k4_xboole_0(X10,X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f22170,f15357])).
% 36.45/4.97  fof(f15357,plain,(
% 36.45/4.97    ( ! [X92,X90,X91] : (k5_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(X90,k4_xboole_0(X91,X92))) = k4_xboole_0(X90,k5_xboole_0(k4_xboole_0(X91,X92),k4_xboole_0(X90,X91)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f15277,f3163])).
% 36.45/4.97  fof(f3163,plain,(
% 36.45/4.97    ( ! [X35,X33,X36,X34] : (k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X34,X35)),k4_xboole_0(X33,X34)) = k4_xboole_0(X36,k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X33,X34)))) )),
% 36.45/4.97    inference(superposition,[],[f39,f2785])).
% 36.45/4.97  fof(f2785,plain,(
% 36.45/4.97    ( ! [X26,X27,X25] : (k4_xboole_0(X27,X25) = k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2737,f91])).
% 36.45/4.97  fof(f2737,plain,(
% 36.45/4.97    ( ! [X26,X27,X25] : (k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26)) = k4_xboole_0(X27,k5_xboole_0(X25,k1_xboole_0))) )),
% 36.45/4.97    inference(superposition,[],[f39,f468])).
% 36.45/4.97  fof(f468,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f467,f147])).
% 36.45/4.97  fof(f467,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f447,f403])).
% 36.45/4.97  fof(f403,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 36.45/4.97    inference(superposition,[],[f36,f35])).
% 36.45/4.97  fof(f36,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 36.45/4.97    inference(definition_unfolding,[],[f26,f24])).
% 36.45/4.97  fof(f26,plain,(
% 36.45/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 36.45/4.97    inference(cnf_transformation,[],[f8])).
% 36.45/4.97  fof(f8,axiom,(
% 36.45/4.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 36.45/4.97  fof(f447,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) )),
% 36.45/4.97    inference(superposition,[],[f119,f35])).
% 36.45/4.97  fof(f15277,plain,(
% 36.45/4.97    ( ! [X92,X90,X91] : (k4_xboole_0(k4_xboole_0(X90,k4_xboole_0(X91,X92)),k4_xboole_0(X90,X91)) = k5_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(X90,k4_xboole_0(X91,X92)))) )),
% 36.45/4.97    inference(superposition,[],[f382,f2741])).
% 36.45/4.97  fof(f382,plain,(
% 36.45/4.97    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 36.45/4.97    inference(superposition,[],[f345,f32])).
% 36.45/4.97  fof(f22170,plain,(
% 36.45/4.97    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X10,X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f22169,f891])).
% 36.45/4.97  fof(f891,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k5_xboole_0(X16,k4_xboole_0(X14,X15)) = k5_xboole_0(X14,k5_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))))) )),
% 36.45/4.97    inference(superposition,[],[f361,f286])).
% 36.45/4.97  fof(f22169,plain,(
% 36.45/4.97    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X9))))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f22168,f37])).
% 36.45/4.97  fof(f37,plain,(
% 36.45/4.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 36.45/4.97    inference(definition_unfolding,[],[f29,f24,f24])).
% 36.45/4.97  fof(f29,plain,(
% 36.45/4.97    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 36.45/4.97    inference(cnf_transformation,[],[f10])).
% 36.45/4.97  fof(f10,axiom,(
% 36.45/4.97    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 36.45/4.97  fof(f22168,plain,(
% 36.45/4.97    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f21936,f1573])).
% 36.45/4.97  fof(f1573,plain,(
% 36.45/4.97    ( ! [X64,X65,X63] : (k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(X65,k5_xboole_0(X64,X63))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f1519,f91])).
% 36.45/4.97  fof(f1519,plain,(
% 36.45/4.97    ( ! [X64,X65,X63] : (k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(k5_xboole_0(X65,k1_xboole_0),k5_xboole_0(X64,X63))) )),
% 36.45/4.97    inference(superposition,[],[f371,f1179])).
% 36.45/4.97  fof(f1179,plain,(
% 36.45/4.97    ( ! [X26,X25] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X25,X26),k5_xboole_0(X26,X25))) )),
% 36.45/4.97    inference(superposition,[],[f334,f1034])).
% 36.45/4.97  fof(f371,plain,(
% 36.45/4.97    ( ! [X10,X11,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),X11)) )),
% 36.45/4.97    inference(superposition,[],[f344,f28])).
% 36.45/4.97  fof(f21936,plain,(
% 36.45/4.97    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 36.45/4.97    inference(superposition,[],[f19447,f36])).
% 36.45/4.97  fof(f2791,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,X14)) )),
% 36.45/4.97    inference(backward_demodulation,[],[f2780,f2741])).
% 36.45/4.97  fof(f2780,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X14,X15)),X14)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2779,f2774])).
% 36.45/4.97  fof(f2779,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2778,f889])).
% 36.45/4.97  fof(f2778,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,k4_xboole_0(X15,X14))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f2733,f352])).
% 36.45/4.97  fof(f2733,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)))) )),
% 36.45/4.97    inference(superposition,[],[f39,f403])).
% 36.45/4.97  fof(f33244,plain,(
% 36.45/4.97    ( ! [X111,X112] : (k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k4_xboole_0(k4_xboole_0(X111,X112),k5_xboole_0(X111,X112)))) )),
% 36.45/4.97    inference(superposition,[],[f26144,f23035])).
% 36.45/4.97  fof(f26144,plain,(
% 36.45/4.97    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15))) )),
% 36.45/4.97    inference(superposition,[],[f697,f22538])).
% 36.45/4.97  fof(f22538,plain,(
% 36.45/4.97    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8)))) )),
% 36.45/4.97    inference(superposition,[],[f387,f22276])).
% 36.45/4.97  fof(f387,plain,(
% 36.45/4.97    ( ! [X10,X11,X9] : (k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),k5_xboole_0(X9,X10)) = X11) )),
% 36.45/4.97    inference(superposition,[],[f345,f28])).
% 36.45/4.97  fof(f697,plain,(
% 36.45/4.97    ( ! [X4,X2,X3] : (k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = X4) )),
% 36.45/4.97    inference(superposition,[],[f292,f352])).
% 36.45/4.97  fof(f49277,plain,(
% 36.45/4.97    ( ! [X41,X40] : (k4_xboole_0(X41,k5_xboole_0(X40,X41)) = k5_xboole_0(X41,k4_xboole_0(k5_xboole_0(X40,X41),k4_xboole_0(X40,X41)))) )),
% 36.45/4.97    inference(superposition,[],[f119,f46594])).
% 36.45/4.97  fof(f46594,plain,(
% 36.45/4.97    ( ! [X33,X34] : (k4_xboole_0(X34,X33) = k4_xboole_0(k5_xboole_0(X34,X33),X33)) )),
% 36.45/4.97    inference(backward_demodulation,[],[f27963,f46593])).
% 36.45/4.97  fof(f46593,plain,(
% 36.45/4.97    ( ! [X237,X238] : (k4_xboole_0(X238,X237) = k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f46592,f403])).
% 36.45/4.97  fof(f46592,plain,(
% 36.45/4.97    ( ! [X237,X238] : (k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238) = k4_xboole_0(X238,k4_xboole_0(X237,k4_xboole_0(X237,X238)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f46591,f22836])).
% 36.45/4.97  fof(f22836,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(X15,X14)))) )),
% 36.45/4.97    inference(backward_demodulation,[],[f19635,f22546])).
% 36.45/4.97  fof(f19635,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f19634,f15357])).
% 36.45/4.97  fof(f19634,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X14))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f19633,f891])).
% 36.45/4.97  fof(f19633,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X14))))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f19632,f37])).
% 36.45/4.97  fof(f19632,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14))))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f19412,f1573])).
% 36.45/4.97  fof(f19412,plain,(
% 36.45/4.97    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14),k4_xboole_0(X14,X15))))) )),
% 36.45/4.97    inference(superposition,[],[f2793,f36])).
% 36.45/4.97  fof(f46591,plain,(
% 36.45/4.97    ( ! [X237,X238] : (k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238) = k4_xboole_0(X238,k4_xboole_0(X237,k5_xboole_0(X238,X237)))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f46325,f275])).
% 36.45/4.97  fof(f46325,plain,(
% 36.45/4.97    ( ! [X237,X238] : (k5_xboole_0(k4_xboole_0(X237,k5_xboole_0(X238,X237)),X238) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X238,k4_xboole_0(X237,k5_xboole_0(X238,X237))))) )),
% 36.45/4.97    inference(superposition,[],[f22546,f46088])).
% 36.45/4.97  fof(f27963,plain,(
% 36.45/4.97    ( ! [X33,X34] : (k4_xboole_0(k5_xboole_0(X34,X33),X33) = k5_xboole_0(k4_xboole_0(X33,k5_xboole_0(X34,X33)),X34)) )),
% 36.45/4.97    inference(superposition,[],[f23035,f334])).
% 36.45/4.97  fof(f49352,plain,(
% 36.45/4.97    ( ! [X249,X248] : (k5_xboole_0(X248,X249) = k4_xboole_0(k5_xboole_0(X249,k4_xboole_0(X248,X249)),k4_xboole_0(X249,k5_xboole_0(X248,X249)))) )),
% 36.45/4.97    inference(superposition,[],[f28271,f46594])).
% 36.45/4.97  fof(f28271,plain,(
% 36.45/4.97    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = X106) )),
% 36.45/4.97    inference(forward_demodulation,[],[f28270,f91])).
% 36.45/4.97  fof(f28270,plain,(
% 36.45/4.97    ( ! [X105,X106] : (k5_xboole_0(X106,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f28269,f468])).
% 36.45/4.97  fof(f28269,plain,(
% 36.45/4.97    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(X106,k4_xboole_0(k4_xboole_0(X105,X106),X105))) )),
% 36.45/4.97    inference(forward_demodulation,[],[f28268,f352])).
% 36.45/4.97  fof(f28268,plain,(
% 36.45/4.97    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f28267,f3274])).
% 36.45/4.97  fof(f3274,plain,(
% 36.45/4.97    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(X27,X26),X28) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f3273,f91])).
% 36.45/4.97  fof(f3273,plain,(
% 36.45/4.97    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k1_xboole_0)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f3245,f127])).
% 36.45/4.97  fof(f3245,plain,(
% 36.45/4.97    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k4_xboole_0(X26,X26))) )),
% 36.45/4.97    inference(superposition,[],[f119,f3120])).
% 36.45/4.97  fof(f3120,plain,(
% 36.45/4.97    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X18,X17),X19)) = X17) )),
% 36.45/4.97    inference(superposition,[],[f2785,f2847])).
% 36.45/4.97  fof(f28267,plain,(
% 36.45/4.97    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106),X106)) )),
% 36.45/4.97    inference(forward_demodulation,[],[f27993,f39])).
% 36.45/4.97  fof(f27993,plain,(
% 36.45/4.97    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),k5_xboole_0(X105,k4_xboole_0(X106,X105))),X106)) )),
% 36.45/4.97    inference(superposition,[],[f23035,f23072])).
% 36.45/4.97  fof(f23072,plain,(
% 36.45/4.97    ( ! [X35,X36] : (k5_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(X35,k4_xboole_0(X36,X35))) = X36) )),
% 36.45/4.97    inference(superposition,[],[f345,f22534])).
% 36.45/4.97  fof(f1033,plain,(
% 36.45/4.97    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))),
% 36.45/4.97    inference(unit_resulting_resolution,[],[f33,f27])).
% 36.45/4.97  fof(f33,plain,(
% 36.45/4.97    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 36.45/4.97    inference(definition_unfolding,[],[f19,f23,f24])).
% 36.45/4.97  fof(f19,plain,(
% 36.45/4.97    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 36.45/4.97    inference(cnf_transformation,[],[f18])).
% 36.45/4.97  fof(f18,plain,(
% 36.45/4.97    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 36.45/4.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 36.45/4.97  fof(f17,plain,(
% 36.45/4.97    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 36.45/4.97    introduced(choice_axiom,[])).
% 36.45/4.97  fof(f15,plain,(
% 36.45/4.97    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 36.45/4.97    inference(ennf_transformation,[],[f14])).
% 36.45/4.97  fof(f14,negated_conjecture,(
% 36.45/4.97    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 36.45/4.97    inference(negated_conjecture,[],[f13])).
% 36.45/4.97  fof(f13,conjecture,(
% 36.45/4.97    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 36.45/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 36.45/4.97  % SZS output end Proof for theBenchmark
% 36.45/4.97  % (6831)------------------------------
% 36.45/4.97  % (6831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.45/4.97  % (6831)Termination reason: Refutation
% 36.45/4.97  
% 36.45/4.97  % (6831)Memory used [KB]: 80979
% 36.45/4.97  % (6831)Time elapsed: 4.278 s
% 36.45/4.97  % (6831)------------------------------
% 36.45/4.97  % (6831)------------------------------
% 36.45/4.97  % (6771)Success in time 4.602 s
%------------------------------------------------------------------------------
