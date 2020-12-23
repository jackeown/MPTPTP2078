%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t25_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:24 EDT 2019

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 136 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :   54 ( 136 expanded)
%              Number of equality atoms :   53 ( 135 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11403,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11402,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',commutativity_k3_xboole_0)).

fof(f11402,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) != k3_xboole_0(k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f11401,f10821])).

fof(f10821,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f210,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t24_xboole_1)).

fof(f210,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k2_xboole_0(X5,X7),k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f24,f20])).

fof(f11401,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) != k3_xboole_0(k2_xboole_0(sK1,k3_xboole_0(sK2,sK0)),k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f11400,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',commutativity_k2_xboole_0)).

fof(f11400,plain,(
    k3_xboole_0(k2_xboole_0(k3_xboole_0(sK2,sK0),sK1),k2_xboole_0(sK0,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f11399,f20])).

fof(f11399,plain,(
    k3_xboole_0(k2_xboole_0(k3_xboole_0(sK2,sK0),sK1),k2_xboole_0(sK0,sK2)) != k3_xboole_0(k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f11398,f188])).

fof(f188,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X2,X4)) = k2_xboole_0(X2,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f24,f21])).

fof(f11398,plain,(
    k3_xboole_0(k2_xboole_0(k3_xboole_0(sK2,sK0),sK1),k2_xboole_0(sK0,sK2)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f11397,f21])).

fof(f11397,plain,(
    k3_xboole_0(k2_xboole_0(k3_xboole_0(sK2,sK0),sK1),k2_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f11396,f8486])).

fof(f8486,plain,(
    ! [X134,X136,X135,X133] : k3_xboole_0(k2_xboole_0(k3_xboole_0(X135,X134),X136),k2_xboole_0(X133,X134)) = k2_xboole_0(k3_xboole_0(X135,X134),k3_xboole_0(X136,k2_xboole_0(X133,X134))) ),
    inference(superposition,[],[f199,f307])).

fof(f307,plain,(
    ! [X14,X15,X16] : k2_xboole_0(X15,X14) = k2_xboole_0(k2_xboole_0(X15,X14),k3_xboole_0(X16,X14)) ),
    inference(superposition,[],[f80,f246])).

fof(f246,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f223,f21])).

fof(f223,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f187,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t22_xboole_1)).

fof(f187,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',idempotence_k2_xboole_0)).

fof(f80,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k3_xboole_0(X2,k3_xboole_0(X3,X4))) = X4 ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t16_xboole_1)).

fof(f26,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f19,f20])).

fof(f199,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k2_xboole_0(X2,X4),k2_xboole_0(X3,X2)) = k2_xboole_0(X2,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f24,f21])).

fof(f11396,plain,(
    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) != k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f11395,f10821])).

fof(f11395,plain,(
    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) != k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(k2_xboole_0(sK2,sK0),sK1)) ),
    inference(forward_demodulation,[],[f11394,f11077])).

fof(f11077,plain,(
    ! [X28,X26,X27] : k2_xboole_0(X26,k3_xboole_0(X28,X27)) = k2_xboole_0(k3_xboole_0(X27,X28),X26) ),
    inference(superposition,[],[f10821,f21])).

fof(f11394,plain,(
    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) != k2_xboole_0(k3_xboole_0(k2_xboole_0(sK2,sK0),sK1),k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f11393,f7249])).

fof(f7249,plain,(
    ! [X39,X38,X40] : k3_xboole_0(k2_xboole_0(X38,X39),X40) = k3_xboole_0(X40,k2_xboole_0(X38,k3_xboole_0(X39,X40))) ),
    inference(superposition,[],[f1747,f24])).

fof(f1747,plain,(
    ! [X64,X65,X63] : k3_xboole_0(X65,X64) = k3_xboole_0(X64,k3_xboole_0(X65,k2_xboole_0(X63,X64))) ),
    inference(superposition,[],[f77,f267])).

fof(f267,plain,(
    ! [X2,X1] : k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f235,f21])).

fof(f235,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f198,f26])).

fof(f198,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f18])).

fof(f77,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f23,f20])).

fof(f11393,plain,(
    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) != k2_xboole_0(k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f11392,f21])).

fof(f11392,plain,(
    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) != k2_xboole_0(k3_xboole_0(sK1,k2_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f11221,f197])).

fof(f197,plain,(
    ! [X33,X31,X32] : k3_xboole_0(X32,k2_xboole_0(k3_xboole_0(X31,X32),X33)) = k2_xboole_0(k3_xboole_0(X31,X32),k3_xboole_0(X32,X33)) ),
    inference(superposition,[],[f24,f132])).

fof(f132,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X8,X7),X7) = X7 ),
    inference(superposition,[],[f87,f26])).

fof(f87,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f47,f21])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t4_xboole_1)).

fof(f11221,plain,(
    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) != k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f16,f10821])).

fof(f16,plain,(
    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) != k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) != k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t25_xboole_1)).
%------------------------------------------------------------------------------
