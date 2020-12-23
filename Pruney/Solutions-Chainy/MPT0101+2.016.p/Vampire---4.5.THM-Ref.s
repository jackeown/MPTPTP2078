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
% DateTime   : Thu Dec  3 12:31:54 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 214 expanded)
%              Number of leaves         :   19 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          :   96 ( 226 expanded)
%              Number of equality atoms :   82 ( 207 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1477,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1476])).

fof(f1476,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1475,f455])).

fof(f455,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X13,X15) = k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15)) ),
    inference(superposition,[],[f44,f413])).

fof(f413,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f50,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1475,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1474,f283])).

fof(f283,plain,(
    ! [X17,X18,X16] : k2_xboole_0(X16,k2_xboole_0(X17,X18)) = k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X18,X16))) ),
    inference(forward_demodulation,[],[f282,f44])).

fof(f282,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X18,X16))) ),
    inference(forward_demodulation,[],[f255,f170])).

fof(f170,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f37,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f255,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X18,k2_xboole_0(X16,X17)))) ),
    inference(superposition,[],[f44,f37])).

fof(f1474,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1473,f252])).

fof(f252,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f44,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1473,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1472,f283])).

fof(f1472,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1471,f252])).

fof(f1471,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1470,f37])).

fof(f1470,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1403,f30])).

fof(f1403,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f991,f64,f64,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X2,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f64,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f59,f57])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f49,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(backward_demodulation,[],[f51,f52])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f991,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f990,f68])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f30,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f990,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f989,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f48,f57])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f989,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f985,f955])).

fof(f955,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X25),X26)) = k4_xboole_0(X27,k2_xboole_0(X26,k4_xboole_0(X27,X25))) ),
    inference(forward_demodulation,[],[f954,f170])).

fof(f954,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X25),X26)) = k4_xboole_0(X27,k2_xboole_0(X26,k4_xboole_0(X27,k2_xboole_0(X25,X26)))) ),
    inference(forward_demodulation,[],[f953,f30])).

fof(f953,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,k2_xboole_0(X25,X26)),X26)) = k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X25),X26)) ),
    inference(forward_demodulation,[],[f889,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f55,f43])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f42,f34,f34])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f889,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,k2_xboole_0(X25,X26)),X26)) = k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X25,X26))) ),
    inference(superposition,[],[f61,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f985,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0)))) ),
    inference(backward_demodulation,[],[f63,f899])).

fof(f899,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7))) ),
    inference(superposition,[],[f61,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f45,f34])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f63,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f62,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f62,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f60,f61])).

fof(f60,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))) ),
    inference(backward_demodulation,[],[f47,f55])).

fof(f47,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f26,f39,f39,f34])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (3266)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (3283)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (3283)Refutation not found, incomplete strategy% (3283)------------------------------
% 0.21/0.55  % (3283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3275)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (3275)Refutation not found, incomplete strategy% (3275)------------------------------
% 0.21/0.55  % (3275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3283)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3283)Memory used [KB]: 1663
% 0.21/0.55  % (3283)Time elapsed: 0.069 s
% 0.21/0.55  % (3283)------------------------------
% 0.21/0.55  % (3283)------------------------------
% 0.21/0.55  % (3275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3275)Memory used [KB]: 6140
% 0.21/0.55  % (3275)Time elapsed: 0.069 s
% 0.21/0.55  % (3275)------------------------------
% 0.21/0.55  % (3275)------------------------------
% 0.21/0.55  % (3267)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (3260)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (3260)Refutation not found, incomplete strategy% (3260)------------------------------
% 0.21/0.56  % (3260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3260)Memory used [KB]: 1663
% 0.21/0.56  % (3260)Time elapsed: 0.138 s
% 0.21/0.56  % (3260)------------------------------
% 0.21/0.56  % (3260)------------------------------
% 0.21/0.57  % (3265)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (3282)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (3276)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (3268)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (3264)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (3264)Refutation not found, incomplete strategy% (3264)------------------------------
% 0.21/0.57  % (3264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (3264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (3264)Memory used [KB]: 6140
% 0.21/0.57  % (3264)Time elapsed: 0.152 s
% 0.21/0.57  % (3264)------------------------------
% 0.21/0.57  % (3264)------------------------------
% 0.21/0.57  % (3263)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (3268)Refutation not found, incomplete strategy% (3268)------------------------------
% 0.21/0.57  % (3268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (3270)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (3268)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (3268)Memory used [KB]: 10618
% 0.21/0.57  % (3268)Time elapsed: 0.149 s
% 0.21/0.57  % (3268)------------------------------
% 0.21/0.57  % (3268)------------------------------
% 0.21/0.58  % (3270)Refutation not found, incomplete strategy% (3270)------------------------------
% 0.21/0.58  % (3270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (3270)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (3270)Memory used [KB]: 10618
% 0.21/0.58  % (3270)Time elapsed: 0.152 s
% 0.21/0.58  % (3270)------------------------------
% 0.21/0.58  % (3270)------------------------------
% 0.21/0.58  % (3271)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (3261)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (3289)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.58  % (3274)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.64/0.59  % (3286)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.64/0.59  % (3288)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.64/0.59  % (3281)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.59  % (3282)Refutation not found, incomplete strategy% (3282)------------------------------
% 1.64/0.59  % (3282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (3282)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (3282)Memory used [KB]: 10746
% 1.64/0.59  % (3282)Time elapsed: 0.168 s
% 1.64/0.59  % (3282)------------------------------
% 1.64/0.59  % (3282)------------------------------
% 1.64/0.59  % (3285)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.64/0.59  % (3279)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.64/0.59  % (3262)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.59  % (3269)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.64/0.59  % (3262)Refutation not found, incomplete strategy% (3262)------------------------------
% 1.64/0.59  % (3262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (3262)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (3262)Memory used [KB]: 10746
% 1.64/0.59  % (3262)Time elapsed: 0.174 s
% 1.64/0.59  % (3262)------------------------------
% 1.64/0.59  % (3262)------------------------------
% 1.64/0.59  % (3278)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.64/0.59  % (3269)Refutation not found, incomplete strategy% (3269)------------------------------
% 1.64/0.59  % (3269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (3269)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (3269)Memory used [KB]: 10618
% 1.64/0.59  % (3269)Time elapsed: 0.177 s
% 1.64/0.59  % (3269)------------------------------
% 1.64/0.59  % (3269)------------------------------
% 1.64/0.60  % (3287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.64/0.60  % (3273)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.64/0.60  % (3280)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.64/0.60  % (3277)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.64/0.60  % (3280)Refutation not found, incomplete strategy% (3280)------------------------------
% 1.64/0.60  % (3280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.60  % (3277)Refutation not found, incomplete strategy% (3277)------------------------------
% 1.90/0.60  % (3277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.60  % (3285)Refutation not found, incomplete strategy% (3285)------------------------------
% 1.90/0.60  % (3285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.60  % (3285)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.60  
% 1.90/0.60  % (3285)Memory used [KB]: 6268
% 1.90/0.60  % (3285)Time elapsed: 0.167 s
% 1.90/0.60  % (3285)------------------------------
% 1.90/0.60  % (3285)------------------------------
% 1.90/0.61  % (3284)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.90/0.61  % (3277)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (3277)Memory used [KB]: 10618
% 1.90/0.61  % (3277)Time elapsed: 0.178 s
% 1.90/0.61  % (3277)------------------------------
% 1.90/0.61  % (3277)------------------------------
% 1.90/0.61  % (3272)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.90/0.61  % (3286)Refutation not found, incomplete strategy% (3286)------------------------------
% 1.90/0.61  % (3286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (3286)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (3286)Memory used [KB]: 10746
% 1.90/0.61  % (3286)Time elapsed: 0.186 s
% 1.90/0.61  % (3286)------------------------------
% 1.90/0.61  % (3286)------------------------------
% 1.90/0.61  % (3281)Refutation not found, incomplete strategy% (3281)------------------------------
% 1.90/0.61  % (3281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (3281)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (3281)Memory used [KB]: 1663
% 1.90/0.61  % (3281)Time elapsed: 0.187 s
% 1.90/0.61  % (3281)------------------------------
% 1.90/0.61  % (3281)------------------------------
% 1.90/0.62  % (3280)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.62  
% 1.90/0.62  % (3280)Memory used [KB]: 10746
% 1.90/0.62  % (3280)Time elapsed: 0.177 s
% 1.90/0.62  % (3280)------------------------------
% 1.90/0.62  % (3280)------------------------------
% 2.08/0.65  % (3310)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.08/0.68  % (3309)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.08/0.68  % (3315)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.08/0.69  % (3308)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.08/0.69  % (3308)Refutation not found, incomplete strategy% (3308)------------------------------
% 2.08/0.69  % (3308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.69  % (3308)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.69  
% 2.08/0.69  % (3308)Memory used [KB]: 6140
% 2.08/0.69  % (3308)Time elapsed: 0.103 s
% 2.08/0.69  % (3308)------------------------------
% 2.08/0.69  % (3308)------------------------------
% 2.08/0.69  % (3321)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.08/0.70  % (3314)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.08/0.70  % (3284)Refutation found. Thanks to Tanya!
% 2.08/0.70  % SZS status Theorem for theBenchmark
% 2.08/0.70  % SZS output start Proof for theBenchmark
% 2.08/0.70  fof(f1477,plain,(
% 2.08/0.70    $false),
% 2.08/0.70    inference(trivial_inequality_removal,[],[f1476])).
% 2.08/0.70  fof(f1476,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)),
% 2.08/0.70    inference(forward_demodulation,[],[f1475,f455])).
% 2.08/0.70  fof(f455,plain,(
% 2.08/0.70    ( ! [X14,X15,X13] : (k2_xboole_0(X13,X15) = k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15))) )),
% 2.08/0.70    inference(superposition,[],[f44,f413])).
% 2.08/0.70  fof(f413,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.08/0.70    inference(superposition,[],[f50,f52])).
% 2.08/0.70  fof(f52,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.08/0.70    inference(definition_unfolding,[],[f35,f34])).
% 2.08/0.70  fof(f34,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f13])).
% 2.08/0.70  fof(f13,axiom,(
% 2.08/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.08/0.70  fof(f35,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f12])).
% 2.08/0.70  fof(f12,axiom,(
% 2.08/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.08/0.70  fof(f50,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 2.08/0.70    inference(definition_unfolding,[],[f32,f34])).
% 2.08/0.70  fof(f32,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.08/0.70    inference(cnf_transformation,[],[f6])).
% 2.08/0.70  fof(f6,axiom,(
% 2.08/0.70    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.08/0.70  fof(f44,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f15])).
% 2.08/0.70  fof(f15,axiom,(
% 2.08/0.70    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.08/0.70  fof(f1475,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k1_xboole_0)),
% 2.08/0.70    inference(forward_demodulation,[],[f1474,f283])).
% 2.08/0.70  fof(f283,plain,(
% 2.08/0.70    ( ! [X17,X18,X16] : (k2_xboole_0(X16,k2_xboole_0(X17,X18)) = k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X18,X16)))) )),
% 2.08/0.70    inference(forward_demodulation,[],[f282,f44])).
% 2.08/0.70  fof(f282,plain,(
% 2.08/0.70    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X18,X16)))) )),
% 2.08/0.70    inference(forward_demodulation,[],[f255,f170])).
% 2.08/0.70  fof(f170,plain,(
% 2.08/0.70    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 2.08/0.70    inference(superposition,[],[f37,f43])).
% 2.08/0.70  fof(f43,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f10])).
% 2.08/0.70  fof(f10,axiom,(
% 2.08/0.70    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.08/0.70  fof(f37,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f8])).
% 2.08/0.70  fof(f8,axiom,(
% 2.08/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.08/0.70  fof(f255,plain,(
% 2.08/0.70    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X18,k2_xboole_0(X16,X17))))) )),
% 2.08/0.70    inference(superposition,[],[f44,f37])).
% 2.08/0.70  fof(f1474,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0)),
% 2.08/0.70    inference(forward_demodulation,[],[f1473,f252])).
% 2.08/0.70  fof(f252,plain,(
% 2.08/0.70    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))) )),
% 2.08/0.70    inference(superposition,[],[f44,f30])).
% 2.08/0.70  fof(f30,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.08/0.70    inference(cnf_transformation,[],[f1])).
% 2.08/0.70  fof(f1,axiom,(
% 2.08/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.08/0.70  fof(f1473,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k1_xboole_0)),
% 2.08/0.70    inference(forward_demodulation,[],[f1472,f283])).
% 2.08/0.70  fof(f1472,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k1_xboole_0)),
% 2.08/0.70    inference(forward_demodulation,[],[f1471,f252])).
% 2.08/0.70  fof(f1471,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0)),
% 2.08/0.70    inference(forward_demodulation,[],[f1470,f37])).
% 2.08/0.70  fof(f1470,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k1_xboole_0)),
% 2.08/0.70    inference(forward_demodulation,[],[f1403,f30])).
% 2.08/0.70  fof(f1403,plain,(
% 2.08/0.70    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_xboole_0)),
% 2.08/0.70    inference(unit_resulting_resolution,[],[f991,f64,f64,f46])).
% 2.08/0.70  fof(f46,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X2,X1) | X0 = X2) )),
% 2.08/0.70    inference(cnf_transformation,[],[f25])).
% 2.08/0.70  fof(f25,plain,(
% 2.08/0.70    ! [X0,X1,X2] : (X0 = X2 | ~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1))),
% 2.08/0.70    inference(flattening,[],[f24])).
% 2.08/0.70  fof(f24,plain,(
% 2.08/0.70    ! [X0,X1,X2] : (X0 = X2 | (~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)))),
% 2.08/0.70    inference(ennf_transformation,[],[f18])).
% 2.08/0.70  fof(f18,axiom,(
% 2.08/0.70    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 2.08/0.70  fof(f64,plain,(
% 2.08/0.70    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.70    inference(superposition,[],[f59,f57])).
% 2.08/0.70  fof(f57,plain,(
% 2.08/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.70    inference(forward_demodulation,[],[f49,f29])).
% 2.08/0.70  fof(f29,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f11])).
% 2.08/0.70  fof(f11,axiom,(
% 2.08/0.70    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.08/0.70  fof(f49,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 2.08/0.70    inference(definition_unfolding,[],[f31,f34])).
% 2.08/0.70  fof(f31,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.08/0.70    inference(cnf_transformation,[],[f5])).
% 2.08/0.70  fof(f5,axiom,(
% 2.08/0.70    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.08/0.70  fof(f59,plain,(
% 2.08/0.70    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.08/0.70    inference(backward_demodulation,[],[f51,f52])).
% 2.08/0.70  fof(f51,plain,(
% 2.08/0.70    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) )),
% 2.08/0.70    inference(definition_unfolding,[],[f33,f34])).
% 2.08/0.70  fof(f33,plain,(
% 2.08/0.70    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.08/0.70    inference(cnf_transformation,[],[f19])).
% 2.08/0.70  fof(f19,axiom,(
% 2.08/0.70    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
% 2.08/0.70  fof(f991,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.08/0.70    inference(forward_demodulation,[],[f990,f68])).
% 2.08/0.70  fof(f68,plain,(
% 2.08/0.70    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.08/0.70    inference(superposition,[],[f30,f28])).
% 2.08/0.70  fof(f28,plain,(
% 2.08/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.70    inference(cnf_transformation,[],[f4])).
% 2.08/0.70  fof(f4,axiom,(
% 2.08/0.70    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.08/0.70  fof(f990,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))))),
% 2.08/0.70    inference(forward_demodulation,[],[f989,f58])).
% 2.08/0.70  fof(f58,plain,(
% 2.08/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.08/0.70    inference(backward_demodulation,[],[f48,f57])).
% 2.08/0.70  fof(f48,plain,(
% 2.08/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.08/0.70    inference(definition_unfolding,[],[f27,f34])).
% 2.08/0.70  fof(f27,plain,(
% 2.08/0.70    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.70    inference(cnf_transformation,[],[f7])).
% 2.08/0.70  fof(f7,axiom,(
% 2.08/0.70    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.08/0.70  fof(f989,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK1))))),
% 2.08/0.70    inference(forward_demodulation,[],[f985,f955])).
% 2.08/0.70  fof(f955,plain,(
% 2.08/0.70    ( ! [X26,X27,X25] : (k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X25),X26)) = k4_xboole_0(X27,k2_xboole_0(X26,k4_xboole_0(X27,X25)))) )),
% 2.08/0.70    inference(forward_demodulation,[],[f954,f170])).
% 2.08/0.70  fof(f954,plain,(
% 2.08/0.70    ( ! [X26,X27,X25] : (k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X25),X26)) = k4_xboole_0(X27,k2_xboole_0(X26,k4_xboole_0(X27,k2_xboole_0(X25,X26))))) )),
% 2.08/0.70    inference(forward_demodulation,[],[f953,f30])).
% 2.08/0.70  fof(f953,plain,(
% 2.08/0.70    ( ! [X26,X27,X25] : (k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,k2_xboole_0(X25,X26)),X26)) = k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X25),X26))) )),
% 2.08/0.70    inference(forward_demodulation,[],[f889,f61])).
% 2.08/0.70  fof(f61,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 2.08/0.70    inference(backward_demodulation,[],[f55,f43])).
% 2.08/0.70  fof(f55,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.08/0.70    inference(definition_unfolding,[],[f42,f34,f34])).
% 2.08/0.70  fof(f42,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.08/0.70    inference(cnf_transformation,[],[f14])).
% 2.08/0.70  fof(f14,axiom,(
% 2.08/0.70    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.08/0.70  fof(f889,plain,(
% 2.08/0.70    ( ! [X26,X27,X25] : (k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,k2_xboole_0(X25,X26)),X26)) = k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X25,X26)))) )),
% 2.08/0.70    inference(superposition,[],[f61,f36])).
% 2.08/0.70  fof(f36,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.08/0.70    inference(cnf_transformation,[],[f9])).
% 2.08/0.70  fof(f9,axiom,(
% 2.08/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.08/0.70  fof(f985,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0))))),
% 2.08/0.70    inference(backward_demodulation,[],[f63,f899])).
% 2.08/0.70  fof(f899,plain,(
% 2.08/0.70    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X7))) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)))) )),
% 2.08/0.70    inference(superposition,[],[f61,f56])).
% 2.08/0.70  fof(f56,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 2.08/0.70    inference(definition_unfolding,[],[f45,f34])).
% 2.08/0.70  fof(f45,plain,(
% 2.08/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f3])).
% 2.08/0.70  fof(f3,axiom,(
% 2.08/0.70    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 2.08/0.70  fof(f63,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.08/0.70    inference(forward_demodulation,[],[f62,f38])).
% 2.08/0.70  fof(f38,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f17])).
% 2.08/0.70  fof(f17,axiom,(
% 2.08/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.08/0.70  fof(f62,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 2.08/0.70    inference(backward_demodulation,[],[f60,f61])).
% 2.08/0.70  fof(f60,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))))),
% 2.08/0.70    inference(backward_demodulation,[],[f47,f55])).
% 2.08/0.70  fof(f47,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.08/0.70    inference(definition_unfolding,[],[f26,f39,f39,f34])).
% 2.08/0.70  fof(f39,plain,(
% 2.08/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.08/0.70    inference(cnf_transformation,[],[f2])).
% 2.08/0.70  fof(f2,axiom,(
% 2.08/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.08/0.70  fof(f26,plain,(
% 2.08/0.70    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.08/0.70    inference(cnf_transformation,[],[f23])).
% 2.08/0.70  fof(f23,plain,(
% 2.08/0.70    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.08/0.70    inference(ennf_transformation,[],[f22])).
% 2.08/0.70  fof(f22,negated_conjecture,(
% 2.08/0.70    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.08/0.70    inference(negated_conjecture,[],[f21])).
% 2.08/0.70  fof(f21,conjecture,(
% 2.08/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.08/0.70  % SZS output end Proof for theBenchmark
% 2.08/0.70  % (3284)------------------------------
% 2.08/0.70  % (3284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.70  % (3284)Termination reason: Refutation
% 2.08/0.70  
% 2.08/0.70  % (3284)Memory used [KB]: 7419
% 2.08/0.70  % (3284)Time elapsed: 0.279 s
% 2.08/0.70  % (3284)------------------------------
% 2.08/0.70  % (3284)------------------------------
% 2.08/0.70  % (3259)Success in time 0.349 s
%------------------------------------------------------------------------------
