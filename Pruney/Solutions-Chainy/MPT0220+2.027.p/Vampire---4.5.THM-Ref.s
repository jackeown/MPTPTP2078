%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:40 EST 2020

% Result     : Theorem 3.79s
% Output     : Refutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 686 expanded)
%              Number of leaves         :   24 ( 226 expanded)
%              Depth                    :   34
%              Number of atoms          :  185 ( 742 expanded)
%              Number of equality atoms :  123 ( 665 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3972,plain,(
    $false ),
    inference(resolution,[],[f3948,f97])).

fof(f97,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,X0) ) ),
    inference(forward_demodulation,[],[f92,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f75,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f3948,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3947,f34])).

fof(f3947,plain,(
    ~ r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3946,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f56,f66,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f3946,plain,(
    ~ r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3945,f916])).

fof(f916,plain,(
    ! [X30,X28,X26,X31,X29,X27,X25,X32] : k3_xboole_0(k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32),k5_xboole_0(k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32),k6_enumset1(X25,X25,X26,X27,X28,X29,X30,X31))) = k5_xboole_0(k6_enumset1(X25,X25,X26,X27,X28,X29,X30,X31),k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32)) ),
    inference(superposition,[],[f184,f743])).

fof(f743,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(backward_demodulation,[],[f71,f715])).

fof(f715,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f497,f714])).

fof(f714,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f713,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f713,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f697,f384])).

fof(f384,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k5_xboole_0(X7,X5),X6) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f55,f39])).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f697,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f83,f248])).

fof(f248,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f54,f37])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f78,f54])).

fof(f78,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f53,f43,f43])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f497,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f474,f248])).

fof(f474,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f83,f37])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f61,f63,f60,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f184,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f165,f84])).

fof(f84,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f165,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f52,f34])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3945,plain,(
    ~ r1_tarski(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3944,f35])).

fof(f3944,plain,(
    ~ r1_tarski(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3943,f39])).

fof(f3943,plain,(
    ~ r1_tarski(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3942,f34])).

fof(f3942,plain,(
    ~ r1_tarski(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3941,f2342])).

fof(f2342,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f2301,f52])).

fof(f2301,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12)) ),
    inference(superposition,[],[f405,f52])).

fof(f405,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f375,f39])).

fof(f375,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f55,f37])).

fof(f3941,plain,(
    ~ r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3940,f38])).

fof(f3940,plain,(
    ~ r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3939,f173])).

fof(f173,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f52,f38])).

fof(f3939,plain,(
    ~ r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3913,f38])).

fof(f3913,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f411,f3573])).

fof(f3573,plain,(
    ! [X39,X40] :
      ( ~ r1_tarski(k5_xboole_0(X39,X40),k1_xboole_0)
      | X39 = X40 ) ),
    inference(superposition,[],[f3270,f209])).

fof(f209,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7 ),
    inference(superposition,[],[f189,f184])).

fof(f189,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f184,f38])).

fof(f3270,plain,(
    ! [X4,X2] :
      ( k5_xboole_0(X2,X4) = X4
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(global_subsumption,[],[f1333,f3269])).

fof(f3269,plain,(
    ! [X4,X2,X3] :
      ( k5_xboole_0(X2,X4) = X4
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f3195,f84])).

fof(f3195,plain,(
    ! [X4,X2,X3] :
      ( k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X4)) = X4
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f185,f1661])).

fof(f1661,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 = k3_xboole_0(X8,X7)
      | ~ r1_tarski(X8,k1_xboole_0) ) ),
    inference(superposition,[],[f1192,f39])).

fof(f1192,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k1_xboole_0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f960,f455])).

fof(f455,plain,(
    ! [X3] :
      ( r2_xboole_0(k1_xboole_0,X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f428,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f428,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(trivial_inequality_removal,[],[f420])).

fof(f420,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X4) ) ),
    inference(backward_demodulation,[],[f95,f419])).

fof(f419,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f390,f34])).

fof(f390,plain,(
    ! [X6,X5] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X5,X5),X6) ),
    inference(superposition,[],[f55,f34])).

fof(f95,plain,(
    ! [X4] :
      ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X4)
      | r1_tarski(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f75,f84])).

fof(f960,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_xboole_0(X6,k3_xboole_0(X7,X5))
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f887,f201])).

fof(f201,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X5,X6) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(forward_demodulation,[],[f191,f35])).

fof(f191,plain,(
    ! [X6,X5] :
      ( k5_xboole_0(X5,k1_xboole_0) = k3_xboole_0(X5,X6)
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f184,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f887,plain,(
    ! [X14,X15,X16] : ~ r2_xboole_0(X16,k3_xboole_0(X14,k3_xboole_0(X15,X16))) ),
    inference(superposition,[],[f862,f54])).

fof(f862,plain,(
    ! [X2,X3] : ~ r2_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(trivial_inequality_removal,[],[f861])).

fof(f861,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_xboole_0(X3,k3_xboole_0(X2,X3)) ) ),
    inference(backward_demodulation,[],[f726,f857])).

fof(f857,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f856,f419])).

fof(f856,plain,(
    ! [X2,X1] : k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f855,f34])).

fof(f855,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k3_xboole_0(k5_xboole_0(X2,X2),X1) ),
    inference(forward_demodulation,[],[f843,f377])).

fof(f377,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k3_xboole_0(X6,X5),k3_xboole_0(X7,X6)) ),
    inference(superposition,[],[f55,f39])).

fof(f843,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f720,f688])).

fof(f688,plain,(
    ! [X6,X5] : k3_xboole_0(X6,X5) = k3_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f248,f39])).

fof(f720,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f83,f715])).

fof(f726,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X3,k3_xboole_0(X2,k5_xboole_0(X2,X3)))
      | ~ r2_xboole_0(X3,k3_xboole_0(X2,X3)) ) ),
    inference(backward_demodulation,[],[f438,f715])).

fof(f438,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
      | ~ r2_xboole_0(X3,k3_xboole_0(X2,X3)) ) ),
    inference(forward_demodulation,[],[f394,f39])).

fof(f394,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3)
      | ~ r2_xboole_0(X3,k3_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f77,f55])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X1,X0))
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f185,plain,(
    ! [X10,X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = X10
      | ~ r1_tarski(X8,X9) ) ),
    inference(forward_demodulation,[],[f168,f84])).

fof(f168,plain,(
    ! [X10,X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k1_xboole_0,X10)
      | ~ r1_tarski(X8,X9) ) ),
    inference(superposition,[],[f52,f76])).

fof(f1333,plain,(
    ! [X30,X29] :
      ( ~ r1_tarski(X30,k1_xboole_0)
      | r1_tarski(X30,X29) ) ),
    inference(superposition,[],[f1037,f419])).

fof(f1037,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(X9,k3_xboole_0(X10,X11))
      | r1_tarski(X9,X11) ) ),
    inference(superposition,[],[f906,f201])).

fof(f906,plain,(
    ! [X14,X15,X16] : r1_tarski(k3_xboole_0(X14,k3_xboole_0(X15,X16)),X16) ),
    inference(superposition,[],[f863,f54])).

fof(f863,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X7) ),
    inference(trivial_inequality_removal,[],[f860])).

fof(f860,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k3_xboole_0(X6,X7),X7) ) ),
    inference(backward_demodulation,[],[f727,f857])).

fof(f727,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k3_xboole_0(X7,k3_xboole_0(X6,k5_xboole_0(X6,X7)))
      | r1_tarski(k3_xboole_0(X6,X7),X7) ) ),
    inference(backward_demodulation,[],[f440,f715])).

fof(f440,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k3_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X6,X7)))
      | r1_tarski(k3_xboole_0(X6,X7),X7) ) ),
    inference(forward_demodulation,[],[f396,f39])).

fof(f396,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k3_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X7)
      | r1_tarski(k3_xboole_0(X6,X7),X7) ) ),
    inference(superposition,[],[f75,f55])).

fof(f411,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f410,f38])).

fof(f410,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f81,f405])).

fof(f81,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(backward_demodulation,[],[f72,f39])).

fof(f72,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f33,f68,f63,f69,f68])).

fof(f33,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (27862)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (27862)Refutation not found, incomplete strategy% (27862)------------------------------
% 0.21/0.48  % (27862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27862)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27862)Memory used [KB]: 10746
% 0.21/0.48  % (27862)Time elapsed: 0.070 s
% 0.21/0.48  % (27862)------------------------------
% 0.21/0.48  % (27862)------------------------------
% 0.21/0.48  % (27878)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.48  % (27878)Refutation not found, incomplete strategy% (27878)------------------------------
% 0.21/0.48  % (27878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27878)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27878)Memory used [KB]: 10618
% 0.21/0.48  % (27878)Time elapsed: 0.071 s
% 0.21/0.48  % (27878)------------------------------
% 0.21/0.48  % (27878)------------------------------
% 0.21/0.52  % (27866)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (27864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (27863)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (27864)Refutation not found, incomplete strategy% (27864)------------------------------
% 0.21/0.52  % (27864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27864)Memory used [KB]: 6140
% 0.21/0.52  % (27864)Time elapsed: 0.117 s
% 0.21/0.52  % (27864)------------------------------
% 0.21/0.52  % (27864)------------------------------
% 0.21/0.52  % (27884)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (27884)Refutation not found, incomplete strategy% (27884)------------------------------
% 0.21/0.52  % (27884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27884)Memory used [KB]: 1663
% 0.21/0.52  % (27884)Time elapsed: 0.091 s
% 0.21/0.52  % (27884)------------------------------
% 0.21/0.52  % (27884)------------------------------
% 0.21/0.52  % (27867)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (27876)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (27859)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (27859)Refutation not found, incomplete strategy% (27859)------------------------------
% 0.21/0.53  % (27859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27859)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27859)Memory used [KB]: 1663
% 0.21/0.53  % (27859)Time elapsed: 0.125 s
% 0.21/0.53  % (27859)------------------------------
% 0.21/0.53  % (27859)------------------------------
% 0.21/0.53  % (27871)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (27871)Refutation not found, incomplete strategy% (27871)------------------------------
% 0.21/0.53  % (27871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27871)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27871)Memory used [KB]: 10618
% 0.21/0.53  % (27871)Time elapsed: 0.124 s
% 0.21/0.53  % (27871)------------------------------
% 0.21/0.53  % (27871)------------------------------
% 0.21/0.53  % (27874)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (27869)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (27860)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (27869)Refutation not found, incomplete strategy% (27869)------------------------------
% 0.21/0.53  % (27869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27869)Memory used [KB]: 10618
% 0.21/0.53  % (27869)Time elapsed: 0.128 s
% 0.21/0.53  % (27869)------------------------------
% 0.21/0.53  % (27869)------------------------------
% 0.21/0.53  % (27890)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (27889)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27882)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (27882)Refutation not found, incomplete strategy% (27882)------------------------------
% 0.21/0.54  % (27882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27882)Memory used [KB]: 1663
% 0.21/0.54  % (27882)Time elapsed: 0.129 s
% 0.21/0.54  % (27882)------------------------------
% 0.21/0.54  % (27882)------------------------------
% 0.21/0.54  % (27888)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (27891)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (27888)Refutation not found, incomplete strategy% (27888)------------------------------
% 0.21/0.54  % (27888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27888)Memory used [KB]: 10746
% 0.21/0.54  % (27888)Time elapsed: 0.136 s
% 0.21/0.54  % (27888)------------------------------
% 0.21/0.54  % (27888)------------------------------
% 0.21/0.54  % (27868)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (27887)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (27880)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (27885)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (27883)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (27883)Refutation not found, incomplete strategy% (27883)------------------------------
% 0.21/0.55  % (27883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27883)Memory used [KB]: 10746
% 0.21/0.55  % (27883)Time elapsed: 0.139 s
% 0.21/0.55  % (27883)------------------------------
% 0.21/0.55  % (27883)------------------------------
% 0.21/0.55  % (27887)Refutation not found, incomplete strategy% (27887)------------------------------
% 0.21/0.55  % (27887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27873)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (27879)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (27875)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (27881)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (27877)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (27887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27887)Memory used [KB]: 6268
% 0.21/0.55  % (27887)Time elapsed: 0.118 s
% 0.21/0.55  % (27887)------------------------------
% 0.21/0.55  % (27887)------------------------------
% 0.21/0.55  % (27881)Refutation not found, incomplete strategy% (27881)------------------------------
% 0.21/0.55  % (27881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27881)Memory used [KB]: 10746
% 0.21/0.55  % (27881)Time elapsed: 0.149 s
% 0.21/0.55  % (27881)------------------------------
% 0.21/0.55  % (27881)------------------------------
% 0.21/0.55  % (27872)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (27872)Refutation not found, incomplete strategy% (27872)------------------------------
% 0.21/0.55  % (27872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27872)Memory used [KB]: 10618
% 0.21/0.55  % (27872)Time elapsed: 0.149 s
% 0.21/0.55  % (27872)------------------------------
% 0.21/0.55  % (27872)------------------------------
% 0.21/0.55  % (27870)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (27951)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 0.21/0.56  % (27870)Refutation not found, incomplete strategy% (27870)------------------------------
% 0.21/0.56  % (27870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27870)Memory used [KB]: 10618
% 0.21/0.56  % (27870)Time elapsed: 0.148 s
% 0.21/0.56  % (27870)------------------------------
% 0.21/0.56  % (27870)------------------------------
% 0.21/0.56  % (27946)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.56  % (27946)Refutation not found, incomplete strategy% (27946)------------------------------
% 0.21/0.56  % (27946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (27946)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (27946)Memory used [KB]: 6140
% 1.60/0.57  % (27946)Time elapsed: 0.029 s
% 1.60/0.57  % (27946)------------------------------
% 1.60/0.57  % (27946)------------------------------
% 2.03/0.63  % (27980)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.17/0.66  % (27986)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.17/0.66  % (28015)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.17/0.67  % (27988)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.17/0.67  % (27993)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.17/0.67  % (27993)Refutation not found, incomplete strategy% (27993)------------------------------
% 2.17/0.67  % (27993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (27993)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (27993)Memory used [KB]: 1791
% 2.17/0.67  % (27993)Time elapsed: 0.107 s
% 2.17/0.67  % (27993)------------------------------
% 2.17/0.67  % (27993)------------------------------
% 2.17/0.67  % (27992)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.17/0.68  % (27989)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.17/0.68  % (28001)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.17/0.68  % (27997)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.17/0.68  % (28001)Refutation not found, incomplete strategy% (28001)------------------------------
% 2.17/0.68  % (28001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (28001)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (28001)Memory used [KB]: 1791
% 2.17/0.68  % (28001)Time elapsed: 0.109 s
% 2.17/0.68  % (28001)------------------------------
% 2.17/0.68  % (28001)------------------------------
% 2.17/0.68  % (27999)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.17/0.69  % (27990)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.17/0.69  % (28007)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.17/0.69  % (28007)Refutation not found, incomplete strategy% (28007)------------------------------
% 2.17/0.69  % (28007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (28007)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (28007)Memory used [KB]: 1663
% 2.17/0.69  % (28007)Time elapsed: 0.113 s
% 2.17/0.69  % (28007)------------------------------
% 2.17/0.69  % (28007)------------------------------
% 2.17/0.69  % (27999)Refutation not found, incomplete strategy% (27999)------------------------------
% 2.17/0.69  % (27999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (27999)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (27999)Memory used [KB]: 6268
% 2.17/0.69  % (27999)Time elapsed: 0.119 s
% 2.17/0.69  % (27999)------------------------------
% 2.17/0.69  % (27999)------------------------------
% 2.17/0.69  % (28005)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 3.07/0.80  % (28048)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 3.07/0.81  % (28043)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 3.07/0.81  % (28038)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.07/0.81  % (28038)Refutation not found, incomplete strategy% (28038)------------------------------
% 3.07/0.81  % (28038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.81  % (28038)Termination reason: Refutation not found, incomplete strategy
% 3.07/0.81  
% 3.07/0.81  % (28038)Memory used [KB]: 6268
% 3.07/0.81  % (28038)Time elapsed: 0.120 s
% 3.07/0.81  % (28038)------------------------------
% 3.07/0.81  % (28038)------------------------------
% 3.07/0.82  % (27866)Time limit reached!
% 3.07/0.82  % (27866)------------------------------
% 3.07/0.82  % (27866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.82  % (27866)Termination reason: Time limit
% 3.07/0.82  
% 3.07/0.82  % (27866)Memory used [KB]: 10490
% 3.07/0.82  % (27866)Time elapsed: 0.416 s
% 3.07/0.82  % (27866)------------------------------
% 3.07/0.82  % (27866)------------------------------
% 3.07/0.84  % (28047)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 3.07/0.84  % (28047)Refutation not found, incomplete strategy% (28047)------------------------------
% 3.07/0.84  % (28047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.84  % (28047)Termination reason: Refutation not found, incomplete strategy
% 3.07/0.84  
% 3.07/0.84  % (28047)Memory used [KB]: 6140
% 3.07/0.84  % (28047)Time elapsed: 0.128 s
% 3.07/0.84  % (28047)------------------------------
% 3.07/0.84  % (28047)------------------------------
% 3.79/0.91  % (27885)Refutation found. Thanks to Tanya!
% 3.79/0.91  % SZS status Theorem for theBenchmark
% 3.79/0.91  % SZS output start Proof for theBenchmark
% 3.79/0.91  fof(f3972,plain,(
% 3.79/0.91    $false),
% 3.79/0.91    inference(resolution,[],[f3948,f97])).
% 3.79/0.91  fof(f97,plain,(
% 3.79/0.91    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.79/0.91    inference(trivial_inequality_removal,[],[f96])).
% 3.79/0.91  fof(f96,plain,(
% 3.79/0.91    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,X0)) )),
% 3.79/0.91    inference(forward_demodulation,[],[f92,f34])).
% 3.79/0.91  fof(f34,plain,(
% 3.79/0.91    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f15])).
% 3.79/0.91  fof(f15,axiom,(
% 3.79/0.91    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.79/0.91  fof(f92,plain,(
% 3.79/0.91    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(X0,X0) | r1_tarski(X0,X0)) )),
% 3.79/0.91    inference(superposition,[],[f75,f37])).
% 3.79/0.91  fof(f37,plain,(
% 3.79/0.91    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.79/0.91    inference(cnf_transformation,[],[f29])).
% 3.79/0.91  fof(f29,plain,(
% 3.79/0.91    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.79/0.91    inference(rectify,[],[f4])).
% 3.79/0.91  fof(f4,axiom,(
% 3.79/0.91    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.79/0.91  fof(f75,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f49,f43])).
% 3.79/0.91  fof(f43,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.79/0.91    inference(cnf_transformation,[],[f6])).
% 3.79/0.91  fof(f6,axiom,(
% 3.79/0.91    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.79/0.91  fof(f49,plain,(
% 3.79/0.91    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.79/0.91    inference(cnf_transformation,[],[f5])).
% 3.79/0.91  fof(f5,axiom,(
% 3.79/0.91    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.79/0.91  fof(f3948,plain,(
% 3.79/0.91    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3947,f34])).
% 3.79/0.91  fof(f3947,plain,(
% 3.79/0.91    ~r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3946,f79])).
% 3.79/0.91  fof(f79,plain,(
% 3.79/0.91    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f56,f66,f66])).
% 3.79/0.91  fof(f66,plain,(
% 3.79/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f57,f65])).
% 3.79/0.91  fof(f65,plain,(
% 3.79/0.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f58,f64])).
% 3.79/0.91  fof(f64,plain,(
% 3.79/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f59,f60])).
% 3.79/0.91  fof(f60,plain,(
% 3.79/0.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f26])).
% 3.79/0.91  fof(f26,axiom,(
% 3.79/0.91    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 3.79/0.91  fof(f59,plain,(
% 3.79/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f25])).
% 3.79/0.91  fof(f25,axiom,(
% 3.79/0.91    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 3.79/0.91  fof(f58,plain,(
% 3.79/0.91    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f24])).
% 3.79/0.91  fof(f24,axiom,(
% 3.79/0.91    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.79/0.91  fof(f57,plain,(
% 3.79/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f23])).
% 3.79/0.91  fof(f23,axiom,(
% 3.79/0.91    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.79/0.91  fof(f56,plain,(
% 3.79/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f17])).
% 3.79/0.91  fof(f17,axiom,(
% 3.79/0.91    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 3.79/0.91  fof(f3946,plain,(
% 3.79/0.91    ~r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK0)),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3945,f916])).
% 3.79/0.91  fof(f916,plain,(
% 3.79/0.91    ( ! [X30,X28,X26,X31,X29,X27,X25,X32] : (k3_xboole_0(k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32),k5_xboole_0(k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32),k6_enumset1(X25,X25,X26,X27,X28,X29,X30,X31))) = k5_xboole_0(k6_enumset1(X25,X25,X26,X27,X28,X29,X30,X31),k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32))) )),
% 3.79/0.91    inference(superposition,[],[f184,f743])).
% 3.79/0.91  fof(f743,plain,(
% 3.79/0.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 3.79/0.91    inference(backward_demodulation,[],[f71,f715])).
% 3.79/0.91  fof(f715,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.79/0.91    inference(backward_demodulation,[],[f497,f714])).
% 3.79/0.91  fof(f714,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f713,f39])).
% 3.79/0.91  fof(f39,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f1])).
% 3.79/0.91  fof(f1,axiom,(
% 3.79/0.91    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.79/0.91  fof(f713,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f697,f384])).
% 3.79/0.91  fof(f384,plain,(
% 3.79/0.91    ( ! [X6,X7,X5] : (k3_xboole_0(k5_xboole_0(X7,X5),X6) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X6,X5))) )),
% 3.79/0.91    inference(superposition,[],[f55,f39])).
% 3.79/0.91  fof(f55,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f8])).
% 3.79/0.91  fof(f8,axiom,(
% 3.79/0.91    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 3.79/0.91  fof(f697,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1))) )),
% 3.79/0.91    inference(superposition,[],[f83,f248])).
% 3.79/0.91  fof(f248,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.79/0.91    inference(superposition,[],[f54,f37])).
% 3.79/0.91  fof(f54,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 3.79/0.91    inference(cnf_transformation,[],[f10])).
% 3.79/0.91  fof(f10,axiom,(
% 3.79/0.91    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 3.79/0.91  fof(f83,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 3.79/0.91    inference(backward_demodulation,[],[f78,f54])).
% 3.79/0.91  fof(f78,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 3.79/0.91    inference(definition_unfolding,[],[f53,f43,f43])).
% 3.79/0.91  fof(f53,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f12])).
% 3.79/0.91  fof(f12,axiom,(
% 3.79/0.91    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 3.79/0.91  fof(f497,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f474,f248])).
% 3.79/0.91  fof(f474,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.79/0.91    inference(superposition,[],[f83,f37])).
% 3.79/0.91  fof(f71,plain,(
% 3.79/0.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 3.79/0.91    inference(definition_unfolding,[],[f61,f63,f60,f69])).
% 3.79/0.91  fof(f69,plain,(
% 3.79/0.91    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f36,f68])).
% 3.79/0.91  fof(f68,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f41,f67])).
% 3.79/0.91  fof(f67,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f51,f66])).
% 3.79/0.91  fof(f51,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f22])).
% 3.79/0.91  fof(f22,axiom,(
% 3.79/0.91    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.79/0.91  fof(f41,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f21])).
% 3.79/0.91  fof(f21,axiom,(
% 3.79/0.91    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.79/0.91  fof(f36,plain,(
% 3.79/0.91    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f20])).
% 3.79/0.91  fof(f20,axiom,(
% 3.79/0.91    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.79/0.91  fof(f63,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.79/0.91    inference(definition_unfolding,[],[f42,f43])).
% 3.79/0.91  fof(f42,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.79/0.91    inference(cnf_transformation,[],[f16])).
% 3.79/0.91  fof(f16,axiom,(
% 3.79/0.91    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.79/0.91  fof(f61,plain,(
% 3.79/0.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 3.79/0.91    inference(cnf_transformation,[],[f19])).
% 3.79/0.91  fof(f19,axiom,(
% 3.79/0.91    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 3.79/0.91  fof(f184,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.79/0.91    inference(forward_demodulation,[],[f165,f84])).
% 3.79/0.91  fof(f84,plain,(
% 3.79/0.91    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 3.79/0.91    inference(superposition,[],[f38,f35])).
% 3.79/0.91  fof(f35,plain,(
% 3.79/0.91    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.79/0.91    inference(cnf_transformation,[],[f13])).
% 3.79/0.91  fof(f13,axiom,(
% 3.79/0.91    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 3.79/0.91  fof(f38,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f2])).
% 3.79/0.91  fof(f2,axiom,(
% 3.79/0.91    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.79/0.91  fof(f165,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.79/0.91    inference(superposition,[],[f52,f34])).
% 3.79/0.91  fof(f52,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.79/0.91    inference(cnf_transformation,[],[f14])).
% 3.79/0.91  fof(f14,axiom,(
% 3.79/0.91    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.79/0.91  fof(f3945,plain,(
% 3.79/0.91    ~r1_tarski(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3944,f35])).
% 3.79/0.91  fof(f3944,plain,(
% 3.79/0.91    ~r1_tarski(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3943,f39])).
% 3.79/0.91  fof(f3943,plain,(
% 3.79/0.91    ~r1_tarski(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3942,f34])).
% 3.79/0.91  fof(f3942,plain,(
% 3.79/0.91    ~r1_tarski(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3941,f2342])).
% 3.79/0.91  fof(f2342,plain,(
% 3.79/0.91    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12)))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f2301,f52])).
% 3.79/0.91  fof(f2301,plain,(
% 3.79/0.91    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12))) )),
% 3.79/0.91    inference(superposition,[],[f405,f52])).
% 3.79/0.91  fof(f405,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f375,f39])).
% 3.79/0.91  fof(f375,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 3.79/0.91    inference(superposition,[],[f55,f37])).
% 3.79/0.91  fof(f3941,plain,(
% 3.79/0.91    ~r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3940,f38])).
% 3.79/0.91  fof(f3940,plain,(
% 3.79/0.91    ~r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3939,f173])).
% 3.79/0.91  fof(f173,plain,(
% 3.79/0.91    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 3.79/0.91    inference(superposition,[],[f52,f38])).
% 3.79/0.91  fof(f3939,plain,(
% 3.79/0.91    ~r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),k1_xboole_0)),
% 3.79/0.91    inference(forward_demodulation,[],[f3913,f38])).
% 3.79/0.91  fof(f3913,plain,(
% 3.79/0.91    ~r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k1_xboole_0)),
% 3.79/0.91    inference(unit_resulting_resolution,[],[f411,f3573])).
% 3.79/0.91  fof(f3573,plain,(
% 3.79/0.91    ( ! [X39,X40] : (~r1_tarski(k5_xboole_0(X39,X40),k1_xboole_0) | X39 = X40) )),
% 3.79/0.91    inference(superposition,[],[f3270,f209])).
% 3.79/0.91  fof(f209,plain,(
% 3.79/0.91    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7) )),
% 3.79/0.91    inference(superposition,[],[f189,f184])).
% 3.79/0.91  fof(f189,plain,(
% 3.79/0.91    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 3.79/0.91    inference(superposition,[],[f184,f38])).
% 3.79/0.91  fof(f3270,plain,(
% 3.79/0.91    ( ! [X4,X2] : (k5_xboole_0(X2,X4) = X4 | ~r1_tarski(X2,k1_xboole_0)) )),
% 3.79/0.91    inference(global_subsumption,[],[f1333,f3269])).
% 3.79/0.91  fof(f3269,plain,(
% 3.79/0.91    ( ! [X4,X2,X3] : (k5_xboole_0(X2,X4) = X4 | ~r1_tarski(X2,X3) | ~r1_tarski(X2,k1_xboole_0)) )),
% 3.79/0.91    inference(forward_demodulation,[],[f3195,f84])).
% 3.79/0.91  fof(f3195,plain,(
% 3.79/0.91    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X4)) = X4 | ~r1_tarski(X2,X3) | ~r1_tarski(X2,k1_xboole_0)) )),
% 3.79/0.91    inference(superposition,[],[f185,f1661])).
% 3.79/0.91  fof(f1661,plain,(
% 3.79/0.91    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(X8,X7) | ~r1_tarski(X8,k1_xboole_0)) )),
% 3.79/0.91    inference(superposition,[],[f1192,f39])).
% 3.79/0.91  fof(f1192,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k1_xboole_0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.79/0.91    inference(resolution,[],[f960,f455])).
% 3.79/0.91  fof(f455,plain,(
% 3.79/0.91    ( ! [X3] : (r2_xboole_0(k1_xboole_0,X3) | k1_xboole_0 = X3) )),
% 3.79/0.91    inference(resolution,[],[f428,f47])).
% 3.79/0.91  fof(f47,plain,(
% 3.79/0.91    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f3])).
% 3.79/0.91  fof(f3,axiom,(
% 3.79/0.91    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 3.79/0.91  fof(f428,plain,(
% 3.79/0.91    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 3.79/0.91    inference(trivial_inequality_removal,[],[f420])).
% 3.79/0.91  fof(f420,plain,(
% 3.79/0.91    ( ! [X4] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X4)) )),
% 3.79/0.91    inference(backward_demodulation,[],[f95,f419])).
% 3.79/0.91  fof(f419,plain,(
% 3.79/0.91    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) )),
% 3.79/0.91    inference(forward_demodulation,[],[f390,f34])).
% 3.79/0.91  fof(f390,plain,(
% 3.79/0.91    ( ! [X6,X5] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X5,X5),X6)) )),
% 3.79/0.91    inference(superposition,[],[f55,f34])).
% 3.79/0.91  fof(f95,plain,(
% 3.79/0.91    ( ! [X4] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X4) | r1_tarski(k1_xboole_0,X4)) )),
% 3.79/0.91    inference(superposition,[],[f75,f84])).
% 3.79/0.91  fof(f960,plain,(
% 3.79/0.91    ( ! [X6,X7,X5] : (~r2_xboole_0(X6,k3_xboole_0(X7,X5)) | ~r1_tarski(X5,X6)) )),
% 3.79/0.91    inference(superposition,[],[f887,f201])).
% 3.79/0.91  fof(f201,plain,(
% 3.79/0.91    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = X5 | ~r1_tarski(X5,X6)) )),
% 3.79/0.91    inference(forward_demodulation,[],[f191,f35])).
% 3.79/0.91  fof(f191,plain,(
% 3.79/0.91    ( ! [X6,X5] : (k5_xboole_0(X5,k1_xboole_0) = k3_xboole_0(X5,X6) | ~r1_tarski(X5,X6)) )),
% 3.79/0.91    inference(superposition,[],[f184,f76])).
% 3.79/0.91  fof(f76,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f48,f43])).
% 3.79/0.91  fof(f48,plain,(
% 3.79/0.91    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.79/0.91    inference(cnf_transformation,[],[f5])).
% 3.79/0.91  fof(f887,plain,(
% 3.79/0.91    ( ! [X14,X15,X16] : (~r2_xboole_0(X16,k3_xboole_0(X14,k3_xboole_0(X15,X16)))) )),
% 3.79/0.91    inference(superposition,[],[f862,f54])).
% 3.79/0.91  fof(f862,plain,(
% 3.79/0.91    ( ! [X2,X3] : (~r2_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 3.79/0.91    inference(trivial_inequality_removal,[],[f861])).
% 3.79/0.91  fof(f861,plain,(
% 3.79/0.91    ( ! [X2,X3] : (k1_xboole_0 != k1_xboole_0 | ~r2_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 3.79/0.91    inference(backward_demodulation,[],[f726,f857])).
% 3.79/0.91  fof(f857,plain,(
% 3.79/0.91    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f856,f419])).
% 3.79/0.91  fof(f856,plain,(
% 3.79/0.91    ( ! [X2,X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f855,f34])).
% 3.79/0.91  fof(f855,plain,(
% 3.79/0.91    ( ! [X2,X1] : (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k3_xboole_0(k5_xboole_0(X2,X2),X1)) )),
% 3.79/0.91    inference(forward_demodulation,[],[f843,f377])).
% 3.79/0.91  fof(f377,plain,(
% 3.79/0.91    ( ! [X6,X7,X5] : (k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k3_xboole_0(X6,X5),k3_xboole_0(X7,X6))) )),
% 3.79/0.91    inference(superposition,[],[f55,f39])).
% 3.79/0.91  fof(f843,plain,(
% 3.79/0.91    ( ! [X2,X1] : (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))) )),
% 3.79/0.91    inference(superposition,[],[f720,f688])).
% 3.79/0.91  fof(f688,plain,(
% 3.79/0.91    ( ! [X6,X5] : (k3_xboole_0(X6,X5) = k3_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 3.79/0.91    inference(superposition,[],[f248,f39])).
% 3.79/0.91  fof(f720,plain,(
% 3.79/0.91    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X2)))) )),
% 3.79/0.91    inference(backward_demodulation,[],[f83,f715])).
% 3.79/0.91  fof(f726,plain,(
% 3.79/0.91    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X3,k3_xboole_0(X2,k5_xboole_0(X2,X3))) | ~r2_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 3.79/0.91    inference(backward_demodulation,[],[f438,f715])).
% 3.79/0.91  fof(f438,plain,(
% 3.79/0.91    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))) | ~r2_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 3.79/0.91    inference(forward_demodulation,[],[f394,f39])).
% 3.79/0.91  fof(f394,plain,(
% 3.79/0.91    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3) | ~r2_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 3.79/0.91    inference(superposition,[],[f77,f55])).
% 3.79/0.91  fof(f77,plain,(
% 3.79/0.91    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X1,X0)) | ~r2_xboole_0(X0,X1)) )),
% 3.79/0.91    inference(definition_unfolding,[],[f50,f43])).
% 3.79/0.91  fof(f50,plain,(
% 3.79/0.91    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X1,X0)) )),
% 3.79/0.91    inference(cnf_transformation,[],[f32])).
% 3.79/0.91  fof(f32,plain,(
% 3.79/0.91    ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 3.79/0.91    inference(ennf_transformation,[],[f7])).
% 3.79/0.91  fof(f7,axiom,(
% 3.79/0.91    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).
% 3.79/0.91  fof(f185,plain,(
% 3.79/0.91    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = X10 | ~r1_tarski(X8,X9)) )),
% 3.79/0.91    inference(forward_demodulation,[],[f168,f84])).
% 3.79/0.91  fof(f168,plain,(
% 3.79/0.91    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k1_xboole_0,X10) | ~r1_tarski(X8,X9)) )),
% 3.79/0.91    inference(superposition,[],[f52,f76])).
% 3.79/0.91  fof(f1333,plain,(
% 3.79/0.91    ( ! [X30,X29] : (~r1_tarski(X30,k1_xboole_0) | r1_tarski(X30,X29)) )),
% 3.79/0.91    inference(superposition,[],[f1037,f419])).
% 3.79/0.91  fof(f1037,plain,(
% 3.79/0.91    ( ! [X10,X11,X9] : (~r1_tarski(X9,k3_xboole_0(X10,X11)) | r1_tarski(X9,X11)) )),
% 3.79/0.91    inference(superposition,[],[f906,f201])).
% 3.79/0.91  fof(f906,plain,(
% 3.79/0.91    ( ! [X14,X15,X16] : (r1_tarski(k3_xboole_0(X14,k3_xboole_0(X15,X16)),X16)) )),
% 3.79/0.91    inference(superposition,[],[f863,f54])).
% 3.79/0.91  fof(f863,plain,(
% 3.79/0.91    ( ! [X6,X7] : (r1_tarski(k3_xboole_0(X6,X7),X7)) )),
% 3.79/0.91    inference(trivial_inequality_removal,[],[f860])).
% 3.79/0.91  fof(f860,plain,(
% 3.79/0.91    ( ! [X6,X7] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k3_xboole_0(X6,X7),X7)) )),
% 3.79/0.91    inference(backward_demodulation,[],[f727,f857])).
% 3.79/0.91  fof(f727,plain,(
% 3.79/0.91    ( ! [X6,X7] : (k1_xboole_0 != k3_xboole_0(X7,k3_xboole_0(X6,k5_xboole_0(X6,X7))) | r1_tarski(k3_xboole_0(X6,X7),X7)) )),
% 3.79/0.91    inference(backward_demodulation,[],[f440,f715])).
% 3.79/0.91  fof(f440,plain,(
% 3.79/0.91    ( ! [X6,X7] : (k1_xboole_0 != k3_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X6,X7))) | r1_tarski(k3_xboole_0(X6,X7),X7)) )),
% 3.79/0.91    inference(forward_demodulation,[],[f396,f39])).
% 3.79/0.91  fof(f396,plain,(
% 3.79/0.91    ( ! [X6,X7] : (k1_xboole_0 != k3_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X7) | r1_tarski(k3_xboole_0(X6,X7),X7)) )),
% 3.79/0.91    inference(superposition,[],[f75,f55])).
% 3.79/0.91  fof(f411,plain,(
% 3.79/0.91    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 3.79/0.91    inference(forward_demodulation,[],[f410,f38])).
% 3.79/0.91  fof(f410,plain,(
% 3.79/0.91    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 3.79/0.91    inference(backward_demodulation,[],[f81,f405])).
% 3.79/0.91  fof(f81,plain,(
% 3.79/0.91    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 3.79/0.91    inference(backward_demodulation,[],[f72,f39])).
% 3.79/0.91  fof(f72,plain,(
% 3.79/0.91    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 3.79/0.91    inference(definition_unfolding,[],[f33,f68,f63,f69,f68])).
% 3.79/0.91  fof(f33,plain,(
% 3.79/0.91    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 3.79/0.91    inference(cnf_transformation,[],[f30])).
% 3.79/0.91  fof(f30,plain,(
% 3.79/0.91    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.79/0.91    inference(ennf_transformation,[],[f28])).
% 3.79/0.91  fof(f28,negated_conjecture,(
% 3.79/0.91    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.79/0.91    inference(negated_conjecture,[],[f27])).
% 3.79/0.91  fof(f27,conjecture,(
% 3.79/0.91    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.79/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 3.79/0.91  % SZS output end Proof for theBenchmark
% 3.79/0.91  % (27885)------------------------------
% 3.79/0.91  % (27885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.79/0.91  % (27885)Termination reason: Refutation
% 3.79/0.91  
% 3.79/0.91  % (27885)Memory used [KB]: 9978
% 3.79/0.91  % (27885)Time elapsed: 0.510 s
% 3.79/0.91  % (27885)------------------------------
% 3.79/0.91  % (27885)------------------------------
% 3.79/0.91  % (27856)Success in time 0.563 s
%------------------------------------------------------------------------------
