%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:26 EST 2020

% Result     : Theorem 37.44s
% Output     : Refutation 37.44s
% Verified   : 
% Statistics : Number of formulae       :  164 (222852 expanded)
%              Number of leaves         :   13 (75980 expanded)
%              Depth                    :   38
%              Number of atoms          :  172 (222870 expanded)
%              Number of equality atoms :  171 (222869 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61503,plain,(
    $false ),
    inference(subsumption_resolution,[],[f61502,f22839])).

fof(f22839,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12)) ),
    inference(forward_demodulation,[],[f22712,f132])).

fof(f132,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f88,f124])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f111])).

fof(f111,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f32,f88])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f88,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f34,f73])).

fof(f73,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f67,f32])).

fof(f67,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f64,f32])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f29,f58])).

fof(f58,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f50,f55])).

fof(f55,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f36,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f32,f36])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f26,f26])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f22712,plain,(
    ! [X12,X13] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X12,X13))) = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12)) ),
    inference(superposition,[],[f34,f22450])).

fof(f22450,plain,(
    ! [X149,X150] : k5_xboole_0(X150,X149) = k4_xboole_0(k5_xboole_0(X149,X150),k1_xboole_0) ),
    inference(forward_demodulation,[],[f22449,f233])).

fof(f233,plain,(
    ! [X9] : k5_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(forward_demodulation,[],[f216,f124])).

fof(f216,plain,(
    ! [X9] : k5_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X9,k1_xboole_0))) = X9 ),
    inference(superposition,[],[f41,f132])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f26,f26])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f23,f26])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f22449,plain,(
    ! [X149,X150] : k4_xboole_0(k5_xboole_0(X149,X150),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X150,X149),k1_xboole_0) ),
    inference(forward_demodulation,[],[f22273,f132])).

fof(f22273,plain,(
    ! [X149,X150] : k4_xboole_0(k5_xboole_0(X149,X150),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X150,X149),k4_xboole_0(k1_xboole_0,k5_xboole_0(X149,X150))) ),
    inference(superposition,[],[f21120,f2459])).

fof(f2459,plain,(
    ! [X50,X51] : k5_xboole_0(X51,X50) = k5_xboole_0(k5_xboole_0(X50,X51),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2416,f405])).

fof(f405,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(forward_demodulation,[],[f391,f236])).

fof(f236,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f124,f234])).

fof(f234,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(backward_demodulation,[],[f136,f233])).

fof(f136,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f111,f132])).

fof(f391,plain,(
    ! [X7] : k5_xboole_0(k4_xboole_0(X7,X7),X7) = X7 ),
    inference(superposition,[],[f247,f222])).

fof(f222,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5 ),
    inference(superposition,[],[f41,f32])).

fof(f247,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f38,f222])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f27,f23,f26])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f2416,plain,(
    ! [X50,X51] : k5_xboole_0(k5_xboole_0(X50,X51),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X51,X50)) ),
    inference(superposition,[],[f2273,f2273])).

fof(f2273,plain,(
    ! [X0,X1] : k5_xboole_0(X1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f1423,f235])).

fof(f235,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f50,f234])).

fof(f1423,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24)) ),
    inference(superposition,[],[f424,f463])).

fof(f463,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f451,f233])).

fof(f451,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f406,f240])).

fof(f240,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f146,f234])).

fof(f146,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f54,f144])).

fof(f144,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f141,f136])).

fof(f141,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f122,f132])).

fof(f122,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f111,f29])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) ),
    inference(superposition,[],[f50,f29])).

fof(f406,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f241,f405])).

fof(f241,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f149,f238])).

fof(f238,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f148,f234])).

fof(f148,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2) = k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f126,f132])).

fof(f126,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2) ),
    inference(superposition,[],[f29,f111])).

fof(f149,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) ),
    inference(backward_demodulation,[],[f56,f148])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f29,f50])).

fof(f424,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) = X10 ),
    inference(superposition,[],[f406,f29])).

fof(f21120,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f424,f20225])).

fof(f20225,plain,(
    ! [X24,X25] : k4_xboole_0(X25,X24) = k5_xboole_0(X24,k5_xboole_0(X25,k4_xboole_0(X24,X25))) ),
    inference(forward_demodulation,[],[f19963,f481])).

fof(f481,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f406,f463])).

fof(f19963,plain,(
    ! [X24,X25] : k4_xboole_0(X25,X24) = k5_xboole_0(X24,k5_xboole_0(k4_xboole_0(X24,X25),X25)) ),
    inference(superposition,[],[f406,f19734])).

fof(f19734,plain,(
    ! [X10,X11] : k5_xboole_0(X10,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X11) ),
    inference(forward_demodulation,[],[f19485,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f19485,plain,(
    ! [X10,X11] : k5_xboole_0(X10,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))),X11) ),
    inference(superposition,[],[f398,f382])).

fof(f382,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f247,f34])).

fof(f398,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[],[f29,f247])).

fof(f61502,plain,(
    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f61501,f22839])).

fof(f61501,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) != k4_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f815,f61500])).

fof(f61500,plain,(
    ! [X229,X228] : k5_xboole_0(X228,X229) = k4_xboole_0(k5_xboole_0(X229,k4_xboole_0(X228,X229)),k4_xboole_0(X229,k4_xboole_0(X229,X228))) ),
    inference(forward_demodulation,[],[f61153,f61392])).

fof(f61392,plain,(
    ! [X37,X36] : k4_xboole_0(X37,k4_xboole_0(X37,X36)) = k4_xboole_0(X37,k5_xboole_0(X36,X37)) ),
    inference(forward_demodulation,[],[f61391,f179])).

fof(f179,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f32,f37])).

fof(f61391,plain,(
    ! [X37,X36] : k5_xboole_0(X37,k4_xboole_0(X37,X36)) = k4_xboole_0(X37,k5_xboole_0(X36,X37)) ),
    inference(forward_demodulation,[],[f61079,f54201])).

fof(f54201,plain,(
    ! [X218,X219] : k4_xboole_0(X219,X218) = k4_xboole_0(k5_xboole_0(X218,X219),k4_xboole_0(X218,X219)) ),
    inference(forward_demodulation,[],[f54198,f405])).

fof(f54198,plain,(
    ! [X218,X219] : k4_xboole_0(k5_xboole_0(X218,X219),k4_xboole_0(X218,X219)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X219,X218)) ),
    inference(backward_demodulation,[],[f26925,f54030])).

fof(f54030,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f2794,f19699])).

fof(f19699,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(forward_demodulation,[],[f19483,f37])).

fof(f19483,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))),k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f398,f863])).

fof(f863,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X15) ),
    inference(superposition,[],[f473,f184])).

fof(f184,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f91,f175])).

fof(f175,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f37,f34])).

fof(f91,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f32,f34])).

fof(f473,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    inference(superposition,[],[f463,f463])).

fof(f2794,plain,(
    ! [X35,X36,X34] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35))) ),
    inference(superposition,[],[f36,f2168])).

fof(f2168,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16)) ),
    inference(superposition,[],[f2105,f222])).

fof(f2105,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21 ),
    inference(forward_demodulation,[],[f2028,f234])).

fof(f2028,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21 ),
    inference(superposition,[],[f1868,f346])).

fof(f346,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f319,f175])).

fof(f319,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X1) ),
    inference(superposition,[],[f251,f34])).

fof(f251,plain,(
    ! [X17,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),X16) ),
    inference(backward_demodulation,[],[f181,f247])).

fof(f181,plain,(
    ! [X17,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k5_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17))) ),
    inference(superposition,[],[f36,f37])).

fof(f1868,plain,(
    ! [X50,X48,X49] : k4_xboole_0(X50,k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50)))) = X50 ),
    inference(superposition,[],[f222,f39])).

fof(f26925,plain,(
    ! [X218,X219] : k4_xboole_0(k5_xboole_0(X218,X219),k4_xboole_0(X218,X219)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X218,X219),k5_xboole_0(X218,X219)),k4_xboole_0(X219,X218)) ),
    inference(superposition,[],[f21124,f21126])).

fof(f21126,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15)) ),
    inference(superposition,[],[f1395,f20225])).

fof(f1395,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = X4 ),
    inference(superposition,[],[f424,f481])).

fof(f21124,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10)) ),
    inference(superposition,[],[f517,f20225])).

fof(f517,plain,(
    ! [X12,X10,X11] : k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(X11,X12)),k5_xboole_0(X10,X11)) = X12 ),
    inference(superposition,[],[f473,f29])).

fof(f61079,plain,(
    ! [X37,X36] : k4_xboole_0(X37,k5_xboole_0(X36,X37)) = k5_xboole_0(X37,k4_xboole_0(k5_xboole_0(X36,X37),k4_xboole_0(X36,X37))) ),
    inference(superposition,[],[f90,f60714])).

fof(f60714,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f60713,f234])).

fof(f60713,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(backward_demodulation,[],[f60375,f60431])).

fof(f60431,plain,(
    ! [X123,X124] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X123,X124),k4_xboole_0(k5_xboole_0(X123,X124),X124)) ),
    inference(superposition,[],[f58050,f472])).

fof(f472,plain,(
    ! [X4,X3] : k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3 ),
    inference(superposition,[],[f463,f406])).

fof(f58050,plain,(
    ! [X21,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X20,X21),X21),k4_xboole_0(X20,X21)) ),
    inference(superposition,[],[f48292,f54193])).

fof(f54193,plain,(
    ! [X121,X120] : k4_xboole_0(X120,X121) = k4_xboole_0(k5_xboole_0(X120,X121),k4_xboole_0(X121,X120)) ),
    inference(forward_demodulation,[],[f54190,f405])).

fof(f54190,plain,(
    ! [X121,X120] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X120,X121)) = k4_xboole_0(k5_xboole_0(X120,X121),k4_xboole_0(X121,X120)) ),
    inference(backward_demodulation,[],[f26317,f54029])).

fof(f54029,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3)) ),
    inference(superposition,[],[f2794,f21123])).

fof(f21123,plain,(
    ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f500,f20225])).

fof(f500,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(X11,X12)),X12) ),
    inference(superposition,[],[f472,f29])).

fof(f26317,plain,(
    ! [X121,X120] : k4_xboole_0(k5_xboole_0(X120,X121),k4_xboole_0(X121,X120)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X121,X120),k5_xboole_0(X120,X121)),k4_xboole_0(X120,X121)) ),
    inference(superposition,[],[f21124,f21120])).

fof(f48292,plain,(
    ! [X19,X17,X18] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,k4_xboole_0(X18,X19))) ),
    inference(superposition,[],[f48054,f2168])).

fof(f48054,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f48053,f463])).

fof(f48053,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,X3)),X4)) ),
    inference(forward_demodulation,[],[f48052,f19699])).

fof(f48052,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4)) ),
    inference(forward_demodulation,[],[f47869,f1676])).

fof(f1676,plain,(
    ! [X45,X46,X44] : k5_xboole_0(X46,k4_xboole_0(X44,k4_xboole_0(X44,X45))) = k5_xboole_0(X44,k5_xboole_0(X46,k4_xboole_0(X44,X45))) ),
    inference(superposition,[],[f476,f423])).

fof(f423,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X6) ),
    inference(superposition,[],[f406,f247])).

fof(f476,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12))) ),
    inference(superposition,[],[f463,f29])).

fof(f47869,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) ),
    inference(superposition,[],[f24444,f34])).

fof(f24444,plain,(
    ! [X45,X46,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X46),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),X46)) ),
    inference(superposition,[],[f328,f1913])).

fof(f1913,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22) ),
    inference(forward_demodulation,[],[f1816,f234])).

fof(f1816,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22) ),
    inference(superposition,[],[f39,f36])).

fof(f328,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f251,f34])).

fof(f60375,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X1))) ),
    inference(unit_resulting_resolution,[],[f58050,f17646])).

fof(f17646,plain,(
    ! [X14,X13] :
      ( k1_xboole_0 != k4_xboole_0(X13,X14)
      | k4_xboole_0(X14,k4_xboole_0(X14,X13)) = X13 ) ),
    inference(forward_demodulation,[],[f17581,f382])).

fof(f17581,plain,(
    ! [X14,X13] :
      ( k1_xboole_0 != k4_xboole_0(X13,X14)
      | k4_xboole_0(X14,k4_xboole_0(X14,X13)) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),k4_xboole_0(X13,X14)) ) ),
    inference(superposition,[],[f1312,f175])).

fof(f1312,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f1267,f36])).

fof(f1267,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ) ),
    inference(superposition,[],[f28,f689])).

fof(f689,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9) ),
    inference(forward_demodulation,[],[f688,f473])).

fof(f688,plain,(
    ! [X10,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9) ),
    inference(forward_demodulation,[],[f658,f234])).

fof(f658,plain,(
    ! [X10,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k1_xboole_0)) ),
    inference(superposition,[],[f90,f36])).

fof(f28,plain,(
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

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f32,f34])).

fof(f61153,plain,(
    ! [X229,X228] : k5_xboole_0(X228,X229) = k4_xboole_0(k5_xboole_0(X229,k4_xboole_0(X228,X229)),k4_xboole_0(X229,k5_xboole_0(X228,X229))) ),
    inference(superposition,[],[f20221,f60714])).

fof(f20221,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f19959,f481])).

fof(f19959,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X8,X9),X9),k4_xboole_0(X9,X8)) = X8 ),
    inference(superposition,[],[f1231,f19734])).

fof(f1231,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15)) = X15 ),
    inference(forward_demodulation,[],[f1230,f472])).

fof(f1230,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15)) = k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f1202,f234])).

fof(f1202,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15)) = k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(k4_xboole_0(X14,X15),k1_xboole_0)) ),
    inference(superposition,[],[f90,f490])).

fof(f490,plain,(
    ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X14,k4_xboole_0(X15,X14))) ),
    inference(backward_demodulation,[],[f298,f481])).

fof(f298,plain,(
    ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(k4_xboole_0(X15,X14),X14)) ),
    inference(superposition,[],[f36,f222])).

fof(f815,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f28])).

fof(f33,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f23,f26])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:44:55 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.51  % (3665)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (3674)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (3657)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (3657)Refutation not found, incomplete strategy% (3657)------------------------------
% 0.21/0.52  % (3657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3657)Memory used [KB]: 10618
% 0.21/0.52  % (3657)Time elapsed: 0.111 s
% 0.21/0.52  % (3657)------------------------------
% 0.21/0.52  % (3657)------------------------------
% 0.21/0.52  % (3669)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (3670)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3655)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (3659)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (3662)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3660)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (3661)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (3681)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (3655)Refutation not found, incomplete strategy% (3655)------------------------------
% 0.21/0.54  % (3655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3655)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3655)Memory used [KB]: 1663
% 0.21/0.54  % (3655)Time elapsed: 0.134 s
% 0.21/0.54  % (3655)------------------------------
% 0.21/0.54  % (3655)------------------------------
% 0.21/0.54  % (3668)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (3656)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (3684)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.54  % (3682)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.54  % (3673)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.54  % (3679)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.55  % (3676)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (3675)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (3663)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.55  % (3667)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (3664)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.55  % (3679)Refutation not found, incomplete strategy% (3679)------------------------------
% 1.43/0.55  % (3679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (3679)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (3679)Memory used [KB]: 1663
% 1.43/0.55  % (3679)Time elapsed: 0.106 s
% 1.43/0.55  % (3679)------------------------------
% 1.43/0.55  % (3679)------------------------------
% 1.43/0.55  % (3680)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (3678)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.55  % (3672)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.56  % (3678)Refutation not found, incomplete strategy% (3678)------------------------------
% 1.43/0.56  % (3678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (3678)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (3678)Memory used [KB]: 10618
% 1.43/0.56  % (3678)Time elapsed: 0.145 s
% 1.43/0.56  % (3678)------------------------------
% 1.43/0.56  % (3678)------------------------------
% 1.43/0.56  % (3663)Refutation not found, incomplete strategy% (3663)------------------------------
% 1.43/0.56  % (3663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (3685)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.56  % (3676)Refutation not found, incomplete strategy% (3676)------------------------------
% 1.51/0.56  % (3676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (3673)Refutation not found, incomplete strategy% (3673)------------------------------
% 1.51/0.56  % (3673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (3658)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.56  % (3677)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.56  % (3677)Refutation not found, incomplete strategy% (3677)------------------------------
% 1.51/0.56  % (3677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (3677)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (3677)Memory used [KB]: 1663
% 1.51/0.56  % (3677)Time elapsed: 0.158 s
% 1.51/0.56  % (3677)------------------------------
% 1.51/0.56  % (3677)------------------------------
% 1.51/0.56  % (3663)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (3663)Memory used [KB]: 10618
% 1.51/0.56  % (3663)Time elapsed: 0.158 s
% 1.51/0.56  % (3663)------------------------------
% 1.51/0.56  % (3663)------------------------------
% 1.51/0.57  % (3673)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (3673)Memory used [KB]: 10618
% 1.51/0.57  % (3673)Time elapsed: 0.158 s
% 1.51/0.57  % (3673)------------------------------
% 1.51/0.57  % (3673)------------------------------
% 1.51/0.57  % (3676)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (3676)Memory used [KB]: 10618
% 1.51/0.57  % (3676)Time elapsed: 0.159 s
% 1.51/0.57  % (3676)------------------------------
% 1.51/0.57  % (3676)------------------------------
% 1.51/0.58  % (3683)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.59  % (3666)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.25/0.68  % (3689)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.25/0.69  % (3690)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.25/0.71  % (3689)Refutation not found, incomplete strategy% (3689)------------------------------
% 2.25/0.71  % (3689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.71  % (3689)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.71  
% 2.25/0.71  % (3689)Memory used [KB]: 6140
% 2.25/0.71  % (3689)Time elapsed: 0.143 s
% 2.25/0.71  % (3689)------------------------------
% 2.25/0.71  % (3689)------------------------------
% 2.25/0.71  % (3692)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.25/0.72  % (3703)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.25/0.72  % (3691)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.25/0.72  % (3695)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.25/0.72  % (3693)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.67/0.74  % (3702)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.83/0.81  % (3660)Time limit reached!
% 2.83/0.81  % (3660)------------------------------
% 2.83/0.81  % (3660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.81  % (3660)Termination reason: Time limit
% 2.83/0.81  % (3660)Termination phase: Saturation
% 2.83/0.81  
% 2.83/0.81  % (3660)Memory used [KB]: 8955
% 2.83/0.81  % (3660)Time elapsed: 0.400 s
% 2.83/0.81  % (3660)------------------------------
% 2.83/0.81  % (3660)------------------------------
% 3.17/0.85  % (3728)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.34/0.91  % (3667)Time limit reached!
% 3.34/0.91  % (3667)------------------------------
% 3.34/0.91  % (3667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.91  % (3667)Termination reason: Time limit
% 3.34/0.91  
% 3.34/0.91  % (3667)Memory used [KB]: 9210
% 3.34/0.91  % (3667)Time elapsed: 0.508 s
% 3.34/0.91  % (3667)------------------------------
% 3.34/0.91  % (3667)------------------------------
% 3.70/0.93  % (3730)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.70/0.94  % (3656)Time limit reached!
% 3.70/0.94  % (3656)------------------------------
% 3.70/0.94  % (3656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.94  % (3656)Termination reason: Time limit
% 3.70/0.94  
% 3.70/0.94  % (3656)Memory used [KB]: 8955
% 3.70/0.94  % (3656)Time elapsed: 0.506 s
% 3.70/0.94  % (3656)------------------------------
% 3.70/0.94  % (3656)------------------------------
% 3.90/0.98  % (3692)Time limit reached!
% 3.90/0.98  % (3692)------------------------------
% 3.90/0.98  % (3692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.90/0.98  % (3692)Termination reason: Time limit
% 3.90/0.98  % (3692)Termination phase: Saturation
% 3.90/0.98  
% 3.90/0.98  % (3692)Memory used [KB]: 7931
% 3.90/0.98  % (3692)Time elapsed: 0.400 s
% 3.90/0.98  % (3692)------------------------------
% 3.90/0.98  % (3692)------------------------------
% 3.90/1.00  % (3693)Time limit reached!
% 3.90/1.00  % (3693)------------------------------
% 3.90/1.00  % (3693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.90/1.02  % (3693)Termination reason: Time limit
% 3.90/1.02  % (3693)Termination phase: Saturation
% 3.90/1.02  
% 3.90/1.02  % (3693)Memory used [KB]: 14072
% 3.90/1.02  % (3693)Time elapsed: 0.400 s
% 3.90/1.02  % (3693)------------------------------
% 3.90/1.02  % (3693)------------------------------
% 3.90/1.02  % (3684)Time limit reached!
% 3.90/1.02  % (3684)------------------------------
% 3.90/1.02  % (3684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.90/1.02  % (3684)Termination reason: Time limit
% 3.90/1.02  
% 3.90/1.02  % (3684)Memory used [KB]: 9083
% 3.90/1.02  % (3684)Time elapsed: 0.618 s
% 3.90/1.02  % (3684)------------------------------
% 3.90/1.02  % (3684)------------------------------
% 3.90/1.02  % (3672)Time limit reached!
% 3.90/1.02  % (3672)------------------------------
% 3.90/1.02  % (3672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.90/1.02  % (3672)Termination reason: Time limit
% 3.90/1.02  % (3672)Termination phase: Saturation
% 3.90/1.02  
% 3.90/1.02  % (3672)Memory used [KB]: 16119
% 3.90/1.02  % (3672)Time elapsed: 0.600 s
% 3.90/1.02  % (3672)------------------------------
% 3.90/1.02  % (3672)------------------------------
% 4.54/1.04  % (3662)Time limit reached!
% 4.54/1.04  % (3662)------------------------------
% 4.54/1.04  % (3662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.04  % (3662)Termination reason: Time limit
% 4.54/1.04  
% 4.54/1.04  % (3662)Memory used [KB]: 12025
% 4.54/1.04  % (3662)Time elapsed: 0.605 s
% 4.54/1.04  % (3662)------------------------------
% 4.54/1.04  % (3662)------------------------------
% 4.54/1.04  % (3731)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.54/1.04  % (3731)Refutation not found, incomplete strategy% (3731)------------------------------
% 4.54/1.04  % (3731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.04  % (3731)Termination reason: Refutation not found, incomplete strategy
% 4.54/1.04  
% 4.54/1.04  % (3731)Memory used [KB]: 6140
% 4.54/1.04  % (3731)Time elapsed: 0.112 s
% 4.54/1.04  % (3731)------------------------------
% 4.54/1.04  % (3731)------------------------------
% 4.54/1.07  % (3732)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.54/1.08  % (3732)Refutation not found, incomplete strategy% (3732)------------------------------
% 4.54/1.08  % (3732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.08  % (3732)Termination reason: Refutation not found, incomplete strategy
% 4.54/1.08  
% 4.54/1.08  % (3732)Memory used [KB]: 1663
% 4.54/1.08  % (3732)Time elapsed: 0.109 s
% 4.54/1.08  % (3732)------------------------------
% 4.54/1.08  % (3732)------------------------------
% 5.63/1.10  % (3733)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.63/1.11  % (3665)Time limit reached!
% 5.63/1.11  % (3665)------------------------------
% 5.63/1.11  % (3665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.13  % (3734)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.63/1.13  % (3665)Termination reason: Time limit
% 5.63/1.13  
% 5.63/1.13  % (3665)Memory used [KB]: 66395
% 5.63/1.13  % (3665)Time elapsed: 0.661 s
% 5.63/1.13  % (3665)------------------------------
% 5.63/1.13  % (3665)------------------------------
% 5.63/1.13  % (3734)Refutation not found, incomplete strategy% (3734)------------------------------
% 5.63/1.13  % (3734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.13  % (3734)Termination reason: Refutation not found, incomplete strategy
% 5.63/1.13  
% 5.63/1.13  % (3734)Memory used [KB]: 1663
% 5.63/1.13  % (3734)Time elapsed: 0.072 s
% 5.63/1.13  % (3734)------------------------------
% 5.63/1.13  % (3734)------------------------------
% 6.12/1.15  % (3736)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.12/1.16  % (3735)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.12/1.16  % (3736)Refutation not found, incomplete strategy% (3736)------------------------------
% 6.12/1.16  % (3736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.12/1.16  % (3736)Termination reason: Refutation not found, incomplete strategy
% 6.12/1.16  
% 6.12/1.16  % (3736)Memory used [KB]: 6140
% 6.12/1.16  % (3736)Time elapsed: 0.123 s
% 6.12/1.16  % (3736)------------------------------
% 6.12/1.16  % (3736)------------------------------
% 6.36/1.17  % (3737)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.36/1.17  % (3738)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.36/1.21  % (3739)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.96/1.27  % (3741)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 6.96/1.27  % (3740)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.96/1.28  % (3752)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.41/1.48  % (3737)Time limit reached!
% 8.41/1.48  % (3737)------------------------------
% 8.41/1.48  % (3737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.41/1.48  % (3737)Termination reason: Time limit
% 8.41/1.48  % (3737)Termination phase: Saturation
% 8.41/1.48  
% 8.41/1.48  % (3737)Memory used [KB]: 3837
% 8.41/1.48  % (3737)Time elapsed: 0.400 s
% 8.41/1.48  % (3737)------------------------------
% 8.41/1.48  % (3737)------------------------------
% 8.41/1.52  % (3733)Time limit reached!
% 8.41/1.52  % (3733)------------------------------
% 8.41/1.52  % (3733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.41/1.52  % (3733)Termination reason: Time limit
% 8.41/1.52  
% 8.41/1.52  % (3733)Memory used [KB]: 6524
% 8.41/1.52  % (3733)Time elapsed: 0.505 s
% 8.41/1.52  % (3733)------------------------------
% 8.41/1.52  % (3733)------------------------------
% 9.01/1.56  % (3740)Time limit reached!
% 9.01/1.56  % (3740)------------------------------
% 9.01/1.56  % (3740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.01/1.58  % (3740)Termination reason: Time limit
% 9.01/1.58  % (3740)Termination phase: Saturation
% 9.01/1.58  
% 9.01/1.58  % (3740)Memory used [KB]: 3582
% 9.01/1.58  % (3740)Time elapsed: 0.400 s
% 9.01/1.58  % (3740)------------------------------
% 9.01/1.58  % (3740)------------------------------
% 9.01/1.61  % (3897)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.01/1.64  % (3911)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.36/1.69  % (3924)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.10/1.80  % (3702)Time limit reached!
% 11.10/1.80  % (3702)------------------------------
% 11.10/1.80  % (3702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.10/1.80  % (3702)Termination reason: Time limit
% 11.10/1.80  
% 11.10/1.80  % (3702)Memory used [KB]: 14328
% 11.10/1.80  % (3702)Time elapsed: 1.202 s
% 11.10/1.80  % (3702)------------------------------
% 11.10/1.80  % (3702)------------------------------
% 11.70/1.88  % (3680)Time limit reached!
% 11.70/1.88  % (3680)------------------------------
% 11.70/1.88  % (3680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.70/1.89  % (3680)Termination reason: Time limit
% 11.70/1.89  % (3680)Termination phase: Saturation
% 11.70/1.89  
% 11.70/1.89  % (3680)Memory used [KB]: 23666
% 11.70/1.89  % (3680)Time elapsed: 1.300 s
% 11.70/1.89  % (3680)------------------------------
% 11.70/1.89  % (3680)------------------------------
% 12.34/1.94  % (3973)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 12.34/1.94  % (3973)Refutation not found, incomplete strategy% (3973)------------------------------
% 12.34/1.94  % (3973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.34/1.94  % (3973)Termination reason: Refutation not found, incomplete strategy
% 12.34/1.94  
% 12.34/1.94  % (3973)Memory used [KB]: 6140
% 12.34/1.94  % (3973)Time elapsed: 0.108 s
% 12.34/1.94  % (3973)------------------------------
% 12.34/1.94  % (3973)------------------------------
% 12.34/1.95  % (3683)Time limit reached!
% 12.34/1.95  % (3683)------------------------------
% 12.34/1.95  % (3683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.34/1.95  % (3683)Termination reason: Time limit
% 12.34/1.95  
% 12.34/1.95  % (3683)Memory used [KB]: 17782
% 12.34/1.95  % (3683)Time elapsed: 1.518 s
% 12.34/1.95  % (3683)------------------------------
% 12.34/1.95  % (3683)------------------------------
% 12.76/2.00  % (3974)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.76/2.02  % (3682)Time limit reached!
% 12.76/2.02  % (3682)------------------------------
% 12.76/2.02  % (3682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/2.02  % (3682)Termination reason: Time limit
% 12.76/2.02  
% 12.76/2.02  % (3682)Memory used [KB]: 139059
% 12.76/2.02  % (3682)Time elapsed: 1.532 s
% 12.76/2.02  % (3682)------------------------------
% 12.76/2.02  % (3682)------------------------------
% 12.76/2.03  % (3666)Time limit reached!
% 12.76/2.03  % (3666)------------------------------
% 12.76/2.03  % (3666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/2.03  % (3666)Termination reason: Time limit
% 12.76/2.03  % (3666)Termination phase: Saturation
% 12.76/2.03  
% 12.76/2.03  % (3666)Memory used [KB]: 27760
% 12.76/2.03  % (3666)Time elapsed: 1.600 s
% 12.76/2.03  % (3666)------------------------------
% 12.76/2.03  % (3666)------------------------------
% 13.29/2.07  % (3975)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 13.47/2.08  % (3659)Time limit reached!
% 13.47/2.08  % (3659)------------------------------
% 13.47/2.08  % (3659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.47/2.09  % (3975)Refutation not found, incomplete strategy% (3975)------------------------------
% 13.47/2.09  % (3975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.47/2.09  % (3975)Termination reason: Refutation not found, incomplete strategy
% 13.47/2.09  
% 13.47/2.09  % (3975)Memory used [KB]: 10618
% 13.47/2.09  % (3975)Time elapsed: 0.116 s
% 13.47/2.09  % (3975)------------------------------
% 13.47/2.09  % (3975)------------------------------
% 13.47/2.09  % (3659)Termination reason: Time limit
% 13.47/2.09  % (3659)Termination phase: Saturation
% 13.47/2.09  
% 13.47/2.09  % (3659)Memory used [KB]: 187161
% 13.47/2.09  % (3659)Time elapsed: 1.500 s
% 13.47/2.09  % (3659)------------------------------
% 13.47/2.09  % (3659)------------------------------
% 13.47/2.11  % (3670)Time limit reached!
% 13.47/2.11  % (3670)------------------------------
% 13.47/2.11  % (3670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.47/2.11  % (3670)Termination reason: Time limit
% 13.47/2.11  % (3670)Termination phase: Saturation
% 13.47/2.11  
% 13.47/2.11  % (3670)Memory used [KB]: 189975
% 13.47/2.11  % (3670)Time elapsed: 1.300 s
% 13.47/2.11  % (3670)------------------------------
% 13.47/2.11  % (3670)------------------------------
% 13.85/2.13  % (3924)Time limit reached!
% 13.85/2.13  % (3924)------------------------------
% 13.85/2.13  % (3924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.85/2.13  % (3924)Termination reason: Time limit
% 13.85/2.13  % (3924)Termination phase: Saturation
% 13.85/2.13  
% 13.85/2.13  % (3924)Memory used [KB]: 14328
% 13.85/2.13  % (3924)Time elapsed: 0.400 s
% 13.85/2.13  % (3924)------------------------------
% 13.85/2.13  % (3924)------------------------------
% 14.91/2.26  % (3669)Time limit reached!
% 14.91/2.26  % (3669)------------------------------
% 14.91/2.26  % (3669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.91/2.27  % (3669)Termination reason: Time limit
% 14.91/2.27  
% 14.91/2.27  % (3669)Memory used [KB]: 22131
% 14.91/2.27  % (3669)Time elapsed: 1.857 s
% 14.91/2.27  % (3669)------------------------------
% 14.91/2.27  % (3669)------------------------------
% 15.33/2.31  % (3691)Time limit reached!
% 15.33/2.31  % (3691)------------------------------
% 15.33/2.31  % (3691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.33/2.32  % (3691)Termination reason: Time limit
% 15.33/2.32  % (3691)Termination phase: Saturation
% 15.33/2.32  
% 15.33/2.32  % (3691)Memory used [KB]: 26225
% 15.33/2.32  % (3691)Time elapsed: 1.700 s
% 15.33/2.32  % (3691)------------------------------
% 15.33/2.32  % (3691)------------------------------
% 15.93/2.39  % (3974)Time limit reached!
% 15.93/2.39  % (3974)------------------------------
% 15.93/2.39  % (3974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.93/2.40  % (3974)Termination reason: Time limit
% 15.93/2.40  % (3974)Termination phase: Saturation
% 15.93/2.40  
% 15.93/2.40  % (3974)Memory used [KB]: 58591
% 15.93/2.40  % (3974)Time elapsed: 0.400 s
% 15.93/2.40  % (3974)------------------------------
% 15.93/2.40  % (3974)------------------------------
% 16.29/2.42  % (3661)Time limit reached!
% 16.29/2.42  % (3661)------------------------------
% 16.29/2.42  % (3661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.42  % (3661)Termination reason: Time limit
% 16.29/2.42  % (3661)Termination phase: Saturation
% 16.29/2.42  
% 16.29/2.42  % (3661)Memory used [KB]: 37483
% 16.29/2.42  % (3661)Time elapsed: 2.0000 s
% 16.29/2.42  % (3661)------------------------------
% 16.29/2.42  % (3661)------------------------------
% 16.29/2.43  % (3739)Time limit reached!
% 16.29/2.43  % (3739)------------------------------
% 16.29/2.43  % (3739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.43  % (3739)Termination reason: Time limit
% 16.29/2.43  
% 16.29/2.43  % (3739)Memory used [KB]: 17654
% 16.29/2.43  % (3739)Time elapsed: 1.323 s
% 16.29/2.43  % (3739)------------------------------
% 16.29/2.43  % (3739)------------------------------
% 16.29/2.44  % (3728)Time limit reached!
% 16.29/2.44  % (3728)------------------------------
% 16.29/2.44  % (3728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.44  % (3728)Termination reason: Time limit
% 16.29/2.44  % (3728)Termination phase: Saturation
% 16.29/2.44  
% 16.29/2.44  % (3728)Memory used [KB]: 191766
% 16.29/2.44  % (3728)Time elapsed: 1.700 s
% 16.29/2.44  % (3728)------------------------------
% 16.29/2.44  % (3728)------------------------------
% 17.37/2.56  % (3674)Time limit reached!
% 17.37/2.56  % (3674)------------------------------
% 17.37/2.56  % (3674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.37/2.56  % (3674)Termination reason: Time limit
% 17.37/2.56  % (3674)Termination phase: Saturation
% 17.37/2.56  
% 17.37/2.56  % (3674)Memory used [KB]: 38123
% 17.37/2.56  % (3674)Time elapsed: 2.155 s
% 17.37/2.56  % (3674)------------------------------
% 17.37/2.56  % (3674)------------------------------
% 21.10/3.03  % (3675)Time limit reached!
% 21.10/3.03  % (3675)------------------------------
% 21.10/3.03  % (3675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.10/3.03  % (3675)Termination reason: Time limit
% 21.10/3.03  % (3675)Termination phase: Saturation
% 21.10/3.03  
% 21.10/3.03  % (3675)Memory used [KB]: 52195
% 21.10/3.03  % (3675)Time elapsed: 2.600 s
% 21.10/3.03  % (3675)------------------------------
% 21.10/3.03  % (3675)------------------------------
% 24.00/3.40  % (3690)Time limit reached!
% 24.00/3.40  % (3690)------------------------------
% 24.00/3.40  % (3690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.00/3.40  % (3690)Termination reason: Time limit
% 24.00/3.40  % (3690)Termination phase: Saturation
% 24.00/3.40  
% 24.00/3.40  % (3690)Memory used [KB]: 43368
% 24.00/3.40  % (3690)Time elapsed: 2.800 s
% 24.00/3.40  % (3690)------------------------------
% 24.00/3.40  % (3690)------------------------------
% 24.00/3.43  % (3668)Time limit reached!
% 24.00/3.43  % (3668)------------------------------
% 24.00/3.43  % (3668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.00/3.43  % (3668)Termination reason: Time limit
% 24.00/3.43  % (3668)Termination phase: Saturation
% 24.00/3.43  
% 24.00/3.43  % (3668)Memory used [KB]: 14711
% 24.00/3.43  % (3668)Time elapsed: 3.0000 s
% 24.00/3.43  % (3668)------------------------------
% 24.00/3.43  % (3668)------------------------------
% 31.14/4.32  % (3685)Time limit reached!
% 31.14/4.32  % (3685)------------------------------
% 31.14/4.32  % (3685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.14/4.32  % (3685)Termination reason: Time limit
% 31.14/4.32  % (3685)Termination phase: Saturation
% 31.14/4.32  
% 31.14/4.32  % (3685)Memory used [KB]: 74838
% 31.14/4.32  % (3685)Time elapsed: 3.900 s
% 31.14/4.32  % (3685)------------------------------
% 31.14/4.32  % (3685)------------------------------
% 33.50/4.61  % (3735)Time limit reached!
% 33.50/4.61  % (3735)------------------------------
% 33.50/4.61  % (3735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.50/4.61  % (3735)Termination reason: Time limit
% 33.50/4.61  % (3735)Termination phase: Saturation
% 33.50/4.61  
% 33.50/4.61  % (3735)Memory used [KB]: 87248
% 33.50/4.61  % (3735)Time elapsed: 3.500 s
% 33.50/4.61  % (3735)------------------------------
% 33.50/4.61  % (3735)------------------------------
% 37.44/5.06  % (3703)Refutation found. Thanks to Tanya!
% 37.44/5.06  % SZS status Theorem for theBenchmark
% 37.44/5.06  % SZS output start Proof for theBenchmark
% 37.44/5.06  fof(f61503,plain,(
% 37.44/5.06    $false),
% 37.44/5.06    inference(subsumption_resolution,[],[f61502,f22839])).
% 37.44/5.06  fof(f22839,plain,(
% 37.44/5.06    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f22712,f132])).
% 37.44/5.06  fof(f132,plain,(
% 37.44/5.06    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 37.44/5.06    inference(backward_demodulation,[],[f88,f124])).
% 37.44/5.06  fof(f124,plain,(
% 37.44/5.06    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 37.44/5.06    inference(superposition,[],[f36,f111])).
% 37.44/5.06  fof(f111,plain,(
% 37.44/5.06    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2))) )),
% 37.44/5.06    inference(superposition,[],[f32,f88])).
% 37.44/5.06  fof(f32,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 37.44/5.06    inference(definition_unfolding,[],[f24,f26])).
% 37.44/5.06  fof(f26,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 37.44/5.06    inference(cnf_transformation,[],[f8])).
% 37.44/5.06  fof(f8,axiom,(
% 37.44/5.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 37.44/5.06  fof(f24,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 37.44/5.06    inference(cnf_transformation,[],[f2])).
% 37.44/5.06  fof(f2,axiom,(
% 37.44/5.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 37.44/5.06  fof(f36,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 37.44/5.06    inference(definition_unfolding,[],[f22,f23])).
% 37.44/5.06  fof(f23,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 37.44/5.06    inference(cnf_transformation,[],[f12])).
% 37.44/5.06  fof(f12,axiom,(
% 37.44/5.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 37.44/5.06  fof(f22,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 37.44/5.06    inference(cnf_transformation,[],[f6])).
% 37.44/5.06  fof(f6,axiom,(
% 37.44/5.06    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 37.44/5.06  fof(f88,plain,(
% 37.44/5.06    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 37.44/5.06    inference(superposition,[],[f34,f73])).
% 37.44/5.06  fof(f73,plain,(
% 37.44/5.06    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 37.44/5.06    inference(superposition,[],[f67,f32])).
% 37.44/5.06  fof(f67,plain,(
% 37.44/5.06    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 37.44/5.06    inference(superposition,[],[f64,f32])).
% 37.44/5.06  fof(f64,plain,(
% 37.44/5.06    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 37.44/5.06    inference(superposition,[],[f29,f58])).
% 37.44/5.06  fof(f58,plain,(
% 37.44/5.06    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 37.44/5.06    inference(superposition,[],[f50,f55])).
% 37.44/5.06  fof(f55,plain,(
% 37.44/5.06    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 37.44/5.06    inference(superposition,[],[f36,f50])).
% 37.44/5.06  fof(f50,plain,(
% 37.44/5.06    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 37.44/5.06    inference(superposition,[],[f32,f36])).
% 37.44/5.06  fof(f29,plain,(
% 37.44/5.06    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 37.44/5.06    inference(cnf_transformation,[],[f11])).
% 37.44/5.06  fof(f11,axiom,(
% 37.44/5.06    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 37.44/5.06  fof(f34,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 37.44/5.06    inference(definition_unfolding,[],[f20,f26,f26])).
% 37.44/5.06  fof(f20,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 37.44/5.06    inference(cnf_transformation,[],[f1])).
% 37.44/5.06  fof(f1,axiom,(
% 37.44/5.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 37.44/5.06  fof(f22712,plain,(
% 37.44/5.06    ( ! [X12,X13] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X12,X13))) = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12))) )),
% 37.44/5.06    inference(superposition,[],[f34,f22450])).
% 37.44/5.06  fof(f22450,plain,(
% 37.44/5.06    ( ! [X149,X150] : (k5_xboole_0(X150,X149) = k4_xboole_0(k5_xboole_0(X149,X150),k1_xboole_0)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f22449,f233])).
% 37.44/5.06  fof(f233,plain,(
% 37.44/5.06    ( ! [X9] : (k5_xboole_0(X9,k1_xboole_0) = X9) )),
% 37.44/5.06    inference(forward_demodulation,[],[f216,f124])).
% 37.44/5.06  fof(f216,plain,(
% 37.44/5.06    ( ! [X9] : (k5_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X9,k1_xboole_0))) = X9) )),
% 37.44/5.06    inference(superposition,[],[f41,f132])).
% 37.44/5.06  fof(f41,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 37.44/5.06    inference(backward_demodulation,[],[f35,f39])).
% 37.44/5.06  fof(f39,plain,(
% 37.44/5.06    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 37.44/5.06    inference(definition_unfolding,[],[f30,f26,f26])).
% 37.44/5.06  fof(f30,plain,(
% 37.44/5.06    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 37.44/5.06    inference(cnf_transformation,[],[f9])).
% 37.44/5.06  fof(f9,axiom,(
% 37.44/5.06    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 37.44/5.06  fof(f35,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 37.44/5.06    inference(definition_unfolding,[],[f21,f23,f26])).
% 37.44/5.06  fof(f21,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 37.44/5.06    inference(cnf_transformation,[],[f4])).
% 37.44/5.06  fof(f4,axiom,(
% 37.44/5.06    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 37.44/5.06  fof(f22449,plain,(
% 37.44/5.06    ( ! [X149,X150] : (k4_xboole_0(k5_xboole_0(X149,X150),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X150,X149),k1_xboole_0)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f22273,f132])).
% 37.44/5.06  fof(f22273,plain,(
% 37.44/5.06    ( ! [X149,X150] : (k4_xboole_0(k5_xboole_0(X149,X150),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X150,X149),k4_xboole_0(k1_xboole_0,k5_xboole_0(X149,X150)))) )),
% 37.44/5.06    inference(superposition,[],[f21120,f2459])).
% 37.44/5.06  fof(f2459,plain,(
% 37.44/5.06    ( ! [X50,X51] : (k5_xboole_0(X51,X50) = k5_xboole_0(k5_xboole_0(X50,X51),k1_xboole_0)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f2416,f405])).
% 37.44/5.06  fof(f405,plain,(
% 37.44/5.06    ( ! [X7] : (k5_xboole_0(k1_xboole_0,X7) = X7) )),
% 37.44/5.06    inference(forward_demodulation,[],[f391,f236])).
% 37.44/5.06  fof(f236,plain,(
% 37.44/5.06    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 37.44/5.06    inference(backward_demodulation,[],[f124,f234])).
% 37.44/5.06  fof(f234,plain,(
% 37.44/5.06    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 37.44/5.06    inference(backward_demodulation,[],[f136,f233])).
% 37.44/5.06  fof(f136,plain,(
% 37.44/5.06    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 37.44/5.06    inference(backward_demodulation,[],[f111,f132])).
% 37.44/5.06  fof(f391,plain,(
% 37.44/5.06    ( ! [X7] : (k5_xboole_0(k4_xboole_0(X7,X7),X7) = X7) )),
% 37.44/5.06    inference(superposition,[],[f247,f222])).
% 37.44/5.06  fof(f222,plain,(
% 37.44/5.06    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5) )),
% 37.44/5.06    inference(superposition,[],[f41,f32])).
% 37.44/5.06  fof(f247,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 37.44/5.06    inference(backward_demodulation,[],[f38,f222])).
% 37.44/5.06  fof(f38,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 37.44/5.06    inference(definition_unfolding,[],[f27,f23,f26])).
% 37.44/5.06  fof(f27,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 37.44/5.06    inference(cnf_transformation,[],[f10])).
% 37.44/5.06  fof(f10,axiom,(
% 37.44/5.06    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 37.44/5.06  fof(f2416,plain,(
% 37.44/5.06    ( ! [X50,X51] : (k5_xboole_0(k5_xboole_0(X50,X51),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X51,X50))) )),
% 37.44/5.06    inference(superposition,[],[f2273,f2273])).
% 37.44/5.06  fof(f2273,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) )),
% 37.44/5.06    inference(superposition,[],[f1423,f235])).
% 37.44/5.06  fof(f235,plain,(
% 37.44/5.06    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 37.44/5.06    inference(backward_demodulation,[],[f50,f234])).
% 37.44/5.06  fof(f1423,plain,(
% 37.44/5.06    ( ! [X24,X23,X25] : (k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24))) )),
% 37.44/5.06    inference(superposition,[],[f424,f463])).
% 37.44/5.06  fof(f463,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 37.44/5.06    inference(forward_demodulation,[],[f451,f233])).
% 37.44/5.06  fof(f451,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 37.44/5.06    inference(superposition,[],[f406,f240])).
% 37.44/5.06  fof(f240,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f146,f234])).
% 37.44/5.06  fof(f146,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),k1_xboole_0))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f54,f144])).
% 37.44/5.06  fof(f144,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f141,f136])).
% 37.44/5.06  fof(f141,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f122,f132])).
% 37.44/5.06  fof(f122,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))))) )),
% 37.44/5.06    inference(superposition,[],[f111,f29])).
% 37.44/5.06  fof(f54,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)))) )),
% 37.44/5.06    inference(superposition,[],[f50,f29])).
% 37.44/5.06  fof(f406,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 37.44/5.06    inference(backward_demodulation,[],[f241,f405])).
% 37.44/5.06  fof(f241,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f149,f238])).
% 37.44/5.06  fof(f238,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f148,f234])).
% 37.44/5.06  fof(f148,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2) = k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f126,f132])).
% 37.44/5.06  fof(f126,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2)) )),
% 37.44/5.06    inference(superposition,[],[f29,f111])).
% 37.44/5.06  fof(f149,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f56,f148])).
% 37.44/5.06  fof(f56,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 37.44/5.06    inference(superposition,[],[f29,f50])).
% 37.44/5.06  fof(f424,plain,(
% 37.44/5.06    ( ! [X10,X8,X9] : (k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) = X10) )),
% 37.44/5.06    inference(superposition,[],[f406,f29])).
% 37.44/5.06  fof(f21120,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))) )),
% 37.44/5.06    inference(superposition,[],[f424,f20225])).
% 37.44/5.06  fof(f20225,plain,(
% 37.44/5.06    ( ! [X24,X25] : (k4_xboole_0(X25,X24) = k5_xboole_0(X24,k5_xboole_0(X25,k4_xboole_0(X24,X25)))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f19963,f481])).
% 37.44/5.06  fof(f481,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 37.44/5.06    inference(superposition,[],[f406,f463])).
% 37.44/5.06  fof(f19963,plain,(
% 37.44/5.06    ( ! [X24,X25] : (k4_xboole_0(X25,X24) = k5_xboole_0(X24,k5_xboole_0(k4_xboole_0(X24,X25),X25))) )),
% 37.44/5.06    inference(superposition,[],[f406,f19734])).
% 37.44/5.06  fof(f19734,plain,(
% 37.44/5.06    ( ! [X10,X11] : (k5_xboole_0(X10,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X11)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f19485,f37])).
% 37.44/5.06  fof(f37,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 37.44/5.06    inference(definition_unfolding,[],[f25,f26])).
% 37.44/5.06  fof(f25,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 37.44/5.06    inference(cnf_transformation,[],[f7])).
% 37.44/5.06  fof(f7,axiom,(
% 37.44/5.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 37.44/5.06  fof(f19485,plain,(
% 37.44/5.06    ( ! [X10,X11] : (k5_xboole_0(X10,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))),X11)) )),
% 37.44/5.06    inference(superposition,[],[f398,f382])).
% 37.44/5.06  fof(f382,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 37.44/5.06    inference(superposition,[],[f247,f34])).
% 37.44/5.06  fof(f398,plain,(
% 37.44/5.06    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,X2)) )),
% 37.44/5.06    inference(superposition,[],[f29,f247])).
% 37.44/5.06  fof(f61502,plain,(
% 37.44/5.06    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0))),
% 37.44/5.06    inference(forward_demodulation,[],[f61501,f22839])).
% 37.44/5.06  fof(f61501,plain,(
% 37.44/5.06    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) != k4_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))),
% 37.44/5.06    inference(backward_demodulation,[],[f815,f61500])).
% 37.44/5.06  fof(f61500,plain,(
% 37.44/5.06    ( ! [X229,X228] : (k5_xboole_0(X228,X229) = k4_xboole_0(k5_xboole_0(X229,k4_xboole_0(X228,X229)),k4_xboole_0(X229,k4_xboole_0(X229,X228)))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f61153,f61392])).
% 37.44/5.06  fof(f61392,plain,(
% 37.44/5.06    ( ! [X37,X36] : (k4_xboole_0(X37,k4_xboole_0(X37,X36)) = k4_xboole_0(X37,k5_xboole_0(X36,X37))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f61391,f179])).
% 37.44/5.06  fof(f179,plain,(
% 37.44/5.06    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 37.44/5.06    inference(superposition,[],[f32,f37])).
% 37.44/5.06  fof(f61391,plain,(
% 37.44/5.06    ( ! [X37,X36] : (k5_xboole_0(X37,k4_xboole_0(X37,X36)) = k4_xboole_0(X37,k5_xboole_0(X36,X37))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f61079,f54201])).
% 37.44/5.06  fof(f54201,plain,(
% 37.44/5.06    ( ! [X218,X219] : (k4_xboole_0(X219,X218) = k4_xboole_0(k5_xboole_0(X218,X219),k4_xboole_0(X218,X219))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f54198,f405])).
% 37.44/5.06  fof(f54198,plain,(
% 37.44/5.06    ( ! [X218,X219] : (k4_xboole_0(k5_xboole_0(X218,X219),k4_xboole_0(X218,X219)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X219,X218))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f26925,f54030])).
% 37.44/5.06  fof(f54030,plain,(
% 37.44/5.06    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6))) )),
% 37.44/5.06    inference(superposition,[],[f2794,f19699])).
% 37.44/5.06  fof(f19699,plain,(
% 37.44/5.06    ( ! [X6,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f19483,f37])).
% 37.44/5.06  fof(f19483,plain,(
% 37.44/5.06    ( ! [X6,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))),k4_xboole_0(X7,X6))) )),
% 37.44/5.06    inference(superposition,[],[f398,f863])).
% 37.44/5.06  fof(f863,plain,(
% 37.44/5.06    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X15)) )),
% 37.44/5.06    inference(superposition,[],[f473,f184])).
% 37.44/5.06  fof(f184,plain,(
% 37.44/5.06    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f91,f175])).
% 37.44/5.06  fof(f175,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 37.44/5.06    inference(superposition,[],[f37,f34])).
% 37.44/5.06  fof(f91,plain,(
% 37.44/5.06    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 37.44/5.06    inference(superposition,[],[f32,f34])).
% 37.44/5.06  fof(f473,plain,(
% 37.44/5.06    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) )),
% 37.44/5.06    inference(superposition,[],[f463,f463])).
% 37.44/5.06  fof(f2794,plain,(
% 37.44/5.06    ( ! [X35,X36,X34] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X34,X35)))) )),
% 37.44/5.06    inference(superposition,[],[f36,f2168])).
% 37.44/5.06  fof(f2168,plain,(
% 37.44/5.06    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))) )),
% 37.44/5.06    inference(superposition,[],[f2105,f222])).
% 37.44/5.06  fof(f2105,plain,(
% 37.44/5.06    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21) )),
% 37.44/5.06    inference(forward_demodulation,[],[f2028,f234])).
% 37.44/5.06  fof(f2028,plain,(
% 37.44/5.06    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21) )),
% 37.44/5.06    inference(superposition,[],[f1868,f346])).
% 37.44/5.06  fof(f346,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f319,f175])).
% 37.44/5.06  fof(f319,plain,(
% 37.44/5.06    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X1)) )),
% 37.44/5.06    inference(superposition,[],[f251,f34])).
% 37.44/5.06  fof(f251,plain,(
% 37.44/5.06    ( ! [X17,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),X16)) )),
% 37.44/5.06    inference(backward_demodulation,[],[f181,f247])).
% 37.44/5.06  fof(f181,plain,(
% 37.44/5.06    ( ! [X17,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k5_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17)))) )),
% 37.44/5.06    inference(superposition,[],[f36,f37])).
% 37.44/5.06  fof(f1868,plain,(
% 37.44/5.06    ( ! [X50,X48,X49] : (k4_xboole_0(X50,k4_xboole_0(X48,k4_xboole_0(X48,k4_xboole_0(X49,X50)))) = X50) )),
% 37.44/5.06    inference(superposition,[],[f222,f39])).
% 37.44/5.06  fof(f26925,plain,(
% 37.44/5.06    ( ! [X218,X219] : (k4_xboole_0(k5_xboole_0(X218,X219),k4_xboole_0(X218,X219)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X218,X219),k5_xboole_0(X218,X219)),k4_xboole_0(X219,X218))) )),
% 37.44/5.06    inference(superposition,[],[f21124,f21126])).
% 37.44/5.06  fof(f21126,plain,(
% 37.44/5.06    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15))) )),
% 37.44/5.06    inference(superposition,[],[f1395,f20225])).
% 37.44/5.06  fof(f1395,plain,(
% 37.44/5.06    ( ! [X4,X2,X3] : (k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = X4) )),
% 37.44/5.06    inference(superposition,[],[f424,f481])).
% 37.44/5.06  fof(f21124,plain,(
% 37.44/5.06    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))) )),
% 37.44/5.06    inference(superposition,[],[f517,f20225])).
% 37.44/5.06  fof(f517,plain,(
% 37.44/5.06    ( ! [X12,X10,X11] : (k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(X11,X12)),k5_xboole_0(X10,X11)) = X12) )),
% 37.44/5.06    inference(superposition,[],[f473,f29])).
% 37.44/5.06  fof(f61079,plain,(
% 37.44/5.06    ( ! [X37,X36] : (k4_xboole_0(X37,k5_xboole_0(X36,X37)) = k5_xboole_0(X37,k4_xboole_0(k5_xboole_0(X36,X37),k4_xboole_0(X36,X37)))) )),
% 37.44/5.06    inference(superposition,[],[f90,f60714])).
% 37.44/5.06  fof(f60714,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,X1),X1)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f60713,f234])).
% 37.44/5.06  fof(f60713,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X0,X1),X1)) )),
% 37.44/5.06    inference(backward_demodulation,[],[f60375,f60431])).
% 37.44/5.06  fof(f60431,plain,(
% 37.44/5.06    ( ! [X123,X124] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X123,X124),k4_xboole_0(k5_xboole_0(X123,X124),X124))) )),
% 37.44/5.06    inference(superposition,[],[f58050,f472])).
% 37.44/5.06  fof(f472,plain,(
% 37.44/5.06    ( ! [X4,X3] : (k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3) )),
% 37.44/5.06    inference(superposition,[],[f463,f406])).
% 37.44/5.06  fof(f58050,plain,(
% 37.44/5.06    ( ! [X21,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X20,X21),X21),k4_xboole_0(X20,X21))) )),
% 37.44/5.06    inference(superposition,[],[f48292,f54193])).
% 37.44/5.06  fof(f54193,plain,(
% 37.44/5.06    ( ! [X121,X120] : (k4_xboole_0(X120,X121) = k4_xboole_0(k5_xboole_0(X120,X121),k4_xboole_0(X121,X120))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f54190,f405])).
% 37.44/5.06  fof(f54190,plain,(
% 37.44/5.06    ( ! [X121,X120] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X120,X121)) = k4_xboole_0(k5_xboole_0(X120,X121),k4_xboole_0(X121,X120))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f26317,f54029])).
% 37.44/5.06  fof(f54029,plain,(
% 37.44/5.06    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3))) )),
% 37.44/5.06    inference(superposition,[],[f2794,f21123])).
% 37.44/5.06  fof(f21123,plain,(
% 37.44/5.06    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8))) )),
% 37.44/5.06    inference(superposition,[],[f500,f20225])).
% 37.44/5.06  fof(f500,plain,(
% 37.44/5.06    ( ! [X12,X10,X11] : (k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(X11,X12)),X12)) )),
% 37.44/5.06    inference(superposition,[],[f472,f29])).
% 37.44/5.06  fof(f26317,plain,(
% 37.44/5.06    ( ! [X121,X120] : (k4_xboole_0(k5_xboole_0(X120,X121),k4_xboole_0(X121,X120)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X121,X120),k5_xboole_0(X120,X121)),k4_xboole_0(X120,X121))) )),
% 37.44/5.06    inference(superposition,[],[f21124,f21120])).
% 37.44/5.06  fof(f48292,plain,(
% 37.44/5.06    ( ! [X19,X17,X18] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,k4_xboole_0(X18,X19)))) )),
% 37.44/5.06    inference(superposition,[],[f48054,f2168])).
% 37.44/5.06  fof(f48054,plain,(
% 37.44/5.06    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f48053,f463])).
% 37.44/5.06  fof(f48053,plain,(
% 37.44/5.06    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,X3)),X4))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f48052,f19699])).
% 37.44/5.06  fof(f48052,plain,(
% 37.44/5.06    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f47869,f1676])).
% 37.44/5.06  fof(f1676,plain,(
% 37.44/5.06    ( ! [X45,X46,X44] : (k5_xboole_0(X46,k4_xboole_0(X44,k4_xboole_0(X44,X45))) = k5_xboole_0(X44,k5_xboole_0(X46,k4_xboole_0(X44,X45)))) )),
% 37.44/5.06    inference(superposition,[],[f476,f423])).
% 37.44/5.06  fof(f423,plain,(
% 37.44/5.06    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k5_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X6)) )),
% 37.44/5.06    inference(superposition,[],[f406,f247])).
% 37.44/5.06  fof(f476,plain,(
% 37.44/5.06    ( ! [X12,X10,X11] : (k5_xboole_0(X10,X11) = k5_xboole_0(X12,k5_xboole_0(X10,k5_xboole_0(X11,X12)))) )),
% 37.44/5.06    inference(superposition,[],[f463,f29])).
% 37.44/5.06  fof(f47869,plain,(
% 37.44/5.06    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4))) )),
% 37.44/5.06    inference(superposition,[],[f24444,f34])).
% 37.44/5.06  fof(f24444,plain,(
% 37.44/5.06    ( ! [X45,X46,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X46),k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X45,X44)),X46))) )),
% 37.44/5.06    inference(superposition,[],[f328,f1913])).
% 37.44/5.06  fof(f1913,plain,(
% 37.44/5.06    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f1816,f234])).
% 37.44/5.06  fof(f1816,plain,(
% 37.44/5.06    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22)) )),
% 37.44/5.06    inference(superposition,[],[f39,f36])).
% 37.44/5.06  fof(f328,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 37.44/5.06    inference(superposition,[],[f251,f34])).
% 37.44/5.06  fof(f60375,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X1)))) )),
% 37.44/5.06    inference(unit_resulting_resolution,[],[f58050,f17646])).
% 37.44/5.06  fof(f17646,plain,(
% 37.44/5.06    ( ! [X14,X13] : (k1_xboole_0 != k4_xboole_0(X13,X14) | k4_xboole_0(X14,k4_xboole_0(X14,X13)) = X13) )),
% 37.44/5.06    inference(forward_demodulation,[],[f17581,f382])).
% 37.44/5.06  fof(f17581,plain,(
% 37.44/5.06    ( ! [X14,X13] : (k1_xboole_0 != k4_xboole_0(X13,X14) | k4_xboole_0(X14,k4_xboole_0(X14,X13)) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),k4_xboole_0(X13,X14))) )),
% 37.44/5.06    inference(superposition,[],[f1312,f175])).
% 37.44/5.06  fof(f1312,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 37.44/5.06    inference(forward_demodulation,[],[f1267,f36])).
% 37.44/5.06  fof(f1267,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 37.44/5.06    inference(superposition,[],[f28,f689])).
% 37.44/5.06  fof(f689,plain,(
% 37.44/5.06    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f688,f473])).
% 37.44/5.06  fof(f688,plain,(
% 37.44/5.06    ( ! [X10,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9)) )),
% 37.44/5.06    inference(forward_demodulation,[],[f658,f234])).
% 37.44/5.06  fof(f658,plain,(
% 37.44/5.06    ( ! [X10,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k1_xboole_0))) )),
% 37.44/5.06    inference(superposition,[],[f90,f36])).
% 37.44/5.06  fof(f28,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 37.44/5.06    inference(cnf_transformation,[],[f16])).
% 37.44/5.06  fof(f16,plain,(
% 37.44/5.06    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 37.44/5.06    inference(ennf_transformation,[],[f5])).
% 37.44/5.06  fof(f5,axiom,(
% 37.44/5.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 37.44/5.06  fof(f90,plain,(
% 37.44/5.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 37.44/5.06    inference(superposition,[],[f32,f34])).
% 37.44/5.06  fof(f61153,plain,(
% 37.44/5.06    ( ! [X229,X228] : (k5_xboole_0(X228,X229) = k4_xboole_0(k5_xboole_0(X229,k4_xboole_0(X228,X229)),k4_xboole_0(X229,k5_xboole_0(X228,X229)))) )),
% 37.44/5.06    inference(superposition,[],[f20221,f60714])).
% 37.44/5.06  fof(f20221,plain,(
% 37.44/5.06    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8) )),
% 37.44/5.06    inference(forward_demodulation,[],[f19959,f481])).
% 37.44/5.06  fof(f19959,plain,(
% 37.44/5.06    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X8,X9),X9),k4_xboole_0(X9,X8)) = X8) )),
% 37.44/5.06    inference(superposition,[],[f1231,f19734])).
% 37.44/5.06  fof(f1231,plain,(
% 37.44/5.06    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15)) = X15) )),
% 37.44/5.06    inference(forward_demodulation,[],[f1230,f472])).
% 37.44/5.06  fof(f1230,plain,(
% 37.44/5.06    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15)) = k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15))) )),
% 37.44/5.06    inference(forward_demodulation,[],[f1202,f234])).
% 37.44/5.06  fof(f1202,plain,(
% 37.44/5.06    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(X14,X15)) = k5_xboole_0(k5_xboole_0(X15,k4_xboole_0(X14,X15)),k4_xboole_0(k4_xboole_0(X14,X15),k1_xboole_0))) )),
% 37.44/5.06    inference(superposition,[],[f90,f490])).
% 37.44/5.06  fof(f490,plain,(
% 37.44/5.06    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X14,k4_xboole_0(X15,X14)))) )),
% 37.44/5.06    inference(backward_demodulation,[],[f298,f481])).
% 37.44/5.06  fof(f298,plain,(
% 37.44/5.06    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(k4_xboole_0(X15,X14),X14))) )),
% 37.44/5.06    inference(superposition,[],[f36,f222])).
% 37.44/5.06  fof(f815,plain,(
% 37.44/5.06    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))),
% 37.44/5.06    inference(unit_resulting_resolution,[],[f33,f28])).
% 37.44/5.06  fof(f33,plain,(
% 37.44/5.06    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 37.44/5.06    inference(definition_unfolding,[],[f19,f23,f26])).
% 37.44/5.06  fof(f19,plain,(
% 37.44/5.06    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 37.44/5.06    inference(cnf_transformation,[],[f18])).
% 37.44/5.06  fof(f18,plain,(
% 37.44/5.06    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 37.44/5.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 37.44/5.06  fof(f17,plain,(
% 37.44/5.06    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 37.44/5.06    introduced(choice_axiom,[])).
% 37.44/5.06  fof(f15,plain,(
% 37.44/5.06    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 37.44/5.06    inference(ennf_transformation,[],[f14])).
% 37.44/5.06  fof(f14,negated_conjecture,(
% 37.44/5.06    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 37.44/5.06    inference(negated_conjecture,[],[f13])).
% 37.44/5.06  fof(f13,conjecture,(
% 37.44/5.06    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 37.44/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 37.44/5.06  % SZS output end Proof for theBenchmark
% 37.44/5.06  % (3703)------------------------------
% 37.44/5.06  % (3703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 37.44/5.06  % (3703)Termination reason: Refutation
% 37.44/5.06  
% 37.44/5.06  % (3703)Memory used [KB]: 88527
% 37.44/5.06  % (3703)Time elapsed: 4.378 s
% 37.44/5.06  % (3703)------------------------------
% 37.44/5.06  % (3703)------------------------------
% 37.62/5.07  % (3654)Success in time 4.707 s
%------------------------------------------------------------------------------
