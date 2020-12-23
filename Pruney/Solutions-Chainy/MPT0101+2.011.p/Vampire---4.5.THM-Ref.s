%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:53 EST 2020

% Result     : Theorem 21.48s
% Output     : Refutation 21.48s
% Verified   : 
% Statistics : Number of formulae       :  129 (1001 expanded)
%              Number of leaves         :   20 ( 322 expanded)
%              Depth                    :   24
%              Number of atoms          :  150 (1199 expanded)
%              Number of equality atoms :  122 ( 970 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33889,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33888,f5242])).

fof(f5242,plain,(
    ! [X74,X73] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X73,X74),k2_xboole_0(X74,X73)) ),
    inference(superposition,[],[f186,f1155])).

fof(f1155,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f119,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f119,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f31,f35])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f186,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f175,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f175,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f29,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f44,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f33888,plain,(
    k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f33887,f33826])).

fof(f33826,plain,(
    ! [X17,X18] : k2_xboole_0(X18,X17) = k2_xboole_0(X18,k4_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f33553,f21461])).

fof(f21461,plain,(
    ! [X99,X97,X98] : k2_xboole_0(X99,X97) = k2_xboole_0(k2_xboole_0(X99,k4_xboole_0(X97,X98)),X97) ),
    inference(superposition,[],[f1046,f409])).

fof(f409,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9 ),
    inference(forward_demodulation,[],[f408,f286])).

fof(f286,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f247,f66])).

fof(f66,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(superposition,[],[f52,f35])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f247,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(superposition,[],[f34,f66])).

fof(f408,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(forward_demodulation,[],[f382,f72])).

fof(f382,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(superposition,[],[f30,f286])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f1046,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X12,k2_xboole_0(X11,X13)) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13)) ),
    inference(forward_demodulation,[],[f1004,f31])).

fof(f1004,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k2_xboole_0(X12,X11),X13) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13)) ),
    inference(superposition,[],[f113,f87])).

fof(f113,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f31,f35])).

fof(f33553,plain,(
    ! [X17,X18] : k2_xboole_0(X18,k4_xboole_0(X17,X18)) = k2_xboole_0(k2_xboole_0(X18,k4_xboole_0(X17,X18)),X17) ),
    inference(superposition,[],[f31575,f5898])).

fof(f5898,plain,(
    ! [X116,X115] : k3_xboole_0(X115,k2_xboole_0(X116,k4_xboole_0(X115,X116))) = X115 ),
    inference(forward_demodulation,[],[f5796,f286])).

fof(f5796,plain,(
    ! [X116,X115] : k3_xboole_0(X115,k2_xboole_0(X116,k4_xboole_0(X115,X116))) = k4_xboole_0(X115,k1_xboole_0) ),
    inference(superposition,[],[f255,f1340])).

fof(f1340,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f396,f59])).

fof(f396,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X5)) = k4_xboole_0(k4_xboole_0(X3,X4),X5) ),
    inference(backward_demodulation,[],[f176,f394])).

fof(f394,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f380,f242])).

fof(f242,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f239,f59])).

fof(f239,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f232,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f232,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f57,f86])).

fof(f86,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f380,plain,(
    ! [X6,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k2_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f29,f286])).

fof(f176,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X3),X5) = k4_xboole_0(X3,k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f29,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f255,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f153,f247])).

fof(f153,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f28,f59])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f31575,plain,(
    ! [X54,X55] : k2_xboole_0(X54,k3_xboole_0(X55,X54)) = X54 ),
    inference(superposition,[],[f392,f31077])).

fof(f31077,plain,(
    ! [X61,X60] : k3_xboole_0(X60,X61) = k3_xboole_0(X61,X60) ),
    inference(subsumption_resolution,[],[f30855,f10262])).

fof(f10262,plain,(
    ! [X14,X13] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X13,X14),k3_xboole_0(X14,X13)) ),
    inference(superposition,[],[f1659,f59])).

fof(f1659,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k3_xboole_0(X4,X5)) = k4_xboole_0(X3,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f197,f30])).

fof(f197,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X3,X5),k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f30,f35])).

fof(f30855,plain,(
    ! [X61,X60] :
      ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(X61,X60),k3_xboole_0(X60,X61))
      | k3_xboole_0(X60,X61) = k3_xboole_0(X61,X60) ) ),
    inference(superposition,[],[f33,f10262])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f392,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f391,f286])).

fof(f391,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f378,f45])).

fof(f378,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f28,f286])).

fof(f33887,plain,(
    k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f33886,f35])).

fof(f33886,plain,(
    k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f33885,f11059])).

fof(f11059,plain,(
    ! [X146,X147,X148] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X146,X147),X148),k2_xboole_0(X146,X148)) ),
    inference(superposition,[],[f186,f1990])).

fof(f1990,plain,(
    ! [X52,X53,X51] : k2_xboole_0(X51,X53) = k2_xboole_0(X51,k2_xboole_0(k4_xboole_0(X51,X52),X53)) ),
    inference(forward_demodulation,[],[f1989,f806])).

fof(f806,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,X2) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f31,f252])).

fof(f252,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f207,f247])).

fof(f207,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = X0 ),
    inference(backward_demodulation,[],[f105,f194])).

fof(f194,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f30,f59])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(unit_resulting_resolution,[],[f39,f42])).

fof(f1989,plain,(
    ! [X52,X53,X51] : k2_xboole_0(k3_xboole_0(X51,X52),k2_xboole_0(k4_xboole_0(X51,X52),X53)) = k2_xboole_0(X51,k2_xboole_0(k4_xboole_0(X51,X52),X53)) ),
    inference(forward_demodulation,[],[f1914,f1856])).

fof(f1856,plain,(
    ! [X24,X23,X25] : k2_xboole_0(X23,X25) = k2_xboole_0(X23,k2_xboole_0(k3_xboole_0(X23,X24),X25)) ),
    inference(superposition,[],[f113,f807])).

fof(f807,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3 ),
    inference(superposition,[],[f34,f252])).

fof(f1914,plain,(
    ! [X52,X53,X51] : k2_xboole_0(k3_xboole_0(X51,X52),k2_xboole_0(k4_xboole_0(X51,X52),X53)) = k2_xboole_0(X51,k2_xboole_0(k3_xboole_0(X51,X52),k2_xboole_0(k4_xboole_0(X51,X52),X53))) ),
    inference(superposition,[],[f122,f252])).

fof(f122,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f34,f31])).

fof(f33885,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK1),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f33884,f286])).

fof(f33884,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f33883,f59])).

fof(f33883,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK0))),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f33882,f35])).

fof(f33882,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,sK1))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f33881,f31564])).

fof(f31564,plain,(
    ! [X26,X24,X27,X25] : k2_xboole_0(k4_xboole_0(X24,k4_xboole_0(X26,X25)),X27) = k2_xboole_0(k4_xboole_0(X24,X26),k2_xboole_0(k3_xboole_0(X25,X24),X27)) ),
    inference(superposition,[],[f159,f31077])).

fof(f159,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X0,X2),X3)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(superposition,[],[f31,f28])).

fof(f33881,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f33867,f119])).

fof(f33867,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f6244,f33826])).

fof(f6244,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6241,f3461])).

fof(f3461,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f3404,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f39,f38])).

fof(f3404,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k4_xboole_0(X2,X1)) ),
    inference(unit_resulting_resolution,[],[f161,f140])).

fof(f140,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k4_xboole_0(X4,X5))
      | k4_xboole_0(k3_xboole_0(X3,X4),X5) = X3 ) ),
    inference(superposition,[],[f32,f38])).

fof(f161,plain,(
    ! [X8,X7,X9] : r1_tarski(k3_xboole_0(X7,X9),k4_xboole_0(X7,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f57,f28])).

fof(f6241,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f228,f6239])).

fof(f6239,plain,(
    ! [X35,X33,X34,X32] : k4_xboole_0(k3_xboole_0(X32,X33),X35) = k4_xboole_0(k3_xboole_0(X32,X33),k2_xboole_0(X35,k4_xboole_0(X34,X32))) ),
    inference(forward_demodulation,[],[f6180,f394])).

fof(f6180,plain,(
    ! [X35,X33,X34,X32] : k4_xboole_0(k3_xboole_0(X32,X33),k2_xboole_0(X35,k4_xboole_0(X34,X32))) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X32,X33),X35),k3_xboole_0(X32,X33)) ),
    inference(superposition,[],[f29,f432])).

fof(f432,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X5,X3)) ),
    inference(forward_demodulation,[],[f427,f409])).

fof(f427,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X3,X4),X5),k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f28,f81])).

fof(f228,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f224,f35])).

fof(f224,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f33])).

fof(f49,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f27,f40,f40])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:22:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (1737)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (1719)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (1711)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (1706)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (1719)Refutation not found, incomplete strategy% (1719)------------------------------
% 0.21/0.52  % (1719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1718)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (1719)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1719)Memory used [KB]: 10618
% 0.21/0.52  % (1719)Time elapsed: 0.108 s
% 0.21/0.52  % (1719)------------------------------
% 0.21/0.52  % (1719)------------------------------
% 0.21/0.52  % (1717)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (1716)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (1708)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (1709)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (1712)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (1730)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (1710)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (1734)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1734)Refutation not found, incomplete strategy% (1734)------------------------------
% 0.21/0.54  % (1734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1734)Memory used [KB]: 6140
% 0.21/0.54  % (1734)Time elapsed: 0.128 s
% 0.21/0.54  % (1734)------------------------------
% 0.21/0.54  % (1734)------------------------------
% 0.21/0.54  % (1717)Refutation not found, incomplete strategy% (1717)------------------------------
% 0.21/0.54  % (1717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1717)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1717)Memory used [KB]: 10746
% 0.21/0.54  % (1717)Time elapsed: 0.108 s
% 0.21/0.54  % (1717)------------------------------
% 0.21/0.54  % (1717)------------------------------
% 0.21/0.54  % (1725)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (1725)Refutation not found, incomplete strategy% (1725)------------------------------
% 0.21/0.55  % (1725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1725)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1725)Memory used [KB]: 1663
% 0.21/0.55  % (1725)Time elapsed: 0.128 s
% 0.21/0.55  % (1725)------------------------------
% 0.21/0.55  % (1725)------------------------------
% 1.41/0.55  % (1735)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.55  % (1735)Refutation not found, incomplete strategy% (1735)------------------------------
% 1.41/0.55  % (1735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (1735)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (1735)Memory used [KB]: 6140
% 1.41/0.55  % (1735)Time elapsed: 0.130 s
% 1.41/0.55  % (1735)------------------------------
% 1.41/0.55  % (1735)------------------------------
% 1.41/0.55  % (1722)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.55  % (1733)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.55  % (1727)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.55  % (1736)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.55  % (1736)Refutation not found, incomplete strategy% (1736)------------------------------
% 1.41/0.55  % (1736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (1736)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (1736)Memory used [KB]: 10746
% 1.41/0.55  % (1736)Time elapsed: 0.141 s
% 1.41/0.55  % (1736)------------------------------
% 1.41/0.55  % (1736)------------------------------
% 1.41/0.55  % (1728)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.55  % (1726)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.55  % (1715)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.56  % (1723)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.56  % (1724)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.56  % (1724)Refutation not found, incomplete strategy% (1724)------------------------------
% 1.41/0.56  % (1724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (1724)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (1724)Memory used [KB]: 1663
% 1.41/0.56  % (1724)Time elapsed: 0.149 s
% 1.41/0.56  % (1724)------------------------------
% 1.41/0.56  % (1724)------------------------------
% 1.41/0.56  % (1723)Refutation not found, incomplete strategy% (1723)------------------------------
% 1.41/0.56  % (1723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (1723)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (1723)Memory used [KB]: 10618
% 1.41/0.56  % (1723)Time elapsed: 0.149 s
% 1.41/0.56  % (1723)------------------------------
% 1.41/0.56  % (1723)------------------------------
% 1.41/0.56  % (1707)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.41/0.56  % (1707)Refutation not found, incomplete strategy% (1707)------------------------------
% 1.41/0.56  % (1707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (1732)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.56  % (1707)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (1707)Memory used [KB]: 1663
% 1.41/0.56  % (1707)Time elapsed: 0.142 s
% 1.41/0.56  % (1707)------------------------------
% 1.41/0.56  % (1707)------------------------------
% 1.41/0.56  % (1732)Refutation not found, incomplete strategy% (1732)------------------------------
% 1.41/0.56  % (1732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (1732)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (1732)Memory used [KB]: 10618
% 1.41/0.56  % (1732)Time elapsed: 0.149 s
% 1.41/0.56  % (1732)------------------------------
% 1.41/0.56  % (1732)------------------------------
% 1.56/0.57  % (1720)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.58  % (1721)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.58  % (1713)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.58  % (1729)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.56/0.59  % (1721)Refutation not found, incomplete strategy% (1721)------------------------------
% 1.56/0.59  % (1721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (1721)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (1721)Memory used [KB]: 1663
% 1.56/0.59  % (1721)Time elapsed: 0.104 s
% 1.56/0.59  % (1721)------------------------------
% 1.56/0.59  % (1721)------------------------------
% 2.22/0.67  % (1761)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.22/0.67  % (1760)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.22/0.67  % (1762)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.22/0.68  % (1709)Refutation not found, incomplete strategy% (1709)------------------------------
% 2.22/0.68  % (1709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (1709)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (1709)Memory used [KB]: 6140
% 2.22/0.68  % (1709)Time elapsed: 0.256 s
% 2.22/0.68  % (1709)------------------------------
% 2.22/0.68  % (1709)------------------------------
% 2.22/0.68  % (1722)Refutation not found, incomplete strategy% (1722)------------------------------
% 2.22/0.68  % (1722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (1722)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (1722)Memory used [KB]: 6140
% 2.22/0.68  % (1722)Time elapsed: 0.272 s
% 2.22/0.68  % (1722)------------------------------
% 2.22/0.68  % (1722)------------------------------
% 2.22/0.69  % (1764)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.22/0.69  % (1763)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.22/0.70  % (1765)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.22/0.70  % (1768)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.22/0.71  % (1764)Refutation not found, incomplete strategy% (1764)------------------------------
% 2.22/0.71  % (1764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.71  % (1764)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.71  
% 2.22/0.71  % (1764)Memory used [KB]: 10618
% 2.22/0.71  % (1764)Time elapsed: 0.127 s
% 2.22/0.71  % (1764)------------------------------
% 2.22/0.71  % (1764)------------------------------
% 2.22/0.71  % (1769)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.22/0.72  % (1769)Refutation not found, incomplete strategy% (1769)------------------------------
% 2.22/0.72  % (1769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.72  % (1769)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.72  
% 2.22/0.72  % (1769)Memory used [KB]: 10618
% 2.22/0.72  % (1769)Time elapsed: 0.113 s
% 2.22/0.72  % (1769)------------------------------
% 2.22/0.72  % (1769)------------------------------
% 2.22/0.72  % (1767)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.22/0.72  % (1770)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.22/0.72  % (1766)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.04/0.83  % (1772)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.04/0.84  % (1771)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.04/0.85  % (1708)Time limit reached!
% 3.04/0.85  % (1708)------------------------------
% 3.04/0.85  % (1708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.04/0.85  % (1708)Termination reason: Time limit
% 3.04/0.85  % (1708)Termination phase: Saturation
% 3.04/0.85  
% 3.04/0.85  % (1708)Memory used [KB]: 6524
% 3.04/0.85  % (1708)Time elapsed: 0.400 s
% 3.04/0.85  % (1708)------------------------------
% 3.04/0.85  % (1708)------------------------------
% 3.23/0.87  % (1773)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.23/0.88  % (1773)Refutation not found, incomplete strategy% (1773)------------------------------
% 3.23/0.88  % (1773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.88  % (1773)Termination reason: Refutation not found, incomplete strategy
% 3.23/0.88  
% 3.23/0.88  % (1773)Memory used [KB]: 10618
% 3.23/0.88  % (1773)Time elapsed: 0.131 s
% 3.23/0.88  % (1773)------------------------------
% 3.23/0.88  % (1773)------------------------------
% 3.23/0.89  % (1774)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.23/0.93  % (1712)Time limit reached!
% 3.23/0.93  % (1712)------------------------------
% 3.23/0.93  % (1712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.93  % (1712)Termination reason: Time limit
% 3.23/0.93  
% 3.23/0.93  % (1712)Memory used [KB]: 16758
% 3.23/0.93  % (1712)Time elapsed: 0.519 s
% 3.23/0.93  % (1712)------------------------------
% 3.23/0.93  % (1712)------------------------------
% 3.80/1.00  % (1776)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.80/1.02  % (1775)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.80/1.03  % (1774)Refutation not found, incomplete strategy% (1774)------------------------------
% 3.80/1.03  % (1774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/1.04  % (1777)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 4.09/1.04  % (1774)Termination reason: Refutation not found, incomplete strategy
% 4.09/1.04  
% 4.09/1.04  % (1774)Memory used [KB]: 6268
% 4.09/1.04  % (1774)Time elapsed: 0.278 s
% 4.09/1.04  % (1774)------------------------------
% 4.09/1.04  % (1774)------------------------------
% 4.09/1.06  % (1737)Time limit reached!
% 4.09/1.06  % (1737)------------------------------
% 4.09/1.06  % (1737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/1.06  % (1737)Termination reason: Time limit
% 4.09/1.06  % (1737)Termination phase: Saturation
% 4.09/1.06  
% 4.09/1.06  % (1737)Memory used [KB]: 102599
% 4.09/1.06  % (1737)Time elapsed: 0.500 s
% 4.09/1.06  % (1737)------------------------------
% 4.09/1.06  % (1737)------------------------------
% 5.48/1.11  % (1713)Time limit reached!
% 5.48/1.11  % (1713)------------------------------
% 5.48/1.11  % (1713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.48/1.12  % (1713)Termination reason: Time limit
% 5.48/1.12  
% 5.48/1.12  % (1713)Memory used [KB]: 7164
% 5.48/1.12  % (1713)Time elapsed: 0.619 s
% 5.48/1.12  % (1713)------------------------------
% 5.48/1.12  % (1713)------------------------------
% 6.04/1.17  % (1778)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 6.35/1.21  % (1779)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 6.95/1.28  % (1780)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 6.95/1.29  % (1766)Time limit reached!
% 6.95/1.29  % (1766)------------------------------
% 6.95/1.29  % (1766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.95/1.29  % (1766)Termination reason: Time limit
% 6.95/1.29  % (1766)Termination phase: Saturation
% 6.95/1.29  
% 6.95/1.29  % (1766)Memory used [KB]: 54881
% 6.95/1.29  % (1766)Time elapsed: 0.600 s
% 6.95/1.29  % (1766)------------------------------
% 6.95/1.29  % (1766)------------------------------
% 7.68/1.36  % (1777)Time limit reached!
% 7.68/1.36  % (1777)------------------------------
% 7.68/1.36  % (1777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.68/1.36  % (1777)Termination reason: Time limit
% 7.68/1.36  % (1777)Termination phase: Saturation
% 7.68/1.36  
% 7.68/1.36  % (1777)Memory used [KB]: 10746
% 7.68/1.36  % (1777)Time elapsed: 0.400 s
% 7.68/1.36  % (1777)------------------------------
% 7.68/1.36  % (1777)------------------------------
% 7.68/1.38  % (1775)Time limit reached!
% 7.68/1.38  % (1775)------------------------------
% 7.68/1.38  % (1775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.68/1.38  % (1775)Termination reason: Time limit
% 7.68/1.38  
% 7.68/1.38  % (1775)Memory used [KB]: 7036
% 7.68/1.38  % (1775)Time elapsed: 0.454 s
% 7.68/1.38  % (1775)------------------------------
% 7.68/1.38  % (1775)------------------------------
% 7.68/1.40  % (1762)Time limit reached!
% 7.68/1.40  % (1762)------------------------------
% 7.68/1.40  % (1762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.68/1.40  % (1762)Termination reason: Time limit
% 7.68/1.40  
% 7.68/1.40  % (1762)Memory used [KB]: 15095
% 7.68/1.40  % (1762)Time elapsed: 0.822 s
% 7.68/1.40  % (1762)------------------------------
% 7.68/1.40  % (1762)------------------------------
% 7.68/1.41  % (1776)Time limit reached!
% 7.68/1.41  % (1776)------------------------------
% 7.68/1.41  % (1776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.68/1.41  % (1776)Termination reason: Time limit
% 7.68/1.41  
% 7.68/1.41  % (1776)Memory used [KB]: 13560
% 7.68/1.41  % (1776)Time elapsed: 0.505 s
% 7.68/1.41  % (1776)------------------------------
% 7.68/1.41  % (1776)------------------------------
% 8.56/1.53  % (1779)Time limit reached!
% 8.56/1.53  % (1779)------------------------------
% 8.56/1.53  % (1779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.04/1.55  % (1779)Termination reason: Time limit
% 9.04/1.55  % (1779)Termination phase: Saturation
% 9.04/1.55  
% 9.04/1.55  % (1779)Memory used [KB]: 4989
% 9.04/1.55  % (1779)Time elapsed: 0.400 s
% 9.04/1.55  % (1779)------------------------------
% 9.04/1.55  % (1779)------------------------------
% 9.37/1.57  % (1780)Time limit reached!
% 9.37/1.57  % (1780)------------------------------
% 9.37/1.57  % (1780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.37/1.57  % (1780)Termination reason: Time limit
% 9.37/1.57  
% 9.37/1.57  % (1780)Memory used [KB]: 8315
% 9.37/1.57  % (1780)Time elapsed: 0.424 s
% 9.37/1.57  % (1780)------------------------------
% 9.37/1.57  % (1780)------------------------------
% 10.00/1.63  % (1706)Time limit reached!
% 10.00/1.63  % (1706)------------------------------
% 10.00/1.63  % (1706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.00/1.63  % (1706)Termination reason: Time limit
% 10.00/1.63  
% 10.00/1.63  % (1706)Memory used [KB]: 12281
% 10.00/1.63  % (1706)Time elapsed: 1.203 s
% 10.00/1.63  % (1706)------------------------------
% 10.00/1.63  % (1706)------------------------------
% 10.32/1.73  % (1711)Time limit reached!
% 10.32/1.73  % (1711)------------------------------
% 10.32/1.73  % (1711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.32/1.73  % (1711)Termination reason: Time limit
% 10.32/1.73  % (1711)Termination phase: Saturation
% 10.32/1.73  
% 10.32/1.73  % (1711)Memory used [KB]: 19573
% 10.32/1.73  % (1711)Time elapsed: 1.300 s
% 10.32/1.73  % (1711)------------------------------
% 10.32/1.73  % (1711)------------------------------
% 14.83/2.25  % (1727)Time limit reached!
% 14.83/2.25  % (1727)------------------------------
% 14.83/2.25  % (1727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.83/2.25  % (1727)Termination reason: Time limit
% 14.83/2.25  
% 14.83/2.25  % (1727)Memory used [KB]: 30703
% 14.83/2.25  % (1727)Time elapsed: 1.815 s
% 14.83/2.25  % (1727)------------------------------
% 14.83/2.25  % (1727)------------------------------
% 21.48/3.12  % (1726)Refutation found. Thanks to Tanya!
% 21.48/3.12  % SZS status Theorem for theBenchmark
% 21.48/3.12  % SZS output start Proof for theBenchmark
% 21.48/3.12  fof(f33889,plain,(
% 21.48/3.12    $false),
% 21.48/3.12    inference(subsumption_resolution,[],[f33888,f5242])).
% 21.48/3.12  fof(f5242,plain,(
% 21.48/3.12    ( ! [X74,X73] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X73,X74),k2_xboole_0(X74,X73))) )),
% 21.48/3.12    inference(superposition,[],[f186,f1155])).
% 21.48/3.12  fof(f1155,plain,(
% 21.48/3.12    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 21.48/3.12    inference(superposition,[],[f119,f87])).
% 21.48/3.12  fof(f87,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 21.48/3.12    inference(superposition,[],[f34,f35])).
% 21.48/3.12  fof(f35,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 21.48/3.12    inference(cnf_transformation,[],[f1])).
% 21.48/3.12  fof(f1,axiom,(
% 21.48/3.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 21.48/3.12  fof(f34,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f17])).
% 21.48/3.12  fof(f17,axiom,(
% 21.48/3.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 21.48/3.12  fof(f119,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 21.48/3.12    inference(superposition,[],[f31,f35])).
% 21.48/3.12  fof(f31,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f10])).
% 21.48/3.12  fof(f10,axiom,(
% 21.48/3.12    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 21.48/3.12  fof(f186,plain,(
% 21.48/3.12    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f175,f72])).
% 21.48/3.12  fof(f72,plain,(
% 21.48/3.12    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f48,f37])).
% 21.48/3.12  fof(f37,plain,(
% 21.48/3.12    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 21.48/3.12    inference(cnf_transformation,[],[f3])).
% 21.48/3.12  fof(f3,axiom,(
% 21.48/3.12    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 21.48/3.12  fof(f48,plain,(
% 21.48/3.12    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 21.48/3.12    inference(cnf_transformation,[],[f15])).
% 21.48/3.12  fof(f15,axiom,(
% 21.48/3.12    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 21.48/3.12  fof(f175,plain,(
% 21.48/3.12    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 21.48/3.12    inference(superposition,[],[f29,f59])).
% 21.48/3.12  fof(f59,plain,(
% 21.48/3.12    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f44,f46])).
% 21.48/3.12  fof(f46,plain,(
% 21.48/3.12    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 21.48/3.12    inference(cnf_transformation,[],[f26])).
% 21.48/3.12  fof(f26,plain,(
% 21.48/3.12    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 21.48/3.12    inference(ennf_transformation,[],[f16])).
% 21.48/3.12  fof(f16,axiom,(
% 21.48/3.12    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 21.48/3.12  fof(f44,plain,(
% 21.48/3.12    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f19])).
% 21.48/3.12  fof(f19,axiom,(
% 21.48/3.12    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).
% 21.48/3.12  fof(f29,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f12])).
% 21.48/3.12  fof(f12,axiom,(
% 21.48/3.12    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
% 21.48/3.12  fof(f33888,plain,(
% 21.48/3.12    k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))),
% 21.48/3.12    inference(forward_demodulation,[],[f33887,f33826])).
% 21.48/3.12  fof(f33826,plain,(
% 21.48/3.12    ( ! [X17,X18] : (k2_xboole_0(X18,X17) = k2_xboole_0(X18,k4_xboole_0(X17,X18))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f33553,f21461])).
% 21.48/3.12  fof(f21461,plain,(
% 21.48/3.12    ( ! [X99,X97,X98] : (k2_xboole_0(X99,X97) = k2_xboole_0(k2_xboole_0(X99,k4_xboole_0(X97,X98)),X97)) )),
% 21.48/3.12    inference(superposition,[],[f1046,f409])).
% 21.48/3.12  fof(f409,plain,(
% 21.48/3.12    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9) )),
% 21.48/3.12    inference(forward_demodulation,[],[f408,f286])).
% 21.48/3.12  fof(f286,plain,(
% 21.48/3.12    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.48/3.12    inference(superposition,[],[f247,f66])).
% 21.48/3.12  fof(f66,plain,(
% 21.48/3.12    ( ! [X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1) )),
% 21.48/3.12    inference(superposition,[],[f52,f35])).
% 21.48/3.12  fof(f52,plain,(
% 21.48/3.12    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 21.48/3.12    inference(backward_demodulation,[],[f50,f45])).
% 21.48/3.12  fof(f45,plain,(
% 21.48/3.12    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 21.48/3.12    inference(cnf_transformation,[],[f9])).
% 21.48/3.12  fof(f9,axiom,(
% 21.48/3.12    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 21.48/3.12  fof(f50,plain,(
% 21.48/3.12    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 21.48/3.12    inference(definition_unfolding,[],[f41,f40])).
% 21.48/3.12  fof(f40,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f2])).
% 21.48/3.12  fof(f2,axiom,(
% 21.48/3.12    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 21.48/3.12  fof(f41,plain,(
% 21.48/3.12    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.48/3.12    inference(cnf_transformation,[],[f14])).
% 21.48/3.12  fof(f14,axiom,(
% 21.48/3.12    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 21.48/3.12  fof(f247,plain,(
% 21.48/3.12    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 21.48/3.12    inference(superposition,[],[f34,f66])).
% 21.48/3.12  fof(f408,plain,(
% 21.48/3.12    ( ! [X10,X9] : (k4_xboole_0(X9,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 21.48/3.12    inference(forward_demodulation,[],[f382,f72])).
% 21.48/3.12  fof(f382,plain,(
% 21.48/3.12    ( ! [X10,X9] : (k4_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 21.48/3.12    inference(superposition,[],[f30,f286])).
% 21.48/3.12  fof(f30,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f13])).
% 21.48/3.12  fof(f13,axiom,(
% 21.48/3.12    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).
% 21.48/3.12  fof(f1046,plain,(
% 21.48/3.12    ( ! [X12,X13,X11] : (k2_xboole_0(X12,k2_xboole_0(X11,X13)) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f1004,f31])).
% 21.48/3.12  fof(f1004,plain,(
% 21.48/3.12    ( ! [X12,X13,X11] : (k2_xboole_0(k2_xboole_0(X12,X11),X13) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13))) )),
% 21.48/3.12    inference(superposition,[],[f113,f87])).
% 21.48/3.12  fof(f113,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) )),
% 21.48/3.12    inference(superposition,[],[f31,f35])).
% 21.48/3.12  fof(f33553,plain,(
% 21.48/3.12    ( ! [X17,X18] : (k2_xboole_0(X18,k4_xboole_0(X17,X18)) = k2_xboole_0(k2_xboole_0(X18,k4_xboole_0(X17,X18)),X17)) )),
% 21.48/3.12    inference(superposition,[],[f31575,f5898])).
% 21.48/3.12  fof(f5898,plain,(
% 21.48/3.12    ( ! [X116,X115] : (k3_xboole_0(X115,k2_xboole_0(X116,k4_xboole_0(X115,X116))) = X115) )),
% 21.48/3.12    inference(forward_demodulation,[],[f5796,f286])).
% 21.48/3.12  fof(f5796,plain,(
% 21.48/3.12    ( ! [X116,X115] : (k3_xboole_0(X115,k2_xboole_0(X116,k4_xboole_0(X115,X116))) = k4_xboole_0(X115,k1_xboole_0)) )),
% 21.48/3.12    inference(superposition,[],[f255,f1340])).
% 21.48/3.12  fof(f1340,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 21.48/3.12    inference(superposition,[],[f396,f59])).
% 21.48/3.12  fof(f396,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X5)) = k4_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 21.48/3.12    inference(backward_demodulation,[],[f176,f394])).
% 21.48/3.12  fof(f394,plain,(
% 21.48/3.12    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 21.48/3.12    inference(forward_demodulation,[],[f380,f242])).
% 21.48/3.12  fof(f242,plain,(
% 21.48/3.12    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.48/3.12    inference(forward_demodulation,[],[f239,f59])).
% 21.48/3.12  fof(f239,plain,(
% 21.48/3.12    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f232,f42])).
% 21.48/3.12  fof(f42,plain,(
% 21.48/3.12    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 21.48/3.12    inference(cnf_transformation,[],[f25])).
% 21.48/3.12  fof(f25,plain,(
% 21.48/3.12    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 21.48/3.12    inference(ennf_transformation,[],[f7])).
% 21.48/3.12  fof(f7,axiom,(
% 21.48/3.12    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 21.48/3.12  fof(f232,plain,(
% 21.48/3.12    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f57,f86])).
% 21.48/3.12  fof(f86,plain,(
% 21.48/3.12    ( ! [X2,X3] : (r1_tarski(X2,X2) | ~r1_tarski(X2,X3)) )),
% 21.48/3.12    inference(superposition,[],[f39,f38])).
% 21.48/3.12  fof(f38,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 21.48/3.12    inference(cnf_transformation,[],[f24])).
% 21.48/3.12  fof(f24,plain,(
% 21.48/3.12    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 21.48/3.12    inference(ennf_transformation,[],[f5])).
% 21.48/3.12  fof(f5,axiom,(
% 21.48/3.12    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 21.48/3.12  fof(f39,plain,(
% 21.48/3.12    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 21.48/3.12    inference(cnf_transformation,[],[f4])).
% 21.48/3.12  fof(f4,axiom,(
% 21.48/3.12    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 21.48/3.12  fof(f57,plain,(
% 21.48/3.12    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 21.48/3.12    inference(superposition,[],[f43,f35])).
% 21.48/3.12  fof(f43,plain,(
% 21.48/3.12    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f18])).
% 21.48/3.12  fof(f18,axiom,(
% 21.48/3.12    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 21.48/3.12  fof(f380,plain,(
% 21.48/3.12    ( ! [X6,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k2_xboole_0(X6,k1_xboole_0))) )),
% 21.48/3.12    inference(superposition,[],[f29,f286])).
% 21.48/3.12  fof(f176,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X3),X5) = k4_xboole_0(X3,k2_xboole_0(X4,X5))) )),
% 21.48/3.12    inference(superposition,[],[f29,f32])).
% 21.48/3.12  fof(f32,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 21.48/3.12    inference(cnf_transformation,[],[f8])).
% 21.48/3.12  fof(f8,axiom,(
% 21.48/3.12    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 21.48/3.12  fof(f255,plain,(
% 21.48/3.12    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 21.48/3.12    inference(backward_demodulation,[],[f153,f247])).
% 21.48/3.12  fof(f153,plain,(
% 21.48/3.12    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X2,X3))) )),
% 21.48/3.12    inference(superposition,[],[f28,f59])).
% 21.48/3.12  fof(f28,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 21.48/3.12    inference(cnf_transformation,[],[f11])).
% 21.48/3.12  fof(f11,axiom,(
% 21.48/3.12    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 21.48/3.12  fof(f31575,plain,(
% 21.48/3.12    ( ! [X54,X55] : (k2_xboole_0(X54,k3_xboole_0(X55,X54)) = X54) )),
% 21.48/3.12    inference(superposition,[],[f392,f31077])).
% 21.48/3.12  fof(f31077,plain,(
% 21.48/3.12    ( ! [X61,X60] : (k3_xboole_0(X60,X61) = k3_xboole_0(X61,X60)) )),
% 21.48/3.12    inference(subsumption_resolution,[],[f30855,f10262])).
% 21.48/3.12  fof(f10262,plain,(
% 21.48/3.12    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X13,X14),k3_xboole_0(X14,X13))) )),
% 21.48/3.12    inference(superposition,[],[f1659,f59])).
% 21.48/3.12  fof(f1659,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k3_xboole_0(X4,X5)) = k4_xboole_0(X3,k3_xboole_0(X5,X4))) )),
% 21.48/3.12    inference(superposition,[],[f197,f30])).
% 21.48/3.12  fof(f197,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X3,X5),k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X4,X5))) )),
% 21.48/3.12    inference(superposition,[],[f30,f35])).
% 21.48/3.12  fof(f30855,plain,(
% 21.48/3.12    ( ! [X61,X60] : (k1_xboole_0 != k4_xboole_0(k3_xboole_0(X61,X60),k3_xboole_0(X60,X61)) | k3_xboole_0(X60,X61) = k3_xboole_0(X61,X60)) )),
% 21.48/3.12    inference(superposition,[],[f33,f10262])).
% 21.48/3.12  fof(f33,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 21.48/3.12    inference(cnf_transformation,[],[f23])).
% 21.48/3.12  fof(f23,plain,(
% 21.48/3.12    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 21.48/3.12    inference(ennf_transformation,[],[f6])).
% 21.48/3.12  fof(f6,axiom,(
% 21.48/3.12    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 21.48/3.12  fof(f392,plain,(
% 21.48/3.12    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1) )),
% 21.48/3.12    inference(forward_demodulation,[],[f391,f286])).
% 21.48/3.12  fof(f391,plain,(
% 21.48/3.12    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f378,f45])).
% 21.48/3.12  fof(f378,plain,(
% 21.48/3.12    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 21.48/3.12    inference(superposition,[],[f28,f286])).
% 21.48/3.12  fof(f33887,plain,(
% 21.48/3.12    k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 21.48/3.12    inference(forward_demodulation,[],[f33886,f35])).
% 21.48/3.12  fof(f33886,plain,(
% 21.48/3.12    k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f33885,f11059])).
% 21.48/3.12  fof(f11059,plain,(
% 21.48/3.12    ( ! [X146,X147,X148] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X146,X147),X148),k2_xboole_0(X146,X148))) )),
% 21.48/3.12    inference(superposition,[],[f186,f1990])).
% 21.48/3.12  fof(f1990,plain,(
% 21.48/3.12    ( ! [X52,X53,X51] : (k2_xboole_0(X51,X53) = k2_xboole_0(X51,k2_xboole_0(k4_xboole_0(X51,X52),X53))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f1989,f806])).
% 21.48/3.12  fof(f806,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 21.48/3.12    inference(superposition,[],[f31,f252])).
% 21.48/3.12  fof(f252,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 21.48/3.12    inference(backward_demodulation,[],[f207,f247])).
% 21.48/3.12  fof(f207,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = X0) )),
% 21.48/3.12    inference(backward_demodulation,[],[f105,f194])).
% 21.48/3.12  fof(f194,plain,(
% 21.48/3.12    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))) )),
% 21.48/3.12    inference(superposition,[],[f30,f59])).
% 21.48/3.12  fof(f105,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = X0) )),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f39,f42])).
% 21.48/3.12  fof(f1989,plain,(
% 21.48/3.12    ( ! [X52,X53,X51] : (k2_xboole_0(k3_xboole_0(X51,X52),k2_xboole_0(k4_xboole_0(X51,X52),X53)) = k2_xboole_0(X51,k2_xboole_0(k4_xboole_0(X51,X52),X53))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f1914,f1856])).
% 21.48/3.12  fof(f1856,plain,(
% 21.48/3.12    ( ! [X24,X23,X25] : (k2_xboole_0(X23,X25) = k2_xboole_0(X23,k2_xboole_0(k3_xboole_0(X23,X24),X25))) )),
% 21.48/3.12    inference(superposition,[],[f113,f807])).
% 21.48/3.12  fof(f807,plain,(
% 21.48/3.12    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3) )),
% 21.48/3.12    inference(superposition,[],[f34,f252])).
% 21.48/3.12  fof(f1914,plain,(
% 21.48/3.12    ( ! [X52,X53,X51] : (k2_xboole_0(k3_xboole_0(X51,X52),k2_xboole_0(k4_xboole_0(X51,X52),X53)) = k2_xboole_0(X51,k2_xboole_0(k3_xboole_0(X51,X52),k2_xboole_0(k4_xboole_0(X51,X52),X53)))) )),
% 21.48/3.12    inference(superposition,[],[f122,f252])).
% 21.48/3.12  fof(f122,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 21.48/3.12    inference(superposition,[],[f34,f31])).
% 21.48/3.12  fof(f33885,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK1),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f33884,f286])).
% 21.48/3.12  fof(f33884,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f33883,f59])).
% 21.48/3.12  fof(f33883,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK0))),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f33882,f35])).
% 21.48/3.12  fof(f33882,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,sK1))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f33881,f31564])).
% 21.48/3.12  fof(f31564,plain,(
% 21.48/3.12    ( ! [X26,X24,X27,X25] : (k2_xboole_0(k4_xboole_0(X24,k4_xboole_0(X26,X25)),X27) = k2_xboole_0(k4_xboole_0(X24,X26),k2_xboole_0(k3_xboole_0(X25,X24),X27))) )),
% 21.48/3.12    inference(superposition,[],[f159,f31077])).
% 21.48/3.12  fof(f159,plain,(
% 21.48/3.12    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X0,X2),X3)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3)) )),
% 21.48/3.12    inference(superposition,[],[f31,f28])).
% 21.48/3.12  fof(f33881,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f33867,f119])).
% 21.48/3.12  fof(f33867,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(backward_demodulation,[],[f6244,f33826])).
% 21.48/3.12  fof(f6244,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f6241,f3461])).
% 21.48/3.12  fof(f3461,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,X1))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f3404,f81])).
% 21.48/3.12  fof(f81,plain,(
% 21.48/3.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f39,f38])).
% 21.48/3.12  fof(f3404,plain,(
% 21.48/3.12    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k4_xboole_0(X2,X1))) )),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f161,f140])).
% 21.48/3.12  fof(f140,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (~r1_tarski(X3,k4_xboole_0(X4,X5)) | k4_xboole_0(k3_xboole_0(X3,X4),X5) = X3) )),
% 21.48/3.12    inference(superposition,[],[f32,f38])).
% 21.48/3.12  fof(f161,plain,(
% 21.48/3.12    ( ! [X8,X7,X9] : (r1_tarski(k3_xboole_0(X7,X9),k4_xboole_0(X7,k4_xboole_0(X8,X9)))) )),
% 21.48/3.12    inference(superposition,[],[f57,f28])).
% 21.48/3.12  fof(f6241,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(backward_demodulation,[],[f228,f6239])).
% 21.48/3.12  fof(f6239,plain,(
% 21.48/3.12    ( ! [X35,X33,X34,X32] : (k4_xboole_0(k3_xboole_0(X32,X33),X35) = k4_xboole_0(k3_xboole_0(X32,X33),k2_xboole_0(X35,k4_xboole_0(X34,X32)))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f6180,f394])).
% 21.48/3.12  fof(f6180,plain,(
% 21.48/3.12    ( ! [X35,X33,X34,X32] : (k4_xboole_0(k3_xboole_0(X32,X33),k2_xboole_0(X35,k4_xboole_0(X34,X32))) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X32,X33),X35),k3_xboole_0(X32,X33))) )),
% 21.48/3.12    inference(superposition,[],[f29,f432])).
% 21.48/3.12  fof(f432,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X5,X3))) )),
% 21.48/3.12    inference(forward_demodulation,[],[f427,f409])).
% 21.48/3.12  fof(f427,plain,(
% 21.48/3.12    ( ! [X4,X5,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X5,X3)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X3,X4),X5),k3_xboole_0(X3,X4))) )),
% 21.48/3.12    inference(superposition,[],[f28,f81])).
% 21.48/3.12  fof(f228,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(forward_demodulation,[],[f224,f35])).
% 21.48/3.12  fof(f224,plain,(
% 21.48/3.12    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(unit_resulting_resolution,[],[f49,f33])).
% 21.48/3.12  fof(f49,plain,(
% 21.48/3.12    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 21.48/3.12    inference(definition_unfolding,[],[f27,f40,f40])).
% 21.48/3.12  fof(f27,plain,(
% 21.48/3.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 21.48/3.12    inference(cnf_transformation,[],[f22])).
% 21.48/3.12  fof(f22,plain,(
% 21.48/3.12    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.48/3.12    inference(ennf_transformation,[],[f21])).
% 21.48/3.12  fof(f21,negated_conjecture,(
% 21.48/3.12    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.48/3.12    inference(negated_conjecture,[],[f20])).
% 21.48/3.12  fof(f20,conjecture,(
% 21.48/3.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.48/3.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 21.48/3.12  % SZS output end Proof for theBenchmark
% 21.48/3.12  % (1726)------------------------------
% 21.48/3.12  % (1726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.48/3.12  % (1726)Termination reason: Refutation
% 21.48/3.12  
% 21.48/3.12  % (1726)Memory used [KB]: 35948
% 21.48/3.12  % (1726)Time elapsed: 2.698 s
% 21.48/3.12  % (1726)------------------------------
% 21.48/3.12  % (1726)------------------------------
% 21.48/3.13  % (1705)Success in time 2.751 s
%------------------------------------------------------------------------------
