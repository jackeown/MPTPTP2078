%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 (3538 expanded)
%              Number of leaves         :   13 (1268 expanded)
%              Depth                    :   33
%              Number of atoms          :   83 (3539 expanded)
%              Number of equality atoms :   82 (3538 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2146,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2144])).

fof(f2144,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f30,f2104])).

fof(f2104,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f2103,f264])).

fof(f264,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f251,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f251,plain,(
    ! [X1] : k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f219,f34])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f22,f21,f21])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f219,plain,(
    ! [X10] : k5_xboole_0(X10,k1_xboole_0) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),X10)) ),
    inference(superposition,[],[f29,f81])).

fof(f81,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f79,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f79,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f34,f43])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f2103,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2102,f1075])).

fof(f1075,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f84,f1070])).

fof(f1070,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f1055,f81])).

fof(f1055,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f620,f977])).

fof(f977,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8)) ),
    inference(forward_demodulation,[],[f976,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f976,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X8)))) ),
    inference(forward_demodulation,[],[f929,f84])).

fof(f929,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) ),
    inference(superposition,[],[f36,f312])).

fof(f312,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4)) ),
    inference(forward_demodulation,[],[f296,f270])).

fof(f270,plain,(
    ! [X10] : k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),X10)) = X10 ),
    inference(backward_demodulation,[],[f219,f264])).

fof(f296,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4)),k4_xboole_0(k1_xboole_0,X4))) ),
    inference(superposition,[],[f229,f35])).

fof(f229,plain,(
    ! [X10] : k5_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,k4_xboole_0(k1_xboole_0,X10))) = X10 ),
    inference(forward_demodulation,[],[f209,f83])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f43,f81])).

fof(f209,plain,(
    ! [X10] : k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,k4_xboole_0(k1_xboole_0,X10))) ),
    inference(superposition,[],[f29,f81])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f25,f21,f23])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f620,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X6,X6)) ),
    inference(backward_demodulation,[],[f90,f489])).

fof(f489,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3) ),
    inference(superposition,[],[f438,f29])).

fof(f438,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f31,f329])).

fof(f329,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f312,f84])).

fof(f90,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f56,f81])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f23,f23])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f32,f81])).

fof(f2102,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X5)) ),
    inference(forward_demodulation,[],[f2101,f1280])).

fof(f1280,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f1258,f81])).

fof(f1258,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f35,f1161])).

fof(f1161,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f1143,f56])).

fof(f1143,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(superposition,[],[f1075,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f2101,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X5)))) ),
    inference(forward_demodulation,[],[f2075,f37])).

fof(f2075,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5)) ),
    inference(superposition,[],[f1991,f35])).

fof(f1991,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f29,f1450])).

fof(f1450,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X23,X24) = k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25)) ),
    inference(forward_demodulation,[],[f1449,f264])).

fof(f1449,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25)) = k5_xboole_0(k4_xboole_0(X23,X24),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1448,f1075])).

fof(f1448,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25)) = k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X24))) ),
    inference(forward_demodulation,[],[f1415,f1280])).

fof(f1415,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25)) = k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X25,k4_xboole_0(X23,X24))))) ),
    inference(superposition,[],[f1238,f1279])).

fof(f1279,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6) ),
    inference(forward_demodulation,[],[f1257,f81])).

fof(f1257,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k4_xboole_0(X7,X6),k1_xboole_0) ),
    inference(superposition,[],[f56,f1161])).

fof(f1238,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f38,f37])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f21,f23])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f30,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f17,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:09:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (30417)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.46  % (30417)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f2146,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f2144])).
% 0.22/0.47  fof(f2144,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(superposition,[],[f30,f2104])).
% 0.22/0.47  fof(f2104,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f2103,f264])).
% 0.22/0.47  fof(f264,plain,(
% 0.22/0.47    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.22/0.47    inference(forward_demodulation,[],[f251,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f18,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.47  fof(f251,plain,(
% 0.22/0.47    ( ! [X1] : (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f219,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f22,f21,f21])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f219,plain,(
% 0.22/0.47    ( ! [X10] : (k5_xboole_0(X10,k1_xboole_0) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),X10))) )),
% 0.22/0.47    inference(superposition,[],[f29,f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 0.22/0.47    inference(forward_demodulation,[],[f79,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.22/0.47    inference(superposition,[],[f33,f31])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X6,k1_xboole_0))) )),
% 0.22/0.47    inference(superposition,[],[f34,f43])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f26,f21])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.47  fof(f2103,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f2102,f1075])).
% 0.22/0.47  fof(f1075,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f84,f1070])).
% 0.22/0.47  fof(f1070,plain,(
% 0.22/0.47    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1055,f81])).
% 0.22/0.47  fof(f1055,plain,(
% 0.22/0.47    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 0.22/0.47    inference(superposition,[],[f620,f977])).
% 0.22/0.47  fof(f977,plain,(
% 0.22/0.47    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f976,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f24,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.47  fof(f976,plain,(
% 0.22/0.47    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X8))))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f929,f84])).
% 0.22/0.47  fof(f929,plain,(
% 0.22/0.47    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8)))) )),
% 0.22/0.47    inference(superposition,[],[f36,f312])).
% 0.22/0.47  fof(f312,plain,(
% 0.22/0.47    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f296,f270])).
% 0.22/0.47  fof(f270,plain,(
% 0.22/0.47    ( ! [X10] : (k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),X10)) = X10) )),
% 0.22/0.47    inference(backward_demodulation,[],[f219,f264])).
% 0.22/0.47  fof(f296,plain,(
% 0.22/0.47    ( ! [X4] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4)),k4_xboole_0(k1_xboole_0,X4)))) )),
% 0.22/0.47    inference(superposition,[],[f229,f35])).
% 0.22/0.47  fof(f229,plain,(
% 0.22/0.47    ( ! [X10] : (k5_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,k4_xboole_0(k1_xboole_0,X10))) = X10) )),
% 0.22/0.47    inference(forward_demodulation,[],[f209,f83])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.47    inference(backward_demodulation,[],[f43,f81])).
% 0.22/0.47  fof(f209,plain,(
% 0.22/0.47    ( ! [X10] : (k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,k4_xboole_0(k1_xboole_0,X10)))) )),
% 0.22/0.47    inference(superposition,[],[f29,f81])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f25,f21,f23])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.47  fof(f620,plain,(
% 0.22/0.47    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X6,X6))) )),
% 0.22/0.47    inference(backward_demodulation,[],[f90,f489])).
% 0.22/0.47  fof(f489,plain,(
% 0.22/0.47    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) )),
% 0.22/0.47    inference(superposition,[],[f438,f29])).
% 0.22/0.47  fof(f438,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.22/0.47    inference(superposition,[],[f31,f329])).
% 0.22/0.47  fof(f329,plain,(
% 0.22/0.47    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1)) )),
% 0.22/0.47    inference(superposition,[],[f312,f84])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))) )),
% 0.22/0.47    inference(superposition,[],[f56,f81])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.47    inference(superposition,[],[f35,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f19,f23,f23])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(superposition,[],[f32,f81])).
% 0.22/0.47  fof(f2102,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X5))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f2101,f1280])).
% 0.22/0.47  fof(f1280,plain,(
% 0.22/0.47    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1258,f81])).
% 0.22/0.47  fof(f1258,plain,(
% 0.22/0.47    ( ! [X8,X9] : (k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(X8,k4_xboole_0(X9,X8))) )),
% 0.22/0.47    inference(superposition,[],[f35,f1161])).
% 0.22/0.47  fof(f1161,plain,(
% 0.22/0.47    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1143,f56])).
% 0.22/0.47  fof(f1143,plain,(
% 0.22/0.47    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) )),
% 0.22/0.47    inference(superposition,[],[f1075,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f27,f23,f23])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.47  fof(f2101,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,X5))))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f2075,f37])).
% 0.22/0.47  fof(f2075,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5))) )),
% 0.22/0.47    inference(superposition,[],[f1991,f35])).
% 0.22/0.47  fof(f1991,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(backward_demodulation,[],[f29,f1450])).
% 0.22/0.47  fof(f1450,plain,(
% 0.22/0.47    ( ! [X24,X23,X25] : (k4_xboole_0(X23,X24) = k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1449,f264])).
% 0.22/0.47  fof(f1449,plain,(
% 0.22/0.47    ( ! [X24,X23,X25] : (k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25)) = k5_xboole_0(k4_xboole_0(X23,X24),k1_xboole_0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1448,f1075])).
% 0.22/0.47  fof(f1448,plain,(
% 0.22/0.47    ( ! [X24,X23,X25] : (k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25)) = k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X24)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1415,f1280])).
% 0.22/0.47  fof(f1415,plain,(
% 0.22/0.47    ( ! [X24,X23,X25] : (k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X25)) = k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X25,k4_xboole_0(X23,X24)))))) )),
% 0.22/0.47    inference(superposition,[],[f1238,f1279])).
% 0.22/0.47  fof(f1279,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1257,f81])).
% 0.22/0.47  fof(f1257,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k4_xboole_0(X7,X6),k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f56,f1161])).
% 0.22/0.47  fof(f1238,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1)))))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f38,f37])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f28,f21,f23])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    inference(definition_unfolding,[],[f17,f23])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f12])).
% 0.22/0.47  fof(f12,conjecture,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (30417)------------------------------
% 0.22/0.47  % (30417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (30417)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (30417)Memory used [KB]: 2558
% 0.22/0.47  % (30417)Time elapsed: 0.046 s
% 0.22/0.47  % (30417)------------------------------
% 0.22/0.47  % (30417)------------------------------
% 0.22/0.47  % (30404)Success in time 0.107 s
%------------------------------------------------------------------------------
