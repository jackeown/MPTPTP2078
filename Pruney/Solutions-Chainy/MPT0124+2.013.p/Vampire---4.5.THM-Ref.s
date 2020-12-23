%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:00 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 906 expanded)
%              Number of leaves         :   13 ( 317 expanded)
%              Depth                    :   21
%              Number of atoms          :   98 (1000 expanded)
%              Number of equality atoms :   77 ( 866 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1239,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1238])).

fof(f1238,plain,(
    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f955,f1197])).

fof(f1197,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1153,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1153,plain,(
    ! [X26] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X26,sK1)) ),
    inference(forward_demodulation,[],[f1127,f973])).

fof(f973,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f972,f83])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f82,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(backward_demodulation,[],[f51,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f51,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X2) ),
    inference(superposition,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f972,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f941,f67])).

fof(f941,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[],[f46,f36])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f44,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f24,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1127,plain,(
    ! [X26] : k4_xboole_0(sK2,k4_xboole_0(X26,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(backward_demodulation,[],[f697,f1121])).

fof(f1121,plain,(
    ! [X15] : k4_xboole_0(sK2,sK2) = k4_xboole_0(k4_xboole_0(X15,sK1),X15) ),
    inference(backward_demodulation,[],[f997,f1119])).

fof(f1119,plain,(
    ! [X1] : k4_xboole_0(sK2,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),X1),k4_xboole_0(sK2,sK2)) ),
    inference(backward_demodulation,[],[f850,f1115])).

fof(f1115,plain,(
    ! [X36,X34] : k4_xboole_0(X34,X34) = k4_xboole_0(k4_xboole_0(X34,X34),X36) ),
    inference(backward_demodulation,[],[f1042,f1114])).

fof(f1114,plain,(
    ! [X47,X48,X46] : k4_xboole_0(X46,k4_xboole_0(k4_xboole_0(X47,X46),X48)) = X46 ),
    inference(forward_demodulation,[],[f1113,f1024])).

fof(f1024,plain,(
    ! [X6] : k5_xboole_0(X6,k4_xboole_0(X6,X6)) = X6 ),
    inference(superposition,[],[f49,f973])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f48,f37])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(resolution,[],[f39,f35])).

fof(f1113,plain,(
    ! [X47,X48,X46] : k4_xboole_0(X46,k4_xboole_0(k4_xboole_0(X47,X46),X48)) = k5_xboole_0(X46,k4_xboole_0(X46,X46)) ),
    inference(forward_demodulation,[],[f1046,f973])).

fof(f1046,plain,(
    ! [X47,X48,X46] : k4_xboole_0(X46,k4_xboole_0(k4_xboole_0(X47,X46),X48)) = k5_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(X48,X46)))) ),
    inference(superposition,[],[f46,f973])).

fof(f1042,plain,(
    ! [X35,X36,X34] : k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X35,X34),X36))) = k4_xboole_0(k4_xboole_0(X34,X34),X36) ),
    inference(superposition,[],[f41,f973])).

fof(f850,plain,(
    ! [X1] : k4_xboole_0(sK2,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),X1),k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(X1,sK1),X1))) ),
    inference(resolution,[],[f848,f39])).

fof(f848,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k4_xboole_0(X0,sK1),X0),k4_xboole_0(sK2,sK2)) ),
    inference(forward_demodulation,[],[f834,f116])).

fof(f116,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f99,f67])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f67,f36])).

fof(f834,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)),k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[],[f676,f392])).

fof(f392,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,sK1),k4_xboole_0(X7,sK2)) = k4_xboole_0(k4_xboole_0(X8,sK1),X7) ),
    inference(forward_demodulation,[],[f375,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f31,f24])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f375,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,sK1),k4_xboole_0(X7,sK2)) = k4_xboole_0(X8,k5_xboole_0(sK1,k4_xboole_0(X7,sK1))) ),
    inference(superposition,[],[f42,f232])).

fof(f232,plain,(
    ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK2),sK1) = k4_xboole_0(X0,sK1) ),
    inference(superposition,[],[f42,f47])).

fof(f47,plain,(
    sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f39,f20])).

fof(f20,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f676,plain,(
    ! [X52,X53] : r1_tarski(k4_xboole_0(k4_xboole_0(X52,sK1),k4_xboole_0(k4_xboole_0(X52,sK1),X53)),k4_xboole_0(X53,sK2)) ),
    inference(superposition,[],[f50,f392])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f35,f36])).

fof(f997,plain,(
    ! [X15] : k4_xboole_0(k4_xboole_0(X15,sK1),X15) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(sK2,sK2)) ),
    inference(forward_demodulation,[],[f996,f392])).

fof(f996,plain,(
    ! [X15] : k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(sK2,sK2)) ),
    inference(forward_demodulation,[],[f995,f975])).

fof(f975,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(backward_demodulation,[],[f796,f973])).

fof(f796,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f737,f36])).

fof(f737,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = X0 ),
    inference(superposition,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f27,f24,f25])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f25,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f995,plain,(
    ! [X15] : k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK1))))) ),
    inference(forward_demodulation,[],[f994,f41])).

fof(f994,plain,(
    ! [X15] : k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X15,sK1))),k4_xboole_0(X15,sK1))) ),
    inference(forward_demodulation,[],[f948,f265])).

fof(f265,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f41,f36])).

fof(f948,plain,(
    ! [X15] : k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(sK2,k4_xboole_0(X15,sK1))))) ),
    inference(superposition,[],[f46,f697])).

fof(f697,plain,(
    ! [X26] : k4_xboole_0(sK2,k4_xboole_0(X26,sK1)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X26,sK1),X26)) ),
    inference(forward_demodulation,[],[f661,f116])).

fof(f661,plain,(
    ! [X26] : k4_xboole_0(sK2,k4_xboole_0(X26,sK1)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X26,sK1),k4_xboole_0(X26,sK1))) ),
    inference(superposition,[],[f67,f392])).

fof(f955,plain,(
    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f45,f46])).

fof(f45,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f34,f41])).

fof(f34,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f24,f25])).

fof(f21,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:31:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (6645)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (6637)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (6633)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (6635)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (6646)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (6636)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (6640)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (6638)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6642)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (6641)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.53  % (6639)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.53  % (6644)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (6634)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.53  % (6647)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.37/0.54  % (6648)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.37/0.55  % (6643)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.37/0.55  % (6643)Refutation not found, incomplete strategy% (6643)------------------------------
% 1.37/0.55  % (6643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (6643)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (6643)Memory used [KB]: 10618
% 1.37/0.55  % (6643)Time elapsed: 0.131 s
% 1.37/0.55  % (6643)------------------------------
% 1.37/0.55  % (6643)------------------------------
% 1.37/0.55  % (6632)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.56/0.57  % (6649)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.56/0.61  % (6633)Refutation found. Thanks to Tanya!
% 1.56/0.61  % SZS status Theorem for theBenchmark
% 1.56/0.61  % SZS output start Proof for theBenchmark
% 1.56/0.61  fof(f1239,plain,(
% 1.56/0.61    $false),
% 1.56/0.61    inference(trivial_inequality_removal,[],[f1238])).
% 1.56/0.61  fof(f1238,plain,(
% 1.56/0.61    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)),
% 1.56/0.61    inference(backward_demodulation,[],[f955,f1197])).
% 1.56/0.61  fof(f1197,plain,(
% 1.56/0.61    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.56/0.61    inference(superposition,[],[f1153,f36])).
% 1.56/0.61  fof(f36,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f23,f25,f25])).
% 1.56/0.61  fof(f25,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f8])).
% 1.56/0.61  fof(f8,axiom,(
% 1.56/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.56/0.61  fof(f23,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f1])).
% 1.56/0.61  fof(f1,axiom,(
% 1.56/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.56/0.61  fof(f1153,plain,(
% 1.56/0.61    ( ! [X26] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X26,sK1))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f1127,f973])).
% 1.56/0.61  fof(f973,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 1.56/0.61    inference(forward_demodulation,[],[f972,f83])).
% 1.56/0.61  fof(f83,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 1.56/0.61    inference(resolution,[],[f82,f39])).
% 1.56/0.61  fof(f39,plain,(
% 1.56/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 1.56/0.61    inference(definition_unfolding,[],[f28,f24])).
% 1.56/0.61  fof(f24,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f12])).
% 1.56/0.61  fof(f12,axiom,(
% 1.56/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.56/0.61  fof(f28,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f16])).
% 1.56/0.61  fof(f16,plain,(
% 1.56/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.56/0.61    inference(ennf_transformation,[],[f3])).
% 1.56/0.61  fof(f3,axiom,(
% 1.56/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.56/0.61  fof(f82,plain,(
% 1.56/0.61    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 1.56/0.61    inference(backward_demodulation,[],[f51,f67])).
% 1.56/0.61  fof(f67,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.56/0.61    inference(superposition,[],[f37,f36])).
% 1.56/0.61  fof(f37,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f26,f25])).
% 1.56/0.61  fof(f26,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f7])).
% 1.56/0.61  fof(f7,axiom,(
% 1.56/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.56/0.61  fof(f51,plain,(
% 1.56/0.61    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X2)) )),
% 1.56/0.61    inference(superposition,[],[f35,f36])).
% 1.56/0.61  fof(f35,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.56/0.61    inference(definition_unfolding,[],[f22,f25])).
% 1.56/0.61  fof(f22,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f4])).
% 1.56/0.61  fof(f4,axiom,(
% 1.56/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.56/0.61  fof(f972,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f941,f67])).
% 1.56/0.61  fof(f941,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) )),
% 1.56/0.61    inference(superposition,[],[f46,f36])).
% 1.56/0.61  fof(f46,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1)))))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f44,f41])).
% 1.56/0.61  fof(f41,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.56/0.61    inference(definition_unfolding,[],[f30,f25,f25])).
% 1.56/0.61  fof(f30,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f9])).
% 1.56/0.61  fof(f9,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.56/0.61  fof(f44,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1)))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f33,f24,f25])).
% 1.56/0.61  fof(f33,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f11])).
% 1.56/0.61  fof(f11,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.56/0.61  fof(f1127,plain,(
% 1.56/0.61    ( ! [X26] : (k4_xboole_0(sK2,k4_xboole_0(X26,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) )),
% 1.56/0.61    inference(backward_demodulation,[],[f697,f1121])).
% 1.56/0.61  fof(f1121,plain,(
% 1.56/0.61    ( ! [X15] : (k4_xboole_0(sK2,sK2) = k4_xboole_0(k4_xboole_0(X15,sK1),X15)) )),
% 1.56/0.61    inference(backward_demodulation,[],[f997,f1119])).
% 1.56/0.61  fof(f1119,plain,(
% 1.56/0.61    ( ! [X1] : (k4_xboole_0(sK2,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),X1),k4_xboole_0(sK2,sK2))) )),
% 1.56/0.61    inference(backward_demodulation,[],[f850,f1115])).
% 1.56/0.61  fof(f1115,plain,(
% 1.56/0.61    ( ! [X36,X34] : (k4_xboole_0(X34,X34) = k4_xboole_0(k4_xboole_0(X34,X34),X36)) )),
% 1.56/0.61    inference(backward_demodulation,[],[f1042,f1114])).
% 1.56/0.61  fof(f1114,plain,(
% 1.56/0.61    ( ! [X47,X48,X46] : (k4_xboole_0(X46,k4_xboole_0(k4_xboole_0(X47,X46),X48)) = X46) )),
% 1.56/0.61    inference(forward_demodulation,[],[f1113,f1024])).
% 1.56/0.61  fof(f1024,plain,(
% 1.56/0.61    ( ! [X6] : (k5_xboole_0(X6,k4_xboole_0(X6,X6)) = X6) )),
% 1.56/0.61    inference(superposition,[],[f49,f973])).
% 1.56/0.61  fof(f49,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.56/0.61    inference(forward_demodulation,[],[f48,f37])).
% 1.56/0.61  fof(f48,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 1.56/0.61    inference(resolution,[],[f39,f35])).
% 1.56/0.61  fof(f1113,plain,(
% 1.56/0.61    ( ! [X47,X48,X46] : (k4_xboole_0(X46,k4_xboole_0(k4_xboole_0(X47,X46),X48)) = k5_xboole_0(X46,k4_xboole_0(X46,X46))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f1046,f973])).
% 1.56/0.61  fof(f1046,plain,(
% 1.56/0.61    ( ! [X47,X48,X46] : (k4_xboole_0(X46,k4_xboole_0(k4_xboole_0(X47,X46),X48)) = k5_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(X48,X46))))) )),
% 1.56/0.61    inference(superposition,[],[f46,f973])).
% 1.56/0.61  fof(f1042,plain,(
% 1.56/0.61    ( ! [X35,X36,X34] : (k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X35,X34),X36))) = k4_xboole_0(k4_xboole_0(X34,X34),X36)) )),
% 1.56/0.61    inference(superposition,[],[f41,f973])).
% 1.56/0.61  fof(f850,plain,(
% 1.56/0.61    ( ! [X1] : (k4_xboole_0(sK2,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),X1),k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(X1,sK1),X1)))) )),
% 1.56/0.61    inference(resolution,[],[f848,f39])).
% 1.56/0.61  fof(f848,plain,(
% 1.56/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(k4_xboole_0(X0,sK1),X0),k4_xboole_0(sK2,sK2))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f834,f116])).
% 1.56/0.61  fof(f116,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f99,f67])).
% 1.56/0.61  fof(f99,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 1.56/0.61    inference(superposition,[],[f67,f36])).
% 1.56/0.61  fof(f834,plain,(
% 1.56/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)),k4_xboole_0(sK2,sK2))) )),
% 1.56/0.61    inference(superposition,[],[f676,f392])).
% 1.56/0.61  fof(f392,plain,(
% 1.56/0.61    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,sK1),k4_xboole_0(X7,sK2)) = k4_xboole_0(k4_xboole_0(X8,sK1),X7)) )),
% 1.56/0.61    inference(forward_demodulation,[],[f375,f42])).
% 1.56/0.61  fof(f42,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f31,f24])).
% 1.56/0.61  fof(f31,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f5])).
% 1.56/0.61  fof(f5,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.56/0.61  fof(f375,plain,(
% 1.56/0.61    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,sK1),k4_xboole_0(X7,sK2)) = k4_xboole_0(X8,k5_xboole_0(sK1,k4_xboole_0(X7,sK1)))) )),
% 1.56/0.61    inference(superposition,[],[f42,f232])).
% 1.56/0.61  fof(f232,plain,(
% 1.56/0.61    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,sK2),sK1) = k4_xboole_0(X0,sK1)) )),
% 1.56/0.61    inference(superposition,[],[f42,f47])).
% 1.56/0.61  fof(f47,plain,(
% 1.56/0.61    sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 1.56/0.61    inference(resolution,[],[f39,f20])).
% 1.56/0.61  fof(f20,plain,(
% 1.56/0.61    r1_tarski(sK2,sK1)),
% 1.56/0.61    inference(cnf_transformation,[],[f19])).
% 1.56/0.61  fof(f19,plain,(
% 1.56/0.61    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 1.56/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 1.56/0.61  fof(f18,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 1.56/0.61    introduced(choice_axiom,[])).
% 1.56/0.61  fof(f15,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 1.56/0.61    inference(ennf_transformation,[],[f14])).
% 1.56/0.61  fof(f14,negated_conjecture,(
% 1.56/0.61    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 1.56/0.61    inference(negated_conjecture,[],[f13])).
% 1.56/0.61  fof(f13,conjecture,(
% 1.56/0.61    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 1.56/0.61  fof(f676,plain,(
% 1.56/0.61    ( ! [X52,X53] : (r1_tarski(k4_xboole_0(k4_xboole_0(X52,sK1),k4_xboole_0(k4_xboole_0(X52,sK1),X53)),k4_xboole_0(X53,sK2))) )),
% 1.56/0.61    inference(superposition,[],[f50,f392])).
% 1.56/0.61  fof(f50,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 1.56/0.61    inference(superposition,[],[f35,f36])).
% 1.56/0.61  fof(f997,plain,(
% 1.56/0.61    ( ! [X15] : (k4_xboole_0(k4_xboole_0(X15,sK1),X15) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(sK2,sK2))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f996,f392])).
% 1.56/0.61  fof(f996,plain,(
% 1.56/0.61    ( ! [X15] : (k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(sK2,sK2))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f995,f975])).
% 1.56/0.61  fof(f975,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0) )),
% 1.56/0.61    inference(backward_demodulation,[],[f796,f973])).
% 1.56/0.61  fof(f796,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0) )),
% 1.56/0.61    inference(forward_demodulation,[],[f737,f36])).
% 1.56/0.61  fof(f737,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = X0) )),
% 1.56/0.61    inference(superposition,[],[f43,f38])).
% 1.56/0.61  fof(f38,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 1.56/0.61    inference(definition_unfolding,[],[f27,f24,f25])).
% 1.56/0.61  fof(f27,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.56/0.61    inference(cnf_transformation,[],[f10])).
% 1.56/0.61  fof(f10,axiom,(
% 1.56/0.61    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.56/0.61  fof(f43,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f32,f25,f24])).
% 1.56/0.61  fof(f32,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f2])).
% 1.56/0.61  fof(f2,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 1.56/0.61  fof(f995,plain,(
% 1.56/0.61    ( ! [X15] : (k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK1)))))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f994,f41])).
% 1.56/0.61  fof(f994,plain,(
% 1.56/0.61    ( ! [X15] : (k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X15,sK1))),k4_xboole_0(X15,sK1)))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f948,f265])).
% 1.56/0.61  fof(f265,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 1.56/0.61    inference(superposition,[],[f41,f36])).
% 1.56/0.61  fof(f948,plain,(
% 1.56/0.61    ( ! [X15] : (k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(X15,sK2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X15,sK1),X15),k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(k4_xboole_0(X15,sK1),k4_xboole_0(sK2,k4_xboole_0(X15,sK1)))))) )),
% 1.56/0.61    inference(superposition,[],[f46,f697])).
% 1.56/0.61  fof(f697,plain,(
% 1.56/0.61    ( ! [X26] : (k4_xboole_0(sK2,k4_xboole_0(X26,sK1)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X26,sK1),X26))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f661,f116])).
% 1.56/0.61  fof(f661,plain,(
% 1.56/0.61    ( ! [X26] : (k4_xboole_0(sK2,k4_xboole_0(X26,sK1)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X26,sK1),k4_xboole_0(X26,sK1)))) )),
% 1.56/0.61    inference(superposition,[],[f67,f392])).
% 1.56/0.61  fof(f955,plain,(
% 1.56/0.61    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.56/0.61    inference(superposition,[],[f45,f46])).
% 1.56/0.61  fof(f45,plain,(
% 1.56/0.61    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))),
% 1.56/0.61    inference(backward_demodulation,[],[f34,f41])).
% 1.56/0.61  fof(f34,plain,(
% 1.56/0.61    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 1.56/0.61    inference(definition_unfolding,[],[f21,f24,f25])).
% 1.56/0.61  fof(f21,plain,(
% 1.56/0.61    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.56/0.61    inference(cnf_transformation,[],[f19])).
% 1.56/0.61  % SZS output end Proof for theBenchmark
% 1.56/0.61  % (6633)------------------------------
% 1.56/0.61  % (6633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (6633)Termination reason: Refutation
% 1.56/0.61  
% 1.56/0.61  % (6633)Memory used [KB]: 2558
% 1.56/0.61  % (6633)Time elapsed: 0.194 s
% 1.56/0.61  % (6633)------------------------------
% 1.56/0.61  % (6633)------------------------------
% 1.56/0.61  % (6631)Success in time 0.247 s
%------------------------------------------------------------------------------
