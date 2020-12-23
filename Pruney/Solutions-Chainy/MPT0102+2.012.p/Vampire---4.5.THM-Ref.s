%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:57 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 768 expanded)
%              Number of leaves         :   14 ( 234 expanded)
%              Depth                    :   26
%              Number of atoms          :  124 ( 917 expanded)
%              Number of equality atoms :   88 ( 686 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10034,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10033,f57])).

fof(f57,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f56,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f53,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f35,f48])).

fof(f48,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f27,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f39,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f10033,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f10032,f567])).

fof(f567,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f184,f29])).

fof(f184,plain,(
    ! [X6,X8,X7] : k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8)) ),
    inference(forward_demodulation,[],[f174,f48])).

fof(f174,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8)) ),
    inference(superposition,[],[f36,f146])).

fof(f146,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f128,f48])).

fof(f128,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f36,f42])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f10032,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f10030,f36])).

fof(f10030,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1919,f9896])).

fof(f9896,plain,(
    ! [X59,X60,X58] : k4_xboole_0(X60,k2_xboole_0(X59,X58)) = k4_xboole_0(k2_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X59,X58)) ),
    inference(superposition,[],[f147,f7663])).

fof(f7663,plain,(
    ! [X45,X44] : k2_xboole_0(X44,X45) = k2_xboole_0(k4_xboole_0(X45,X44),X44) ),
    inference(forward_demodulation,[],[f7523,f5932])).

fof(f5932,plain,(
    ! [X70,X68,X69] : k2_xboole_0(X70,X68) = k2_xboole_0(k2_xboole_0(X70,X68),k4_xboole_0(X68,X69)) ),
    inference(forward_demodulation,[],[f5736,f26])).

fof(f5736,plain,(
    ! [X70,X68,X69] : k2_xboole_0(X70,X68) = k2_xboole_0(k2_xboole_0(X70,X68),k4_xboole_0(k4_xboole_0(X68,X69),k1_xboole_0)) ),
    inference(superposition,[],[f3603,f3480])).

fof(f3480,plain,(
    ! [X80,X81,X79] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X79,X80),k2_xboole_0(X81,X79)) ),
    inference(superposition,[],[f567,f3312])).

fof(f3312,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f3289,f33])).

fof(f3289,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f3253,f57])).

fof(f3253,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f344,f165])).

fof(f165,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f146,f29])).

fof(f344,plain,(
    ! [X19,X20,X18] : r1_tarski(k4_xboole_0(X18,X19),k2_xboole_0(X20,k4_xboole_0(X18,k2_xboole_0(X19,X20)))) ),
    inference(superposition,[],[f325,f36])).

fof(f325,plain,(
    ! [X8,X7] : r1_tarski(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    inference(trivial_inequality_removal,[],[f315])).

fof(f315,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8))) ) ),
    inference(superposition,[],[f35,f136])).

fof(f136,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f36,f42])).

fof(f3603,plain,(
    ! [X31,X32] : k2_xboole_0(X31,k4_xboole_0(X32,k4_xboole_0(X32,X31))) = X31 ),
    inference(superposition,[],[f3447,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f30,f30])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3447,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f3312,f29])).

fof(f7523,plain,(
    ! [X45,X44] : k2_xboole_0(k4_xboole_0(X45,X44),X44) = k2_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X45,X44)) ),
    inference(superposition,[],[f5848,f232])).

fof(f232,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)) = X10 ),
    inference(forward_demodulation,[],[f231,f26])).

fof(f231,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)) = k4_xboole_0(X10,k1_xboole_0) ),
    inference(forward_demodulation,[],[f196,f146])).

fof(f196,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)) ),
    inference(superposition,[],[f40,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f5848,plain,(
    ! [X48,X49] : k2_xboole_0(X48,X49) = k2_xboole_0(X49,k4_xboole_0(X48,X49)) ),
    inference(forward_demodulation,[],[f5847,f3104])).

fof(f3104,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f3077,f33])).

fof(f3077,plain,(
    ! [X47,X46] : r1_tarski(k2_xboole_0(X47,k4_xboole_0(X46,X47)),k2_xboole_0(X46,X47)) ),
    inference(forward_demodulation,[],[f3010,f254])).

fof(f254,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f187,f33])).

fof(f187,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f183,f29])).

fof(f183,plain,(
    ! [X4,X5] : r1_tarski(X4,k2_xboole_0(X4,X5)) ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X4,k2_xboole_0(X4,X5)) ) ),
    inference(superposition,[],[f35,f146])).

fof(f3010,plain,(
    ! [X47,X46] : r1_tarski(k2_xboole_0(X47,k4_xboole_0(X46,X47)),k2_xboole_0(X47,k2_xboole_0(X46,X47))) ),
    inference(superposition,[],[f2952,f31])).

fof(f2952,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(X50,X51)) ),
    inference(forward_demodulation,[],[f2951,f26])).

fof(f2951,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2950,f56])).

fof(f2950,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f2949,f29])).

fof(f2949,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2948,f766])).

fof(f766,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f294,f29])).

fof(f294,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X9),X11)) ),
    inference(forward_demodulation,[],[f284,f48])).

fof(f284,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X9),X11)) = k4_xboole_0(k1_xboole_0,X11) ),
    inference(superposition,[],[f36,f165])).

fof(f2948,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k4_xboole_0(X51,k2_xboole_0(X50,k2_xboole_0(X50,X51))))) ),
    inference(forward_demodulation,[],[f2947,f36])).

fof(f2947,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k4_xboole_0(k4_xboole_0(X51,X50),k2_xboole_0(X50,X51)))) ),
    inference(forward_demodulation,[],[f2946,f148])).

fof(f148,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(X8,k2_xboole_0(X7,X9)) ),
    inference(forward_demodulation,[],[f130,f36])).

fof(f130,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k4_xboole_0(X8,X7),X9) ),
    inference(superposition,[],[f36,f66])).

fof(f2946,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k4_xboole_0(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(X50,X51)))) ),
    inference(forward_demodulation,[],[f2809,f29])).

fof(f2809,plain,(
    ! [X50,X51] : r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(X50,X51)),k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0))) ),
    inference(superposition,[],[f338,f306])).

fof(f306,plain,(
    ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X14,X15),k2_xboole_0(X14,k4_xboole_0(X15,X14))) ),
    inference(superposition,[],[f136,f66])).

fof(f338,plain,(
    ! [X8,X7] : r1_tarski(X7,k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,k4_xboole_0(X8,X7)))) ),
    inference(superposition,[],[f325,f40])).

fof(f5847,plain,(
    ! [X48,X49] : k2_xboole_0(X49,k4_xboole_0(X48,X49)) = k2_xboole_0(k2_xboole_0(X49,k4_xboole_0(X48,X49)),k2_xboole_0(X48,X49)) ),
    inference(forward_demodulation,[],[f5727,f26])).

fof(f5727,plain,(
    ! [X48,X49] : k2_xboole_0(X49,k4_xboole_0(X48,X49)) = k2_xboole_0(k2_xboole_0(X49,k4_xboole_0(X48,X49)),k4_xboole_0(k2_xboole_0(X48,X49),k1_xboole_0)) ),
    inference(superposition,[],[f3603,f305])).

fof(f305,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f136,f31])).

fof(f147,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f129,f36])).

fof(f129,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6) ),
    inference(superposition,[],[f36,f31])).

fof(f1919,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f533,f29])).

fof(f533,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f532,f40])).

fof(f532,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f38,f509])).

fof(f509,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6)) ),
    inference(superposition,[],[f36,f230])).

fof(f230,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = X9 ),
    inference(forward_demodulation,[],[f229,f26])).

fof(f229,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k4_xboole_0(X9,k1_xboole_0) ),
    inference(forward_demodulation,[],[f195,f165])).

fof(f195,plain,(
    ! [X8,X9] : k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f40,f31])).

fof(f38,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f24,f30,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % WCLimit    : 600
% 0.19/0.33  % DateTime   : Tue Dec  1 13:41:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.43  % (23778)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.44  % (23770)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (23767)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (23777)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (23780)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (23776)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (23768)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (23766)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (23765)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (23763)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (23769)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (23775)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (23772)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (23773)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (23774)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (23774)Refutation not found, incomplete strategy% (23774)------------------------------
% 0.20/0.49  % (23774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23774)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23774)Memory used [KB]: 10490
% 0.20/0.49  % (23774)Time elapsed: 0.078 s
% 0.20/0.49  % (23774)------------------------------
% 0.20/0.49  % (23774)------------------------------
% 0.20/0.49  % (23764)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (23771)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (23779)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.86/0.73  % (23772)Refutation found. Thanks to Tanya!
% 2.86/0.73  % SZS status Theorem for theBenchmark
% 2.86/0.74  % SZS output start Proof for theBenchmark
% 2.86/0.74  fof(f10034,plain,(
% 2.86/0.74    $false),
% 2.86/0.74    inference(subsumption_resolution,[],[f10033,f57])).
% 2.86/0.74  fof(f57,plain,(
% 2.86/0.74    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.86/0.74    inference(superposition,[],[f56,f29])).
% 2.86/0.74  fof(f29,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.86/0.74    inference(cnf_transformation,[],[f1])).
% 2.86/0.74  fof(f1,axiom,(
% 2.86/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.86/0.74  fof(f56,plain,(
% 2.86/0.74    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.86/0.74    inference(resolution,[],[f53,f33])).
% 2.86/0.74  fof(f33,plain,(
% 2.86/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.86/0.74    inference(cnf_transformation,[],[f19])).
% 2.86/0.74  fof(f19,plain,(
% 2.86/0.74    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.86/0.74    inference(ennf_transformation,[],[f5])).
% 2.86/0.74  fof(f5,axiom,(
% 2.86/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.86/0.74  fof(f53,plain,(
% 2.86/0.74    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.86/0.74    inference(trivial_inequality_removal,[],[f52])).
% 2.86/0.74  fof(f52,plain,(
% 2.86/0.74    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X2)) )),
% 2.86/0.74    inference(superposition,[],[f35,f48])).
% 2.86/0.74  fof(f48,plain,(
% 2.86/0.74    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 2.86/0.74    inference(resolution,[],[f34,f45])).
% 2.86/0.74  fof(f45,plain,(
% 2.86/0.74    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.86/0.74    inference(superposition,[],[f27,f42])).
% 2.86/0.74  fof(f42,plain,(
% 2.86/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.86/0.74    inference(backward_demodulation,[],[f39,f26])).
% 2.86/0.74  fof(f26,plain,(
% 2.86/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.86/0.74    inference(cnf_transformation,[],[f7])).
% 2.86/0.74  fof(f7,axiom,(
% 2.86/0.74    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.86/0.74  fof(f39,plain,(
% 2.86/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.86/0.74    inference(definition_unfolding,[],[f25,f30])).
% 2.86/0.74  fof(f30,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.86/0.74    inference(cnf_transformation,[],[f10])).
% 2.86/0.74  fof(f10,axiom,(
% 2.86/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.86/0.74  fof(f25,plain,(
% 2.86/0.74    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.86/0.74    inference(cnf_transformation,[],[f6])).
% 2.86/0.74  fof(f6,axiom,(
% 2.86/0.74    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.86/0.74  fof(f27,plain,(
% 2.86/0.74    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.86/0.74    inference(cnf_transformation,[],[f12])).
% 2.86/0.74  fof(f12,axiom,(
% 2.86/0.74    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.86/0.74  fof(f34,plain,(
% 2.86/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.86/0.74    inference(cnf_transformation,[],[f20])).
% 2.86/0.74  fof(f20,plain,(
% 2.86/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.86/0.74    inference(ennf_transformation,[],[f16])).
% 2.86/0.74  fof(f16,plain,(
% 2.86/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 2.86/0.74    inference(unused_predicate_definition_removal,[],[f13])).
% 2.86/0.74  fof(f13,axiom,(
% 2.86/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.86/0.74  fof(f35,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.86/0.74    inference(cnf_transformation,[],[f21])).
% 2.86/0.74  fof(f21,plain,(
% 2.86/0.74    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 2.86/0.74    inference(ennf_transformation,[],[f17])).
% 2.86/0.74  fof(f17,plain,(
% 2.86/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 2.86/0.74    inference(unused_predicate_definition_removal,[],[f4])).
% 2.86/0.74  fof(f4,axiom,(
% 2.86/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.86/0.74  fof(f10033,plain,(
% 2.86/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)),
% 2.86/0.74    inference(forward_demodulation,[],[f10032,f567])).
% 2.86/0.74  fof(f567,plain,(
% 2.86/0.74    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X0,X1)))) )),
% 2.86/0.74    inference(superposition,[],[f184,f29])).
% 2.86/0.74  fof(f184,plain,(
% 2.86/0.74    ( ! [X6,X8,X7] : (k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f174,f48])).
% 2.86/0.74  fof(f174,plain,(
% 2.86/0.74    ( ! [X6,X8,X7] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8))) )),
% 2.86/0.74    inference(superposition,[],[f36,f146])).
% 2.86/0.74  fof(f146,plain,(
% 2.86/0.74    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f128,f48])).
% 2.86/0.74  fof(f128,plain,(
% 2.86/0.74    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.86/0.74    inference(superposition,[],[f36,f42])).
% 2.86/0.74  fof(f36,plain,(
% 2.86/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.86/0.74    inference(cnf_transformation,[],[f9])).
% 2.86/0.74  fof(f9,axiom,(
% 2.86/0.74    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.86/0.74  fof(f10032,plain,(
% 2.86/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))))),
% 2.86/0.74    inference(forward_demodulation,[],[f10030,f36])).
% 2.86/0.74  fof(f10030,plain,(
% 2.86/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)))),
% 2.86/0.74    inference(backward_demodulation,[],[f1919,f9896])).
% 2.86/0.74  fof(f9896,plain,(
% 2.86/0.74    ( ! [X59,X60,X58] : (k4_xboole_0(X60,k2_xboole_0(X59,X58)) = k4_xboole_0(k2_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X59,X58))) )),
% 2.86/0.74    inference(superposition,[],[f147,f7663])).
% 2.86/0.74  fof(f7663,plain,(
% 2.86/0.74    ( ! [X45,X44] : (k2_xboole_0(X44,X45) = k2_xboole_0(k4_xboole_0(X45,X44),X44)) )),
% 2.86/0.74    inference(forward_demodulation,[],[f7523,f5932])).
% 2.86/0.74  fof(f5932,plain,(
% 2.86/0.74    ( ! [X70,X68,X69] : (k2_xboole_0(X70,X68) = k2_xboole_0(k2_xboole_0(X70,X68),k4_xboole_0(X68,X69))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f5736,f26])).
% 2.86/0.74  fof(f5736,plain,(
% 2.86/0.74    ( ! [X70,X68,X69] : (k2_xboole_0(X70,X68) = k2_xboole_0(k2_xboole_0(X70,X68),k4_xboole_0(k4_xboole_0(X68,X69),k1_xboole_0))) )),
% 2.86/0.74    inference(superposition,[],[f3603,f3480])).
% 2.86/0.74  fof(f3480,plain,(
% 2.86/0.74    ( ! [X80,X81,X79] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X79,X80),k2_xboole_0(X81,X79))) )),
% 2.86/0.74    inference(superposition,[],[f567,f3312])).
% 2.86/0.74  fof(f3312,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 2.86/0.74    inference(resolution,[],[f3289,f33])).
% 2.86/0.74  fof(f3289,plain,(
% 2.86/0.74    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.86/0.74    inference(forward_demodulation,[],[f3253,f57])).
% 2.86/0.74  fof(f3253,plain,(
% 2.86/0.74    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X2,k1_xboole_0))) )),
% 2.86/0.74    inference(superposition,[],[f344,f165])).
% 2.86/0.74  fof(f165,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 2.86/0.74    inference(superposition,[],[f146,f29])).
% 2.86/0.74  fof(f344,plain,(
% 2.86/0.74    ( ! [X19,X20,X18] : (r1_tarski(k4_xboole_0(X18,X19),k2_xboole_0(X20,k4_xboole_0(X18,k2_xboole_0(X19,X20))))) )),
% 2.86/0.74    inference(superposition,[],[f325,f36])).
% 2.86/0.74  fof(f325,plain,(
% 2.86/0.74    ( ! [X8,X7] : (r1_tarski(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 2.86/0.74    inference(trivial_inequality_removal,[],[f315])).
% 2.86/0.74  fof(f315,plain,(
% 2.86/0.74    ( ! [X8,X7] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 2.86/0.74    inference(superposition,[],[f35,f136])).
% 2.86/0.74  fof(f136,plain,(
% 2.86/0.74    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 2.86/0.74    inference(superposition,[],[f36,f42])).
% 2.86/0.74  fof(f3603,plain,(
% 2.86/0.74    ( ! [X31,X32] : (k2_xboole_0(X31,k4_xboole_0(X32,k4_xboole_0(X32,X31))) = X31) )),
% 2.86/0.74    inference(superposition,[],[f3447,f40])).
% 2.86/0.74  fof(f40,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.86/0.74    inference(definition_unfolding,[],[f28,f30,f30])).
% 2.86/0.74  fof(f28,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.86/0.74    inference(cnf_transformation,[],[f2])).
% 2.86/0.74  fof(f2,axiom,(
% 2.86/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.86/0.74  fof(f3447,plain,(
% 2.86/0.74    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.86/0.74    inference(superposition,[],[f3312,f29])).
% 2.86/0.74  fof(f7523,plain,(
% 2.86/0.74    ( ! [X45,X44] : (k2_xboole_0(k4_xboole_0(X45,X44),X44) = k2_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X45,X44))) )),
% 2.86/0.74    inference(superposition,[],[f5848,f232])).
% 2.86/0.74  fof(f232,plain,(
% 2.86/0.74    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)) = X10) )),
% 2.86/0.74    inference(forward_demodulation,[],[f231,f26])).
% 2.86/0.74  fof(f231,plain,(
% 2.86/0.74    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)) = k4_xboole_0(X10,k1_xboole_0)) )),
% 2.86/0.74    inference(forward_demodulation,[],[f196,f146])).
% 2.86/0.74  fof(f196,plain,(
% 2.86/0.74    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10))) )),
% 2.86/0.74    inference(superposition,[],[f40,f66])).
% 2.86/0.74  fof(f66,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 2.86/0.74    inference(superposition,[],[f31,f29])).
% 2.86/0.74  fof(f31,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.86/0.74    inference(cnf_transformation,[],[f8])).
% 2.86/0.74  fof(f8,axiom,(
% 2.86/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.86/0.74  fof(f5848,plain,(
% 2.86/0.74    ( ! [X48,X49] : (k2_xboole_0(X48,X49) = k2_xboole_0(X49,k4_xboole_0(X48,X49))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f5847,f3104])).
% 2.86/0.74  fof(f3104,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))) )),
% 2.86/0.74    inference(resolution,[],[f3077,f33])).
% 2.86/0.74  fof(f3077,plain,(
% 2.86/0.74    ( ! [X47,X46] : (r1_tarski(k2_xboole_0(X47,k4_xboole_0(X46,X47)),k2_xboole_0(X46,X47))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f3010,f254])).
% 2.86/0.74  fof(f254,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 2.86/0.74    inference(resolution,[],[f187,f33])).
% 2.86/0.74  fof(f187,plain,(
% 2.86/0.74    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.86/0.74    inference(superposition,[],[f183,f29])).
% 2.86/0.74  fof(f183,plain,(
% 2.86/0.74    ( ! [X4,X5] : (r1_tarski(X4,k2_xboole_0(X4,X5))) )),
% 2.86/0.74    inference(trivial_inequality_removal,[],[f173])).
% 2.86/0.74  fof(f173,plain,(
% 2.86/0.74    ( ! [X4,X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X4,k2_xboole_0(X4,X5))) )),
% 2.86/0.74    inference(superposition,[],[f35,f146])).
% 2.86/0.74  fof(f3010,plain,(
% 2.86/0.74    ( ! [X47,X46] : (r1_tarski(k2_xboole_0(X47,k4_xboole_0(X46,X47)),k2_xboole_0(X47,k2_xboole_0(X46,X47)))) )),
% 2.86/0.74    inference(superposition,[],[f2952,f31])).
% 2.86/0.74  fof(f2952,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(X50,X51))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f2951,f26])).
% 2.86/0.74  fof(f2951,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f2950,f56])).
% 2.86/0.74  fof(f2950,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0)))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f2949,f29])).
% 2.86/0.74  fof(f2949,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k1_xboole_0))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f2948,f766])).
% 2.86/0.74  fof(f766,plain,(
% 2.86/0.74    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 2.86/0.74    inference(superposition,[],[f294,f29])).
% 2.86/0.74  fof(f294,plain,(
% 2.86/0.74    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X9),X11))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f284,f48])).
% 2.86/0.74  fof(f284,plain,(
% 2.86/0.74    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X9),X11)) = k4_xboole_0(k1_xboole_0,X11)) )),
% 2.86/0.74    inference(superposition,[],[f36,f165])).
% 2.86/0.74  fof(f2948,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k4_xboole_0(X51,k2_xboole_0(X50,k2_xboole_0(X50,X51)))))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f2947,f36])).
% 2.86/0.74  fof(f2947,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k4_xboole_0(k4_xboole_0(X51,X50),k2_xboole_0(X50,X51))))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f2946,f148])).
% 2.86/0.74  fof(f148,plain,(
% 2.86/0.74    ( ! [X8,X7,X9] : (k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(X8,k2_xboole_0(X7,X9))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f130,f36])).
% 2.86/0.74  fof(f130,plain,(
% 2.86/0.74    ( ! [X8,X7,X9] : (k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k4_xboole_0(X8,X7),X9)) )),
% 2.86/0.74    inference(superposition,[],[f36,f66])).
% 2.86/0.74  fof(f2946,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0),k4_xboole_0(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(X50,X51))))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f2809,f29])).
% 2.86/0.74  fof(f2809,plain,(
% 2.86/0.74    ( ! [X50,X51] : (r1_tarski(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X50,k4_xboole_0(X51,X50)),k2_xboole_0(X50,X51)),k4_xboole_0(k2_xboole_0(X50,X51),k1_xboole_0)))) )),
% 2.86/0.74    inference(superposition,[],[f338,f306])).
% 2.86/0.74  fof(f306,plain,(
% 2.86/0.74    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X14,X15),k2_xboole_0(X14,k4_xboole_0(X15,X14)))) )),
% 2.86/0.74    inference(superposition,[],[f136,f66])).
% 2.86/0.74  fof(f338,plain,(
% 2.86/0.74    ( ! [X8,X7] : (r1_tarski(X7,k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,k4_xboole_0(X8,X7))))) )),
% 2.86/0.74    inference(superposition,[],[f325,f40])).
% 2.86/0.74  fof(f5847,plain,(
% 2.86/0.74    ( ! [X48,X49] : (k2_xboole_0(X49,k4_xboole_0(X48,X49)) = k2_xboole_0(k2_xboole_0(X49,k4_xboole_0(X48,X49)),k2_xboole_0(X48,X49))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f5727,f26])).
% 2.86/0.74  fof(f5727,plain,(
% 2.86/0.74    ( ! [X48,X49] : (k2_xboole_0(X49,k4_xboole_0(X48,X49)) = k2_xboole_0(k2_xboole_0(X49,k4_xboole_0(X48,X49)),k4_xboole_0(k2_xboole_0(X48,X49),k1_xboole_0))) )),
% 2.86/0.74    inference(superposition,[],[f3603,f305])).
% 2.86/0.74  fof(f305,plain,(
% 2.86/0.74    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X12,X13)))) )),
% 2.86/0.74    inference(superposition,[],[f136,f31])).
% 2.86/0.74  fof(f147,plain,(
% 2.86/0.74    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) )),
% 2.86/0.74    inference(forward_demodulation,[],[f129,f36])).
% 2.86/0.74  fof(f129,plain,(
% 2.86/0.74    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 2.86/0.74    inference(superposition,[],[f36,f31])).
% 2.86/0.74  fof(f1919,plain,(
% 2.86/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))),
% 2.86/0.74    inference(superposition,[],[f533,f29])).
% 2.86/0.74  fof(f533,plain,(
% 2.86/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.86/0.74    inference(forward_demodulation,[],[f532,f40])).
% 2.86/0.74  fof(f532,plain,(
% 2.86/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 2.86/0.74    inference(backward_demodulation,[],[f38,f509])).
% 2.86/0.74  fof(f509,plain,(
% 2.86/0.74    ( ! [X6,X4,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6))) )),
% 2.86/0.74    inference(superposition,[],[f36,f230])).
% 2.86/0.74  fof(f230,plain,(
% 2.86/0.74    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = X9) )),
% 2.86/0.74    inference(forward_demodulation,[],[f229,f26])).
% 2.86/0.74  fof(f229,plain,(
% 2.86/0.74    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k4_xboole_0(X9,k1_xboole_0)) )),
% 2.86/0.74    inference(forward_demodulation,[],[f195,f165])).
% 2.86/0.74  fof(f195,plain,(
% 2.86/0.74    ( ! [X8,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9))) )),
% 2.86/0.74    inference(superposition,[],[f40,f31])).
% 2.86/0.74  fof(f38,plain,(
% 2.86/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.86/0.74    inference(definition_unfolding,[],[f24,f30,f32,f32])).
% 2.86/0.74  fof(f32,plain,(
% 2.86/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.86/0.74    inference(cnf_transformation,[],[f3])).
% 2.86/0.74  fof(f3,axiom,(
% 2.86/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.86/0.74  fof(f24,plain,(
% 2.86/0.74    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.86/0.74    inference(cnf_transformation,[],[f23])).
% 2.86/0.74  fof(f23,plain,(
% 2.86/0.74    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.86/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f22])).
% 2.86/0.74  fof(f22,plain,(
% 2.86/0.74    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.86/0.74    introduced(choice_axiom,[])).
% 2.86/0.74  fof(f18,plain,(
% 2.86/0.74    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.86/0.74    inference(ennf_transformation,[],[f15])).
% 2.86/0.74  fof(f15,negated_conjecture,(
% 2.86/0.74    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.86/0.74    inference(negated_conjecture,[],[f14])).
% 2.86/0.74  fof(f14,conjecture,(
% 2.86/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.86/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.86/0.74  % SZS output end Proof for theBenchmark
% 2.86/0.74  % (23772)------------------------------
% 2.86/0.74  % (23772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.74  % (23772)Termination reason: Refutation
% 2.86/0.74  
% 2.86/0.74  % (23772)Memory used [KB]: 15223
% 2.86/0.74  % (23772)Time elapsed: 0.314 s
% 2.86/0.74  % (23772)------------------------------
% 2.86/0.74  % (23772)------------------------------
% 2.86/0.75  % (23762)Success in time 0.399 s
%------------------------------------------------------------------------------
