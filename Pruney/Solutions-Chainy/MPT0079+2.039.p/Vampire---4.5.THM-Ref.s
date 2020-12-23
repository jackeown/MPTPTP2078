%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:57 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 540 expanded)
%              Number of leaves         :   16 ( 153 expanded)
%              Depth                    :   28
%              Number of atoms          :  138 (1097 expanded)
%              Number of equality atoms :   82 ( 572 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2861,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2860,f29])).

fof(f29,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f2860,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f2609,f2859])).

fof(f2859,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f2843,f1717])).

fof(f1717,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f1619,f84])).

fof(f84,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f75,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f75,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f35,f57])).

fof(f57,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1619,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f1567,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1567,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f41,f173])).

fof(f173,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f171,f31])).

fof(f171,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f103,f168])).

fof(f168,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f167,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f167,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f162,f59])).

fof(f59,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f34,f31])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f162,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f150])).

fof(f150,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f148,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f148,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f138,f31])).

fof(f138,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f36,f31])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f103,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f34,f59])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f2843,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f36,f2825])).

fof(f2825,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f2824,f26])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f2824,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f2796,f2741])).

fof(f2741,plain,(
    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f2739,f37])).

fof(f2739,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f2734,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f2734,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f2715,f36])).

fof(f2715,plain,(
    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK3) ),
    inference(superposition,[],[f2232,f2581])).

fof(f2581,plain,(
    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f360,f2579])).

fof(f2579,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f2578,f50])).

fof(f50,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f46,f33])).

fof(f2578,plain,(
    k4_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
    inference(resolution,[],[f2563,f37])).

fof(f2563,plain,(
    r1_tarski(sK3,k4_xboole_0(sK3,sK2)) ),
    inference(superposition,[],[f2232,f84])).

fof(f360,plain,(
    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f131,f26])).

fof(f131,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f36,f33])).

fof(f2232,plain,(
    ! [X45] : r1_tarski(k4_xboole_0(X45,sK1),k4_xboole_0(X45,sK2)) ),
    inference(superposition,[],[f978,f446])).

fof(f446,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f443,f37])).

fof(f443,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f425,f223])).

fof(f223,plain,(
    ! [X15] :
      ( ~ r1_tarski(sK2,k2_xboole_0(sK0,X15))
      | r1_tarski(sK2,X15) ) ),
    inference(superposition,[],[f42,f83])).

fof(f83,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f74,f31])).

fof(f74,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f35,f56])).

fof(f56,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f425,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f421,f420])).

fof(f420,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f416,f37])).

fof(f416,plain,(
    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f379,f26])).

fof(f379,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f43,f32])).

fof(f421,plain,(
    r1_tarski(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f385,f420])).

fof(f385,plain,(
    r1_tarski(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)))) ),
    inference(resolution,[],[f43,f324])).

fof(f324,plain,(
    r1_tarski(k4_xboole_0(sK2,sK3),k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f321,f33])).

fof(f321,plain,(
    r1_tarski(k4_xboole_0(sK2,sK3),k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)) ),
    inference(superposition,[],[f142,f137])).

fof(f137,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f36,f26])).

fof(f142,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f32,f36])).

fof(f978,plain,(
    ! [X6,X4,X5] : r1_tarski(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f32,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2796,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f591,f47])).

fof(f47,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(superposition,[],[f32,f31])).

fof(f591,plain,(
    ! [X30] : k2_xboole_0(sK2,k2_xboole_0(sK3,X30)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X30)) ),
    inference(forward_demodulation,[],[f565,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f565,plain,(
    ! [X30] : k2_xboole_0(sK2,k2_xboole_0(sK3,X30)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X30) ),
    inference(superposition,[],[f39,f26])).

fof(f2609,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f137,f2604])).

fof(f2604,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f1619,f2579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (15958)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (15950)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (15942)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (15934)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (15931)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (15936)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (15937)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (15938)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (15955)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (15954)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (15932)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15956)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15933)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (15929)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (15930)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (15939)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (15957)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (15946)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (15948)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (15946)Refutation not found, incomplete strategy% (15946)------------------------------
% 0.21/0.55  % (15946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15946)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15946)Memory used [KB]: 10618
% 0.21/0.55  % (15946)Time elapsed: 0.129 s
% 0.21/0.55  % (15946)------------------------------
% 0.21/0.55  % (15946)------------------------------
% 0.21/0.55  % (15947)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (15949)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (15953)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (15952)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (15940)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (15941)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (15944)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (15945)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (15944)Refutation not found, incomplete strategy% (15944)------------------------------
% 0.21/0.56  % (15944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (15944)Memory used [KB]: 6140
% 0.21/0.57  % (15944)Time elapsed: 0.005 s
% 0.21/0.57  % (15944)------------------------------
% 0.21/0.57  % (15944)------------------------------
% 1.55/0.59  % (15935)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.55/0.59  % (15951)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.78/0.60  % (15943)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.13/0.69  % (15936)Refutation found. Thanks to Tanya!
% 2.13/0.69  % SZS status Theorem for theBenchmark
% 2.13/0.69  % SZS output start Proof for theBenchmark
% 2.13/0.69  fof(f2861,plain,(
% 2.13/0.69    $false),
% 2.13/0.69    inference(subsumption_resolution,[],[f2860,f29])).
% 2.13/0.69  fof(f29,plain,(
% 2.13/0.69    sK1 != sK2),
% 2.13/0.69    inference(cnf_transformation,[],[f25])).
% 2.13/0.69  fof(f25,plain,(
% 2.13/0.69    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.13/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f24])).
% 2.13/0.69  fof(f24,plain,(
% 2.13/0.69    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 2.13/0.69    introduced(choice_axiom,[])).
% 2.13/0.69  fof(f19,plain,(
% 2.13/0.69    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.13/0.69    inference(flattening,[],[f18])).
% 2.13/0.69  fof(f18,plain,(
% 2.13/0.69    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.13/0.69    inference(ennf_transformation,[],[f16])).
% 2.13/0.69  fof(f16,negated_conjecture,(
% 2.13/0.69    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.13/0.69    inference(negated_conjecture,[],[f15])).
% 2.13/0.69  fof(f15,conjecture,(
% 2.13/0.69    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.13/0.69  fof(f2860,plain,(
% 2.13/0.69    sK1 = sK2),
% 2.13/0.69    inference(backward_demodulation,[],[f2609,f2859])).
% 2.13/0.69  fof(f2859,plain,(
% 2.13/0.69    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.13/0.69    inference(forward_demodulation,[],[f2843,f1717])).
% 2.13/0.69  fof(f1717,plain,(
% 2.13/0.69    sK1 = k4_xboole_0(sK1,sK3)),
% 2.13/0.69    inference(superposition,[],[f1619,f84])).
% 2.13/0.69  fof(f84,plain,(
% 2.13/0.69    sK3 = k4_xboole_0(sK3,sK1)),
% 2.13/0.69    inference(forward_demodulation,[],[f75,f31])).
% 2.13/0.69  fof(f31,plain,(
% 2.13/0.69    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.13/0.69    inference(cnf_transformation,[],[f5])).
% 2.13/0.69  fof(f5,axiom,(
% 2.13/0.69    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.13/0.69  fof(f75,plain,(
% 2.13/0.69    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.13/0.69    inference(superposition,[],[f35,f57])).
% 2.13/0.69  fof(f57,plain,(
% 2.13/0.69    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 2.13/0.69    inference(resolution,[],[f38,f28])).
% 2.13/0.69  fof(f28,plain,(
% 2.13/0.69    r1_xboole_0(sK3,sK1)),
% 2.13/0.69    inference(cnf_transformation,[],[f25])).
% 2.13/0.69  fof(f38,plain,(
% 2.13/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.13/0.69    inference(cnf_transformation,[],[f21])).
% 2.13/0.69  fof(f21,plain,(
% 2.13/0.69    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.13/0.69    inference(ennf_transformation,[],[f17])).
% 2.13/0.69  fof(f17,plain,(
% 2.13/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.13/0.69    inference(unused_predicate_definition_removal,[],[f2])).
% 2.13/0.69  fof(f2,axiom,(
% 2.13/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.13/0.69  fof(f35,plain,(
% 2.13/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.13/0.69    inference(cnf_transformation,[],[f10])).
% 2.13/0.69  fof(f10,axiom,(
% 2.13/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.13/0.69  fof(f1619,plain,(
% 2.13/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 2.13/0.69    inference(forward_demodulation,[],[f1567,f46])).
% 2.13/0.69  fof(f46,plain,(
% 2.13/0.69    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 2.13/0.69    inference(resolution,[],[f37,f32])).
% 2.13/0.69  fof(f32,plain,(
% 2.13/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.13/0.69    inference(cnf_transformation,[],[f4])).
% 2.13/0.69  fof(f4,axiom,(
% 2.13/0.69    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.13/0.69  fof(f37,plain,(
% 2.13/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.13/0.69    inference(cnf_transformation,[],[f20])).
% 2.13/0.69  fof(f20,plain,(
% 2.13/0.69    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.13/0.69    inference(ennf_transformation,[],[f3])).
% 2.13/0.69  fof(f3,axiom,(
% 2.13/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.13/0.69  fof(f1567,plain,(
% 2.13/0.69    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.13/0.69    inference(superposition,[],[f41,f173])).
% 2.13/0.69  fof(f173,plain,(
% 2.13/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.13/0.69    inference(forward_demodulation,[],[f171,f31])).
% 2.13/0.69  fof(f171,plain,(
% 2.13/0.69    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 2.13/0.69    inference(backward_demodulation,[],[f103,f168])).
% 2.13/0.69  fof(f168,plain,(
% 2.13/0.69    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.13/0.69    inference(forward_demodulation,[],[f167,f30])).
% 2.13/0.69  fof(f30,plain,(
% 2.13/0.69    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.13/0.69    inference(cnf_transformation,[],[f12])).
% 2.13/0.69  fof(f12,axiom,(
% 2.13/0.69    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.13/0.69  fof(f167,plain,(
% 2.13/0.69    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.13/0.69    inference(forward_demodulation,[],[f162,f59])).
% 2.13/0.69  fof(f59,plain,(
% 2.13/0.69    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1)) )),
% 2.13/0.69    inference(superposition,[],[f34,f31])).
% 2.13/0.69  fof(f34,plain,(
% 2.13/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.13/0.69    inference(cnf_transformation,[],[f11])).
% 2.13/0.69  fof(f11,axiom,(
% 2.13/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.13/0.69  fof(f162,plain,(
% 2.13/0.69    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 2.13/0.69    inference(superposition,[],[f36,f150])).
% 2.13/0.69  fof(f150,plain,(
% 2.13/0.69    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.13/0.69    inference(superposition,[],[f148,f33])).
% 2.13/0.69  fof(f33,plain,(
% 2.13/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.13/0.69    inference(cnf_transformation,[],[f1])).
% 2.13/0.69  fof(f1,axiom,(
% 2.13/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.13/0.69  fof(f148,plain,(
% 2.13/0.69    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.13/0.69    inference(forward_demodulation,[],[f138,f31])).
% 2.13/0.69  fof(f138,plain,(
% 2.13/0.69    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.13/0.69    inference(superposition,[],[f36,f31])).
% 2.13/0.69  fof(f36,plain,(
% 2.13/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.13/0.69    inference(cnf_transformation,[],[f6])).
% 2.13/0.69  fof(f6,axiom,(
% 2.13/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.13/0.69  fof(f103,plain,(
% 2.13/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 2.13/0.69    inference(superposition,[],[f34,f59])).
% 2.13/0.69  fof(f41,plain,(
% 2.13/0.69    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.13/0.69    inference(cnf_transformation,[],[f14])).
% 2.13/0.69  fof(f14,axiom,(
% 2.13/0.69    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.13/0.69  fof(f2843,plain,(
% 2.13/0.69    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 2.13/0.69    inference(superposition,[],[f36,f2825])).
% 2.13/0.69  fof(f2825,plain,(
% 2.13/0.69    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 2.13/0.69    inference(forward_demodulation,[],[f2824,f26])).
% 2.13/0.69  fof(f26,plain,(
% 2.13/0.69    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.13/0.69    inference(cnf_transformation,[],[f25])).
% 2.13/0.69  fof(f2824,plain,(
% 2.13/0.69    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK1,sK3)),
% 2.13/0.69    inference(forward_demodulation,[],[f2796,f2741])).
% 2.13/0.69  fof(f2741,plain,(
% 2.13/0.69    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 2.13/0.69    inference(resolution,[],[f2739,f37])).
% 2.13/0.69  fof(f2739,plain,(
% 2.13/0.69    r1_tarski(sK0,k2_xboole_0(sK1,sK3))),
% 2.13/0.69    inference(resolution,[],[f2734,f43])).
% 2.13/0.69  fof(f43,plain,(
% 2.13/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.69    inference(cnf_transformation,[],[f23])).
% 2.13/0.69  fof(f23,plain,(
% 2.13/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.69    inference(ennf_transformation,[],[f9])).
% 2.13/0.69  fof(f9,axiom,(
% 2.13/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.13/0.69  fof(f2734,plain,(
% 2.13/0.69    r1_tarski(k4_xboole_0(sK0,sK1),sK3)),
% 2.13/0.69    inference(forward_demodulation,[],[f2715,f36])).
% 2.13/0.69  fof(f2715,plain,(
% 2.13/0.69    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK3)),
% 2.13/0.69    inference(superposition,[],[f2232,f2581])).
% 2.13/0.69  fof(f2581,plain,(
% 2.13/0.69    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 2.13/0.69    inference(backward_demodulation,[],[f360,f2579])).
% 2.13/0.69  fof(f2579,plain,(
% 2.13/0.69    sK3 = k4_xboole_0(sK3,sK2)),
% 2.13/0.69    inference(forward_demodulation,[],[f2578,f50])).
% 2.13/0.69  fof(f50,plain,(
% 2.13/0.69    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.13/0.69    inference(superposition,[],[f46,f33])).
% 2.13/0.69  fof(f2578,plain,(
% 2.13/0.69    k4_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k4_xboole_0(sK3,sK2))),
% 2.13/0.69    inference(resolution,[],[f2563,f37])).
% 2.13/0.69  fof(f2563,plain,(
% 2.13/0.69    r1_tarski(sK3,k4_xboole_0(sK3,sK2))),
% 2.13/0.69    inference(superposition,[],[f2232,f84])).
% 2.13/0.69  fof(f360,plain,(
% 2.13/0.69    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 2.13/0.69    inference(superposition,[],[f131,f26])).
% 2.13/0.69  fof(f131,plain,(
% 2.13/0.69    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 2.13/0.69    inference(superposition,[],[f36,f33])).
% 2.13/0.69  fof(f2232,plain,(
% 2.13/0.69    ( ! [X45] : (r1_tarski(k4_xboole_0(X45,sK1),k4_xboole_0(X45,sK2))) )),
% 2.13/0.69    inference(superposition,[],[f978,f446])).
% 2.13/0.69  fof(f446,plain,(
% 2.13/0.69    sK1 = k2_xboole_0(sK2,sK1)),
% 2.13/0.69    inference(resolution,[],[f443,f37])).
% 2.13/0.69  fof(f443,plain,(
% 2.13/0.69    r1_tarski(sK2,sK1)),
% 2.13/0.69    inference(resolution,[],[f425,f223])).
% 2.13/0.69  fof(f223,plain,(
% 2.13/0.69    ( ! [X15] : (~r1_tarski(sK2,k2_xboole_0(sK0,X15)) | r1_tarski(sK2,X15)) )),
% 2.13/0.69    inference(superposition,[],[f42,f83])).
% 2.13/0.69  fof(f83,plain,(
% 2.13/0.69    sK2 = k4_xboole_0(sK2,sK0)),
% 2.13/0.69    inference(forward_demodulation,[],[f74,f31])).
% 2.13/0.69  fof(f74,plain,(
% 2.13/0.69    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.13/0.69    inference(superposition,[],[f35,f56])).
% 2.13/0.69  fof(f56,plain,(
% 2.13/0.69    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 2.13/0.69    inference(resolution,[],[f38,f27])).
% 2.13/0.69  fof(f27,plain,(
% 2.13/0.69    r1_xboole_0(sK2,sK0)),
% 2.13/0.69    inference(cnf_transformation,[],[f25])).
% 2.13/0.69  fof(f42,plain,(
% 2.13/0.69    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.69    inference(cnf_transformation,[],[f22])).
% 2.13/0.69  fof(f22,plain,(
% 2.13/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.69    inference(ennf_transformation,[],[f8])).
% 2.13/0.69  fof(f8,axiom,(
% 2.13/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.13/0.69  fof(f425,plain,(
% 2.13/0.69    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 2.13/0.69    inference(forward_demodulation,[],[f421,f420])).
% 2.13/0.69  fof(f420,plain,(
% 2.13/0.69    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.13/0.69    inference(resolution,[],[f416,f37])).
% 2.13/0.69  fof(f416,plain,(
% 2.13/0.69    r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 2.13/0.69    inference(superposition,[],[f379,f26])).
% 2.13/0.69  fof(f379,plain,(
% 2.13/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.13/0.69    inference(resolution,[],[f43,f32])).
% 2.13/0.69  fof(f421,plain,(
% 2.13/0.69    r1_tarski(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)))),
% 2.13/0.69    inference(backward_demodulation,[],[f385,f420])).
% 2.13/0.69  fof(f385,plain,(
% 2.13/0.69    r1_tarski(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))))),
% 2.13/0.69    inference(resolution,[],[f43,f324])).
% 2.13/0.69  fof(f324,plain,(
% 2.13/0.69    r1_tarski(k4_xboole_0(sK2,sK3),k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)))),
% 2.13/0.69    inference(forward_demodulation,[],[f321,f33])).
% 2.13/0.69  fof(f321,plain,(
% 2.13/0.69    r1_tarski(k4_xboole_0(sK2,sK3),k2_xboole_0(k2_xboole_0(sK0,sK1),sK3))),
% 2.13/0.69    inference(superposition,[],[f142,f137])).
% 2.13/0.69  fof(f137,plain,(
% 2.13/0.69    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.13/0.69    inference(superposition,[],[f36,f26])).
% 2.13/0.69  fof(f142,plain,(
% 2.13/0.69    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7))) )),
% 2.13/0.69    inference(superposition,[],[f32,f36])).
% 2.13/0.69  fof(f978,plain,(
% 2.13/0.69    ( ! [X6,X4,X5] : (r1_tarski(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,X5))) )),
% 2.13/0.69    inference(superposition,[],[f32,f40])).
% 2.13/0.69  fof(f40,plain,(
% 2.13/0.69    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.69    inference(cnf_transformation,[],[f7])).
% 2.13/0.69  fof(f7,axiom,(
% 2.13/0.69    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.13/0.69  fof(f2796,plain,(
% 2.13/0.69    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 2.13/0.69    inference(superposition,[],[f591,f47])).
% 2.13/0.69  fof(f47,plain,(
% 2.13/0.69    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 2.13/0.69    inference(resolution,[],[f37,f45])).
% 2.13/0.69  fof(f45,plain,(
% 2.13/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.13/0.69    inference(superposition,[],[f32,f31])).
% 2.13/0.69  fof(f591,plain,(
% 2.13/0.69    ( ! [X30] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X30)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X30))) )),
% 2.13/0.69    inference(forward_demodulation,[],[f565,f39])).
% 2.13/0.69  fof(f39,plain,(
% 2.13/0.69    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.69    inference(cnf_transformation,[],[f13])).
% 2.13/0.69  fof(f13,axiom,(
% 2.13/0.69    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.13/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.13/0.69  fof(f565,plain,(
% 2.13/0.69    ( ! [X30] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X30)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X30)) )),
% 2.13/0.69    inference(superposition,[],[f39,f26])).
% 2.13/0.69  fof(f2609,plain,(
% 2.13/0.69    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.13/0.69    inference(backward_demodulation,[],[f137,f2604])).
% 2.13/0.69  fof(f2604,plain,(
% 2.13/0.69    sK2 = k4_xboole_0(sK2,sK3)),
% 2.13/0.69    inference(superposition,[],[f1619,f2579])).
% 2.13/0.69  % SZS output end Proof for theBenchmark
% 2.13/0.69  % (15936)------------------------------
% 2.13/0.69  % (15936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.69  % (15936)Termination reason: Refutation
% 2.13/0.69  
% 2.13/0.69  % (15936)Memory used [KB]: 8059
% 2.13/0.69  % (15936)Time elapsed: 0.270 s
% 2.13/0.69  % (15936)------------------------------
% 2.13/0.69  % (15936)------------------------------
% 2.13/0.69  % (15926)Success in time 0.315 s
%------------------------------------------------------------------------------
