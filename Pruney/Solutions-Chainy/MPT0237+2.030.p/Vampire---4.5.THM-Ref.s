%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:33 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 485 expanded)
%              Number of leaves         :   20 ( 161 expanded)
%              Depth                    :   16
%              Number of atoms          :  112 ( 543 expanded)
%              Number of equality atoms :   89 ( 504 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(subsumption_resolution,[],[f263,f83])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f78,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f62,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f263,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f262,f139])).

fof(f139,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(backward_demodulation,[],[f137,f138])).

fof(f138,plain,(
    ! [X2,X3] : k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(resolution,[],[f74,f40])).

fof(f74,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) != X0
      | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f49,f58,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f137,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(resolution,[],[f74,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f262,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f260,f138])).

fof(f260,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f255,f259])).

fof(f259,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f258,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f39,f58,f60,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f58])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f258,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f255,f218])).

fof(f218,plain,(
    ! [X6,X5] :
      ( k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5) = k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))
      | X5 = X6 ) ),
    inference(superposition,[],[f146,f33])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
      | X0 = X1 ) ),
    inference(resolution,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f38,f60,f60])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f255,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f61,f107])).

fof(f107,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f63,f33])).

fof(f63,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f59,f37])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f58])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f61,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f29,f58,f58,f60,f60])).

fof(f29,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:09 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.56  % (12182)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (12190)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (12184)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (12184)Refutation not found, incomplete strategy% (12184)------------------------------
% 0.21/0.56  % (12184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (12200)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (12192)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (12184)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (12184)Memory used [KB]: 10618
% 0.21/0.57  % (12184)Time elapsed: 0.122 s
% 0.21/0.57  % (12184)------------------------------
% 0.21/0.57  % (12184)------------------------------
% 0.21/0.57  % (12198)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (12198)Refutation not found, incomplete strategy% (12198)------------------------------
% 0.21/0.57  % (12198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12198)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12198)Memory used [KB]: 10746
% 0.21/0.58  % (12198)Time elapsed: 0.126 s
% 0.21/0.58  % (12198)------------------------------
% 0.21/0.58  % (12198)------------------------------
% 1.57/0.60  % (12182)Refutation found. Thanks to Tanya!
% 1.57/0.60  % SZS status Theorem for theBenchmark
% 1.57/0.61  % SZS output start Proof for theBenchmark
% 1.57/0.61  fof(f264,plain,(
% 1.57/0.61    $false),
% 1.57/0.61    inference(subsumption_resolution,[],[f263,f83])).
% 1.57/0.61  fof(f83,plain,(
% 1.57/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.61    inference(backward_demodulation,[],[f78,f82])).
% 1.57/0.61  fof(f82,plain,(
% 1.57/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.61    inference(resolution,[],[f40,f30])).
% 1.57/0.61  fof(f30,plain,(
% 1.57/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f5])).
% 1.57/0.61  fof(f5,axiom,(
% 1.57/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.57/0.61  fof(f40,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.61    inference(cnf_transformation,[],[f26])).
% 1.57/0.61  fof(f26,plain,(
% 1.57/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f4])).
% 1.57/0.61  fof(f4,axiom,(
% 1.57/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.61  fof(f78,plain,(
% 1.57/0.61    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.57/0.61    inference(superposition,[],[f62,f33])).
% 1.57/0.61  fof(f33,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f1])).
% 1.57/0.61  fof(f1,axiom,(
% 1.57/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.57/0.61  fof(f62,plain,(
% 1.57/0.61    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.57/0.61    inference(definition_unfolding,[],[f31,f37])).
% 1.57/0.61  fof(f37,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f3])).
% 1.57/0.61  fof(f3,axiom,(
% 1.57/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.61  fof(f31,plain,(
% 1.57/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.61    inference(cnf_transformation,[],[f6])).
% 1.57/0.61  fof(f6,axiom,(
% 1.57/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.57/0.61  fof(f263,plain,(
% 1.57/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.57/0.61    inference(forward_demodulation,[],[f262,f139])).
% 1.57/0.61  fof(f139,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.57/0.61    inference(backward_demodulation,[],[f137,f138])).
% 1.57/0.61  fof(f138,plain,(
% 1.57/0.61    ( ! [X2,X3] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 1.57/0.61    inference(resolution,[],[f74,f40])).
% 1.57/0.61  fof(f74,plain,(
% 1.57/0.61    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.57/0.61    inference(equality_resolution,[],[f69])).
% 1.57/0.61  fof(f69,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) != X0 | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.57/0.61    inference(definition_unfolding,[],[f49,f58,f58])).
% 1.57/0.61  fof(f58,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.57/0.61    inference(definition_unfolding,[],[f35,f57])).
% 1.57/0.61  fof(f57,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.57/0.61    inference(definition_unfolding,[],[f44,f56])).
% 1.57/0.61  fof(f56,plain,(
% 1.57/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.57/0.61    inference(definition_unfolding,[],[f50,f55])).
% 1.57/0.61  fof(f55,plain,(
% 1.57/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.57/0.61    inference(definition_unfolding,[],[f51,f54])).
% 1.57/0.61  fof(f54,plain,(
% 1.57/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.57/0.61    inference(definition_unfolding,[],[f52,f53])).
% 1.57/0.61  fof(f53,plain,(
% 1.57/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f15])).
% 1.57/0.61  fof(f15,axiom,(
% 1.57/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.57/0.61  fof(f52,plain,(
% 1.57/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f14])).
% 1.57/0.61  fof(f14,axiom,(
% 1.57/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.57/0.61  fof(f51,plain,(
% 1.57/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f13])).
% 1.57/0.61  fof(f13,axiom,(
% 1.57/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.57/0.61  fof(f50,plain,(
% 1.57/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f12])).
% 1.57/0.61  fof(f12,axiom,(
% 1.57/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.57/0.61  fof(f44,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f11])).
% 1.57/0.61  fof(f11,axiom,(
% 1.57/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.61  fof(f35,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f10])).
% 1.57/0.61  fof(f10,axiom,(
% 1.57/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.61  fof(f49,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f28])).
% 1.57/0.61  fof(f28,plain,(
% 1.57/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.57/0.61    inference(ennf_transformation,[],[f16])).
% 1.57/0.61  fof(f16,axiom,(
% 1.57/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.57/0.61  fof(f137,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.57/0.61    inference(resolution,[],[f74,f68])).
% 1.57/0.61  fof(f68,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.61    inference(definition_unfolding,[],[f42,f37])).
% 1.57/0.61  fof(f42,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.57/0.61    inference(cnf_transformation,[],[f2])).
% 1.57/0.61  fof(f2,axiom,(
% 1.57/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.57/0.61  fof(f262,plain,(
% 1.57/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.57/0.61    inference(forward_demodulation,[],[f260,f138])).
% 1.57/0.61  fof(f260,plain,(
% 1.57/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.57/0.61    inference(backward_demodulation,[],[f255,f259])).
% 1.57/0.61  fof(f259,plain,(
% 1.57/0.61    sK0 = sK1),
% 1.57/0.61    inference(subsumption_resolution,[],[f258,f65])).
% 1.57/0.61  fof(f65,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 1.57/0.61    inference(definition_unfolding,[],[f39,f58,f60,f60])).
% 1.57/0.61  fof(f60,plain,(
% 1.57/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.57/0.61    inference(definition_unfolding,[],[f32,f58])).
% 1.57/0.61  fof(f32,plain,(
% 1.57/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f9])).
% 1.57/0.61  fof(f9,axiom,(
% 1.57/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.57/0.61  fof(f39,plain,(
% 1.57/0.61    ( ! [X0,X1] : (X0 = X1 | k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f25])).
% 1.57/0.61  fof(f25,plain,(
% 1.57/0.61    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.57/0.61    inference(ennf_transformation,[],[f19])).
% 1.57/0.61  fof(f19,axiom,(
% 1.57/0.61    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 1.57/0.61  fof(f258,plain,(
% 1.57/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 1.57/0.61    inference(superposition,[],[f255,f218])).
% 1.57/0.61  fof(f218,plain,(
% 1.57/0.61    ( ! [X6,X5] : (k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5) = k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) | X5 = X6) )),
% 1.57/0.61    inference(superposition,[],[f146,f33])).
% 1.57/0.61  fof(f146,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) | X0 = X1) )),
% 1.57/0.61    inference(resolution,[],[f64,f66])).
% 1.57/0.61  fof(f66,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.57/0.61    inference(definition_unfolding,[],[f41,f37])).
% 1.57/0.61  fof(f41,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.57/0.61    inference(cnf_transformation,[],[f27])).
% 1.57/0.61  fof(f27,plain,(
% 1.57/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f22])).
% 1.57/0.61  fof(f22,plain,(
% 1.57/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.57/0.61    inference(unused_predicate_definition_removal,[],[f7])).
% 1.57/0.61  fof(f7,axiom,(
% 1.57/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.57/0.61  fof(f64,plain,(
% 1.57/0.61    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 1.57/0.61    inference(definition_unfolding,[],[f38,f60,f60])).
% 1.57/0.61  fof(f38,plain,(
% 1.57/0.61    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f24])).
% 1.57/0.61  fof(f24,plain,(
% 1.57/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.57/0.61    inference(ennf_transformation,[],[f18])).
% 1.57/0.61  fof(f18,axiom,(
% 1.57/0.61    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.86/0.61  fof(f255,plain,(
% 1.86/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.86/0.61    inference(superposition,[],[f61,f107])).
% 1.86/0.61  fof(f107,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 1.86/0.61    inference(superposition,[],[f63,f33])).
% 1.86/0.61  fof(f63,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.86/0.61    inference(definition_unfolding,[],[f36,f59,f37])).
% 1.86/0.61  fof(f59,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.86/0.61    inference(definition_unfolding,[],[f34,f58])).
% 1.86/0.61  fof(f34,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f17])).
% 1.86/0.61  fof(f17,axiom,(
% 1.86/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.86/0.61  fof(f36,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f8])).
% 1.86/0.61  fof(f8,axiom,(
% 1.86/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.86/0.61  fof(f61,plain,(
% 1.86/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.86/0.61    inference(definition_unfolding,[],[f29,f58,f58,f60,f60])).
% 1.86/0.61  fof(f29,plain,(
% 1.86/0.61    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.86/0.61    inference(cnf_transformation,[],[f23])).
% 1.86/0.61  fof(f23,plain,(
% 1.86/0.61    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.86/0.61    inference(ennf_transformation,[],[f21])).
% 1.86/0.61  fof(f21,negated_conjecture,(
% 1.86/0.61    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.86/0.61    inference(negated_conjecture,[],[f20])).
% 1.86/0.61  fof(f20,conjecture,(
% 1.86/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 1.86/0.61  % SZS output end Proof for theBenchmark
% 1.86/0.61  % (12182)------------------------------
% 1.86/0.61  % (12182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.61  % (12182)Termination reason: Refutation
% 1.86/0.61  
% 1.86/0.61  % (12182)Memory used [KB]: 6524
% 1.86/0.61  % (12182)Time elapsed: 0.145 s
% 1.86/0.61  % (12182)------------------------------
% 1.86/0.61  % (12182)------------------------------
% 1.86/0.61  % (12175)Success in time 0.244 s
%------------------------------------------------------------------------------
