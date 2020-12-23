%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:06 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  111 (4111 expanded)
%              Number of leaves         :   16 (1185 expanded)
%              Depth                    :   29
%              Number of atoms          :  150 (7066 expanded)
%              Number of equality atoms :   76 (2754 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1006,f347])).

fof(f347,plain,(
    sK2 != k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f244,f324])).

fof(f324,plain,(
    k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f310,f189])).

fof(f189,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f63,f73])).

fof(f73,plain,(
    k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f46,f63])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f58,f25])).

fof(f25,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,X0)))) ) ),
    inference(forward_demodulation,[],[f57,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f35,f35])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK2))) ) ),
    inference(resolution,[],[f55,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f55,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK2)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f25,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | r1_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f310,plain,(
    k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0))) ),
    inference(superposition,[],[f197,f49])).

fof(f197,plain,(
    k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK2)) ),
    inference(resolution,[],[f190,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f190,plain,(
    r1_tarski(k5_xboole_0(sK2,k1_xboole_0),sK2) ),
    inference(superposition,[],[f29,f73])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f244,plain,(
    sK2 != k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f47,f156])).

fof(f156,plain,(
    k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f46,f66])).

fof(f66,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(resolution,[],[f62,f28])).

fof(f62,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    inference(resolution,[],[f58,f26])).

fof(f26,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    sK2 != k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f27,f45])).

fof(f27,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1006,plain,(
    sK2 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f998,f338])).

fof(f338,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f189,f324])).

fof(f998,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))
    | sK2 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f39,f993])).

fof(f993,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2) ),
    inference(backward_demodulation,[],[f475,f962])).

fof(f962,plain,(
    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f398,f952])).

fof(f952,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f951,f389])).

fof(f389,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(resolution,[],[f388,f28])).

fof(f388,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f387,f103])).

fof(f103,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f102,f28])).

fof(f102,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f101,f83])).

fof(f83,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(resolution,[],[f72,f52])).

fof(f72,plain,(
    r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f48,f63])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f101,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)))) ),
    inference(resolution,[],[f91,f51])).

fof(f91,plain,(
    r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(superposition,[],[f31,f83])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f387,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f386,f123])).

fof(f123,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f89,f115])).

fof(f115,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f111,f103])).

fof(f111,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f46,f103])).

fof(f89,plain,(
    k4_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f46,f83])).

fof(f386,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))))) ),
    inference(forward_demodulation,[],[f385,f49])).

fof(f385,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))))) ),
    inference(forward_demodulation,[],[f384,f49])).

fof(f384,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)))) ),
    inference(resolution,[],[f383,f51])).

fof(f383,plain,(
    r1_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)) ),
    inference(forward_demodulation,[],[f319,f324])).

fof(f319,plain,(
    r1_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK2)) ),
    inference(superposition,[],[f31,f197])).

fof(f951,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f950,f492])).

fof(f492,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f478,f389])).

fof(f478,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(superposition,[],[f46,f341])).

fof(f341,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)) ),
    inference(backward_demodulation,[],[f197,f324])).

fof(f950,plain,(
    k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f949,f324])).

fof(f949,plain,(
    k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f936,f103])).

fof(f936,plain,(
    k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f369,f342])).

fof(f342,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f218,f324])).

fof(f218,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f211,f115])).

fof(f211,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[],[f46,f204])).

fof(f204,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))) ),
    inference(resolution,[],[f196,f28])).

fof(f196,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)))) ),
    inference(resolution,[],[f188,f51])).

fof(f188,plain,(
    r1_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f75,f73])).

fof(f75,plain,(
    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f31,f63])).

fof(f369,plain,(
    ! [X2] : k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK2,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,X2))) ),
    inference(forward_demodulation,[],[f361,f49])).

fof(f361,plain,(
    ! [X2] : k4_xboole_0(k5_xboole_0(sK2,X2),k4_xboole_0(k5_xboole_0(sK2,X2),k4_xboole_0(sK2,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK2,k1_xboole_0)))) ),
    inference(superposition,[],[f53,f338])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f41,f35,f35,f35])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f398,plain,(
    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f46,f389])).

fof(f475,plain,(
    k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[],[f46,f341])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:34:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.50  % (24698)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (24709)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (24698)Refutation not found, incomplete strategy% (24698)------------------------------
% 0.22/0.52  % (24698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24700)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (24716)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (24698)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (24698)Memory used [KB]: 10746
% 0.22/0.52  % (24698)Time elapsed: 0.097 s
% 0.22/0.52  % (24698)------------------------------
% 0.22/0.52  % (24698)------------------------------
% 0.22/0.52  % (24705)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (24717)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (24708)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (24722)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (24702)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (24718)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (24718)Refutation not found, incomplete strategy% (24718)------------------------------
% 0.22/0.53  % (24718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24718)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24718)Memory used [KB]: 10618
% 0.22/0.53  % (24718)Time elapsed: 0.083 s
% 0.22/0.53  % (24718)------------------------------
% 0.22/0.53  % (24718)------------------------------
% 0.22/0.53  % (24725)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (24714)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (24697)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (24696)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (24707)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (24724)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (24699)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (24710)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (24701)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (24712)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (24721)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (24711)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (24719)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (24713)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (24720)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (24713)Refutation not found, incomplete strategy% (24713)------------------------------
% 0.22/0.55  % (24713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24713)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24713)Memory used [KB]: 10618
% 0.22/0.55  % (24713)Time elapsed: 0.138 s
% 0.22/0.55  % (24713)------------------------------
% 0.22/0.55  % (24713)------------------------------
% 0.22/0.55  % (24704)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (24704)Refutation not found, incomplete strategy% (24704)------------------------------
% 0.22/0.56  % (24704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (24704)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (24704)Memory used [KB]: 10618
% 0.22/0.56  % (24704)Time elapsed: 0.139 s
% 0.22/0.56  % (24704)------------------------------
% 0.22/0.56  % (24704)------------------------------
% 0.22/0.56  % (24706)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (24715)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (24703)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (24723)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.65/0.59  % (24717)Refutation found. Thanks to Tanya!
% 1.65/0.59  % SZS status Theorem for theBenchmark
% 1.65/0.59  % SZS output start Proof for theBenchmark
% 1.65/0.59  fof(f1007,plain,(
% 1.65/0.59    $false),
% 1.65/0.59    inference(subsumption_resolution,[],[f1006,f347])).
% 1.65/0.59  fof(f347,plain,(
% 1.65/0.59    sK2 != k4_xboole_0(sK2,k1_xboole_0)),
% 1.65/0.59    inference(superposition,[],[f244,f324])).
% 1.65/0.59  fof(f324,plain,(
% 1.65/0.59    k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.65/0.59    inference(forward_demodulation,[],[f310,f189])).
% 1.65/0.59  fof(f189,plain,(
% 1.65/0.59    k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.59    inference(backward_demodulation,[],[f63,f73])).
% 1.65/0.59  fof(f73,plain,(
% 1.65/0.59    k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.65/0.59    inference(superposition,[],[f46,f63])).
% 1.65/0.59  fof(f46,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.65/0.59    inference(definition_unfolding,[],[f34,f35])).
% 1.65/0.59  fof(f35,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f10])).
% 1.65/0.59  fof(f10,axiom,(
% 1.65/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.65/0.59  fof(f34,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f4])).
% 1.65/0.59  fof(f4,axiom,(
% 1.65/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.65/0.59  fof(f63,plain,(
% 1.65/0.59    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.65/0.59    inference(resolution,[],[f61,f28])).
% 1.65/0.59  fof(f28,plain,(
% 1.65/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f20])).
% 1.65/0.59  fof(f20,plain,(
% 1.65/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.65/0.59    inference(ennf_transformation,[],[f3])).
% 1.65/0.59  fof(f3,axiom,(
% 1.65/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.65/0.59  fof(f61,plain,(
% 1.65/0.59    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) )),
% 1.65/0.59    inference(resolution,[],[f58,f25])).
% 1.65/0.59  fof(f25,plain,(
% 1.65/0.59    ~r2_hidden(sK0,sK2)),
% 1.65/0.59    inference(cnf_transformation,[],[f19])).
% 1.65/0.59  fof(f19,plain,(
% 1.65/0.59    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.65/0.59    inference(ennf_transformation,[],[f17])).
% 1.65/0.59  fof(f17,negated_conjecture,(
% 1.65/0.59    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.65/0.59    inference(negated_conjecture,[],[f16])).
% 1.65/0.59  fof(f16,conjecture,(
% 1.65/0.59    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.65/0.59  fof(f58,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,X0))))) )),
% 1.65/0.59    inference(forward_demodulation,[],[f57,f49])).
% 1.65/0.59  fof(f49,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.65/0.59    inference(definition_unfolding,[],[f32,f35,f35])).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f1])).
% 1.65/0.59  fof(f1,axiom,(
% 1.65/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.65/0.60  fof(f57,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK2)))) )),
% 1.65/0.60    inference(resolution,[],[f55,f51])).
% 1.65/0.60  fof(f51,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.65/0.60    inference(definition_unfolding,[],[f36,f35])).
% 1.65/0.60  fof(f36,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f21])).
% 1.65/0.60  fof(f21,plain,(
% 1.65/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.65/0.60    inference(ennf_transformation,[],[f18])).
% 1.65/0.60  fof(f18,plain,(
% 1.65/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.60    inference(rectify,[],[f2])).
% 1.65/0.60  fof(f2,axiom,(
% 1.65/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.65/0.60  fof(f55,plain,(
% 1.65/0.60    ( ! [X0] : (r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK2) | r2_hidden(X0,sK2)) )),
% 1.65/0.60    inference(resolution,[],[f25,f54])).
% 1.65/0.60  fof(f54,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f42,f45])).
% 1.65/0.60  fof(f45,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f33,f44])).
% 1.65/0.60  fof(f44,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f40,f43])).
% 1.65/0.60  fof(f43,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f14])).
% 1.65/0.60  fof(f14,axiom,(
% 1.65/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.65/0.60  fof(f40,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f13])).
% 1.65/0.60  fof(f13,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.65/0.60  fof(f33,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f12])).
% 1.65/0.60  fof(f12,axiom,(
% 1.65/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.65/0.60  fof(f42,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | r1_xboole_0(k2_tarski(X0,X2),X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f24])).
% 1.65/0.60  fof(f24,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.65/0.60    inference(ennf_transformation,[],[f15])).
% 1.65/0.60  fof(f15,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.65/0.60  fof(f310,plain,(
% 1.65/0.60    k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0)))),
% 1.65/0.60    inference(superposition,[],[f197,f49])).
% 1.65/0.60  fof(f197,plain,(
% 1.65/0.60    k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK2))),
% 1.65/0.60    inference(resolution,[],[f190,f52])).
% 1.65/0.60  fof(f52,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.65/0.60    inference(definition_unfolding,[],[f38,f35])).
% 1.65/0.60  fof(f38,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.65/0.60    inference(cnf_transformation,[],[f22])).
% 1.65/0.60  fof(f22,plain,(
% 1.65/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.65/0.60    inference(ennf_transformation,[],[f7])).
% 1.65/0.60  fof(f7,axiom,(
% 1.65/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.65/0.60  fof(f190,plain,(
% 1.65/0.60    r1_tarski(k5_xboole_0(sK2,k1_xboole_0),sK2)),
% 1.65/0.60    inference(superposition,[],[f29,f73])).
% 1.65/0.60  fof(f29,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f9])).
% 1.65/0.60  fof(f9,axiom,(
% 1.65/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.65/0.60  fof(f244,plain,(
% 1.65/0.60    sK2 != k5_xboole_0(sK2,k1_xboole_0)),
% 1.65/0.60    inference(superposition,[],[f47,f156])).
% 1.65/0.60  fof(f156,plain,(
% 1.65/0.60    k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.65/0.60    inference(superposition,[],[f46,f66])).
% 1.65/0.60  fof(f66,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 1.65/0.60    inference(resolution,[],[f62,f28])).
% 1.65/0.60  fof(f62,plain,(
% 1.65/0.60    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))) )),
% 1.65/0.60    inference(resolution,[],[f58,f26])).
% 1.65/0.60  fof(f26,plain,(
% 1.65/0.60    ~r2_hidden(sK1,sK2)),
% 1.65/0.60    inference(cnf_transformation,[],[f19])).
% 1.65/0.60  fof(f47,plain,(
% 1.65/0.60    sK2 != k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 1.65/0.60    inference(definition_unfolding,[],[f27,f45])).
% 1.65/0.60  fof(f27,plain,(
% 1.65/0.60    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 1.65/0.60    inference(cnf_transformation,[],[f19])).
% 1.65/0.60  fof(f1006,plain,(
% 1.65/0.60    sK2 = k4_xboole_0(sK2,k1_xboole_0)),
% 1.65/0.60    inference(subsumption_resolution,[],[f998,f338])).
% 1.65/0.60  fof(f338,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(backward_demodulation,[],[f189,f324])).
% 1.65/0.60  fof(f998,plain,(
% 1.65/0.60    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) | sK2 = k4_xboole_0(sK2,k1_xboole_0)),
% 1.65/0.60    inference(superposition,[],[f39,f993])).
% 1.65/0.60  fof(f993,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)),
% 1.65/0.60    inference(backward_demodulation,[],[f475,f962])).
% 1.65/0.60  fof(f962,plain,(
% 1.65/0.60    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(backward_demodulation,[],[f398,f952])).
% 1.65/0.60  fof(f952,plain,(
% 1.65/0.60    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)),
% 1.65/0.60    inference(forward_demodulation,[],[f951,f389])).
% 1.65/0.60  fof(f389,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(resolution,[],[f388,f28])).
% 1.65/0.60  fof(f388,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)))) )),
% 1.65/0.60    inference(forward_demodulation,[],[f387,f103])).
% 1.65/0.60  fof(f103,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.65/0.60    inference(resolution,[],[f102,f28])).
% 1.65/0.60  fof(f102,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.65/0.60    inference(forward_demodulation,[],[f101,f83])).
% 1.65/0.60  fof(f83,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))),
% 1.65/0.60    inference(resolution,[],[f72,f52])).
% 1.65/0.60  fof(f72,plain,(
% 1.65/0.60    r1_tarski(k1_xboole_0,sK2)),
% 1.65/0.60    inference(superposition,[],[f48,f63])).
% 1.65/0.60  fof(f48,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f30,f35])).
% 1.65/0.60  fof(f30,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f6])).
% 1.65/0.60  fof(f6,axiom,(
% 1.65/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.65/0.60  fof(f101,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))))) )),
% 1.65/0.60    inference(resolution,[],[f91,f51])).
% 1.65/0.60  fof(f91,plain,(
% 1.65/0.60    r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))),
% 1.65/0.60    inference(superposition,[],[f31,f83])).
% 1.65/0.60  fof(f31,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f11])).
% 1.65/0.60  fof(f11,axiom,(
% 1.65/0.60    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.65/0.60  fof(f387,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0))))) )),
% 1.65/0.60    inference(forward_demodulation,[],[f386,f123])).
% 1.65/0.60  fof(f123,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 1.65/0.60    inference(forward_demodulation,[],[f89,f115])).
% 1.65/0.60  fof(f115,plain,(
% 1.65/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.65/0.60    inference(forward_demodulation,[],[f111,f103])).
% 1.65/0.60  fof(f111,plain,(
% 1.65/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.65/0.60    inference(superposition,[],[f46,f103])).
% 1.65/0.60  fof(f89,plain,(
% 1.65/0.60    k4_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.65/0.60    inference(superposition,[],[f46,f83])).
% 1.65/0.60  fof(f386,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)))))) )),
% 1.65/0.60    inference(forward_demodulation,[],[f385,f49])).
% 1.65/0.60  fof(f385,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)))))) )),
% 1.65/0.60    inference(forward_demodulation,[],[f384,f49])).
% 1.65/0.60  fof(f384,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2))))) )),
% 1.65/0.60    inference(resolution,[],[f383,f51])).
% 1.65/0.60  fof(f383,plain,(
% 1.65/0.60    r1_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2))),
% 1.65/0.60    inference(forward_demodulation,[],[f319,f324])).
% 1.65/0.60  fof(f319,plain,(
% 1.65/0.60    r1_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK2))),
% 1.65/0.60    inference(superposition,[],[f31,f197])).
% 1.65/0.60  fof(f951,plain,(
% 1.65/0.60    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)))),
% 1.65/0.60    inference(forward_demodulation,[],[f950,f492])).
% 1.65/0.60  fof(f492,plain,(
% 1.65/0.60    k4_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)),
% 1.65/0.60    inference(forward_demodulation,[],[f478,f389])).
% 1.65/0.60  fof(f478,plain,(
% 1.65/0.60    k4_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)))),
% 1.65/0.60    inference(superposition,[],[f46,f341])).
% 1.65/0.60  fof(f341,plain,(
% 1.65/0.60    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2))),
% 1.65/0.60    inference(backward_demodulation,[],[f197,f324])).
% 1.65/0.60  fof(f950,plain,(
% 1.65/0.60    k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)),
% 1.65/0.60    inference(forward_demodulation,[],[f949,f324])).
% 1.65/0.60  fof(f949,plain,(
% 1.65/0.60    k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0)))),
% 1.65/0.60    inference(forward_demodulation,[],[f936,f103])).
% 1.65/0.60  fof(f936,plain,(
% 1.65/0.60    k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.65/0.60    inference(superposition,[],[f369,f342])).
% 1.65/0.60  fof(f342,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(backward_demodulation,[],[f218,f324])).
% 1.65/0.60  fof(f218,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(forward_demodulation,[],[f211,f115])).
% 1.65/0.60  fof(f211,plain,(
% 1.65/0.60    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(superposition,[],[f46,f204])).
% 1.65/0.60  fof(f204,plain,(
% 1.65/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)))),
% 1.65/0.60    inference(resolution,[],[f196,f28])).
% 1.65/0.60  fof(f196,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))))) )),
% 1.65/0.60    inference(resolution,[],[f188,f51])).
% 1.65/0.60  fof(f188,plain,(
% 1.65/0.60    r1_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(backward_demodulation,[],[f75,f73])).
% 1.65/0.60  fof(f75,plain,(
% 1.65/0.60    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.65/0.60    inference(superposition,[],[f31,f63])).
% 1.65/0.60  fof(f369,plain,(
% 1.65/0.60    ( ! [X2] : (k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK2,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,X2)))) )),
% 1.65/0.60    inference(forward_demodulation,[],[f361,f49])).
% 1.65/0.60  fof(f361,plain,(
% 1.65/0.60    ( ! [X2] : (k4_xboole_0(k5_xboole_0(sK2,X2),k4_xboole_0(k5_xboole_0(sK2,X2),k4_xboole_0(sK2,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK2,k1_xboole_0))))) )),
% 1.65/0.60    inference(superposition,[],[f53,f338])).
% 1.65/0.60  fof(f53,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1))) )),
% 1.65/0.60    inference(definition_unfolding,[],[f41,f35,f35,f35])).
% 1.65/0.60  fof(f41,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f5])).
% 1.65/0.60  fof(f5,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.65/0.60  fof(f398,plain,(
% 1.65/0.60    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0))),
% 1.65/0.60    inference(superposition,[],[f46,f389])).
% 1.65/0.60  fof(f475,plain,(
% 1.65/0.60    k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2) = k5_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))),
% 1.65/0.60    inference(superposition,[],[f46,f341])).
% 1.65/0.60  fof(f39,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 1.65/0.60    inference(cnf_transformation,[],[f23])).
% 1.65/0.60  fof(f23,plain,(
% 1.65/0.60    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 1.65/0.60    inference(ennf_transformation,[],[f8])).
% 1.65/0.60  fof(f8,axiom,(
% 1.65/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 1.65/0.60  % SZS output end Proof for theBenchmark
% 1.65/0.60  % (24717)------------------------------
% 1.65/0.60  % (24717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.60  % (24717)Termination reason: Refutation
% 1.65/0.60  
% 1.65/0.60  % (24717)Memory used [KB]: 2174
% 1.65/0.60  % (24717)Time elapsed: 0.168 s
% 1.65/0.60  % (24717)------------------------------
% 1.65/0.60  % (24717)------------------------------
% 1.65/0.60  % (24695)Success in time 0.23 s
%------------------------------------------------------------------------------
