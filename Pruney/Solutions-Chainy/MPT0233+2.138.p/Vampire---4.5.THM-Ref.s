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
% DateTime   : Thu Dec  3 12:37:22 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 966 expanded)
%              Number of leaves         :   19 ( 325 expanded)
%              Depth                    :   16
%              Number of atoms          :  131 (1123 expanded)
%              Number of equality atoms :   74 ( 929 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1564,plain,(
    $false ),
    inference(resolution,[],[f1383,f1430])).

fof(f1430,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK0)) ),
    inference(backward_demodulation,[],[f165,f1423])).

fof(f1423,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK0) ),
    inference(forward_demodulation,[],[f1369,f1319])).

fof(f1319,plain,(
    ! [X0] : k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f611,f247])).

fof(f247,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) ) ),
    inference(forward_demodulation,[],[f246,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f246,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_xboole_0)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ) ),
    inference(forward_demodulation,[],[f241,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f87,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(unit_resulting_resolution,[],[f63,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f31,f55])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f241,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ) ),
    inference(superposition,[],[f68,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f43,f58,f55,f59,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f59])).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f611,plain,(
    ! [X0] : r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,sK3)) ),
    inference(unit_resulting_resolution,[],[f582,f245,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f245,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7)) ),
    inference(superposition,[],[f63,f68])).

fof(f582,plain,(
    ! [X4] : r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X4,sK3)) ),
    inference(superposition,[],[f557,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f39,f59,f59])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f557,plain,(
    ! [X0] : r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,X0)) ),
    inference(superposition,[],[f83,f68])).

fof(f83,plain,(
    ! [X0] : r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) ),
    inference(unit_resulting_resolution,[],[f63,f62,f41])).

fof(f62,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f26,f60,f60])).

fof(f26,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f1369,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3) ),
    inference(superposition,[],[f1319,f67])).

fof(f165,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f140,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f140,plain,(
    ~ sP5(sK0,sK3,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f27,f28,f27,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f1383,plain,(
    ! [X29] : r2_hidden(X29,k6_enumset1(sK2,sK2,sK2,sK2,sK2,X29,sK3,sK0)) ),
    inference(superposition,[],[f168,f1319])).

fof(f168,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(unit_resulting_resolution,[],[f76,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X4,X2,X0] : sP5(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (30737)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (30729)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (30727)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (30745)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (30721)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (30734)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (30722)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (30749)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (30724)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (30723)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (30725)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (30739)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (30723)Refutation not found, incomplete strategy% (30723)------------------------------
% 0.21/0.54  % (30723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30723)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30723)Memory used [KB]: 10746
% 0.21/0.54  % (30723)Time elapsed: 0.134 s
% 0.21/0.54  % (30723)------------------------------
% 0.21/0.54  % (30723)------------------------------
% 0.21/0.55  % (30752)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (30743)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (30741)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (30740)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (30742)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (30740)Refutation not found, incomplete strategy% (30740)------------------------------
% 0.21/0.55  % (30740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30740)Memory used [KB]: 10618
% 0.21/0.55  % (30740)Time elapsed: 0.137 s
% 0.21/0.55  % (30740)------------------------------
% 0.21/0.55  % (30740)------------------------------
% 0.21/0.55  % (30735)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (30732)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (30733)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (30744)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (30738)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (30733)Refutation not found, incomplete strategy% (30733)------------------------------
% 0.21/0.55  % (30733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30733)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30733)Memory used [KB]: 10618
% 0.21/0.55  % (30733)Time elapsed: 0.149 s
% 0.21/0.55  % (30733)------------------------------
% 0.21/0.55  % (30733)------------------------------
% 0.21/0.56  % (30734)Refutation not found, incomplete strategy% (30734)------------------------------
% 0.21/0.56  % (30734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30734)Memory used [KB]: 10618
% 0.21/0.56  % (30734)Time elapsed: 0.152 s
% 0.21/0.56  % (30734)------------------------------
% 0.21/0.56  % (30734)------------------------------
% 0.21/0.56  % (30736)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (30748)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (30738)Refutation not found, incomplete strategy% (30738)------------------------------
% 0.21/0.56  % (30738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30738)Memory used [KB]: 6268
% 0.21/0.56  % (30738)Time elapsed: 0.062 s
% 0.21/0.56  % (30738)------------------------------
% 0.21/0.56  % (30738)------------------------------
% 0.21/0.56  % (30746)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (30730)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (30750)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (30747)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (30751)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (30731)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.66/0.59  % (30731)Refutation not found, incomplete strategy% (30731)------------------------------
% 1.66/0.59  % (30731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (30731)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (30731)Memory used [KB]: 10746
% 1.66/0.59  % (30731)Time elapsed: 0.176 s
% 1.66/0.59  % (30731)------------------------------
% 1.66/0.59  % (30731)------------------------------
% 2.12/0.68  % (30774)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.69  % (30775)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.69  % (30776)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.12/0.69  % (30777)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.12/0.71  % (30778)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.12/0.71  % (30779)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.12/0.72  % (30747)Refutation found. Thanks to Tanya!
% 2.12/0.72  % SZS status Theorem for theBenchmark
% 2.12/0.72  % SZS output start Proof for theBenchmark
% 2.12/0.72  fof(f1564,plain,(
% 2.12/0.72    $false),
% 2.12/0.72    inference(resolution,[],[f1383,f1430])).
% 2.12/0.72  fof(f1430,plain,(
% 2.12/0.72    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK0))),
% 2.12/0.72    inference(backward_demodulation,[],[f165,f1423])).
% 2.12/0.72  fof(f1423,plain,(
% 2.12/0.72    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK0)),
% 2.12/0.72    inference(forward_demodulation,[],[f1369,f1319])).
% 2.12/0.72  fof(f1319,plain,(
% 2.12/0.72    ( ! [X0] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,X0,sK3,sK0)) )),
% 2.12/0.72    inference(unit_resulting_resolution,[],[f611,f247])).
% 2.12/0.72  fof(f247,plain,(
% 2.12/0.72    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0)) )),
% 2.12/0.72    inference(forward_demodulation,[],[f246,f29])).
% 2.12/0.72  fof(f29,plain,(
% 2.12/0.72    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.72    inference(cnf_transformation,[],[f6])).
% 2.12/0.72  fof(f6,axiom,(
% 2.12/0.72    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.12/0.72  fof(f246,plain,(
% 2.12/0.72    ( ! [X2,X0,X3,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_xboole_0) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) )),
% 2.12/0.72    inference(forward_demodulation,[],[f241,f94])).
% 2.12/0.72  fof(f94,plain,(
% 2.12/0.72    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.12/0.72    inference(forward_demodulation,[],[f87,f64])).
% 2.12/0.72  fof(f64,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 2.12/0.72    inference(definition_unfolding,[],[f32,f55])).
% 2.12/0.72  fof(f55,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.12/0.72    inference(definition_unfolding,[],[f35,f34])).
% 2.12/0.72  fof(f34,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.72    inference(cnf_transformation,[],[f2])).
% 2.12/0.72  fof(f2,axiom,(
% 2.12/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.72  fof(f35,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.12/0.72    inference(cnf_transformation,[],[f8])).
% 2.12/0.72  fof(f8,axiom,(
% 2.12/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.12/0.72  fof(f32,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.12/0.72    inference(cnf_transformation,[],[f4])).
% 2.12/0.72  fof(f4,axiom,(
% 2.12/0.72    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.12/0.72  fof(f87,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 2.12/0.72    inference(unit_resulting_resolution,[],[f63,f66])).
% 2.12/0.72  fof(f66,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f37,f34])).
% 2.12/0.72  fof(f37,plain,(
% 2.12/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.12/0.72    inference(cnf_transformation,[],[f1])).
% 2.12/0.72  fof(f1,axiom,(
% 2.12/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.12/0.72  fof(f63,plain,(
% 2.12/0.72    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.12/0.72    inference(definition_unfolding,[],[f31,f55])).
% 2.12/0.72  fof(f31,plain,(
% 2.12/0.72    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.12/0.72    inference(cnf_transformation,[],[f7])).
% 2.12/0.72  fof(f7,axiom,(
% 2.12/0.72    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.12/0.72  fof(f241,plain,(
% 2.12/0.72    ( ! [X2,X0,X3,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) )),
% 2.12/0.72    inference(superposition,[],[f68,f36])).
% 2.12/0.72  fof(f36,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f22])).
% 2.12/0.72  fof(f22,plain,(
% 2.12/0.72    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.12/0.72    inference(ennf_transformation,[],[f5])).
% 2.12/0.72  fof(f5,axiom,(
% 2.12/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.12/0.72  fof(f68,plain,(
% 2.12/0.72    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))))) )),
% 2.12/0.72    inference(definition_unfolding,[],[f43,f58,f55,f59,f61])).
% 2.12/0.72  fof(f61,plain,(
% 2.12/0.72    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f30,f60])).
% 2.12/0.72  fof(f60,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f33,f59])).
% 2.12/0.72  fof(f33,plain,(
% 2.12/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f12])).
% 2.12/0.72  fof(f12,axiom,(
% 2.12/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.12/0.72  fof(f30,plain,(
% 2.12/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f11])).
% 2.12/0.72  fof(f11,axiom,(
% 2.12/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.12/0.72  fof(f59,plain,(
% 2.12/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f40,f58])).
% 2.12/0.72  fof(f40,plain,(
% 2.12/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f13])).
% 2.12/0.72  fof(f13,axiom,(
% 2.12/0.72    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.12/0.72  fof(f58,plain,(
% 2.12/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f42,f57])).
% 2.12/0.72  fof(f57,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f52,f56])).
% 2.12/0.72  fof(f56,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f53,f54])).
% 2.12/0.72  fof(f54,plain,(
% 2.12/0.72    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f17])).
% 2.12/0.72  fof(f17,axiom,(
% 2.12/0.72    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.12/0.72  fof(f53,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f16])).
% 2.12/0.72  fof(f16,axiom,(
% 2.12/0.72    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.12/0.72  fof(f52,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f15])).
% 2.12/0.72  fof(f15,axiom,(
% 2.12/0.72    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.12/0.72  fof(f42,plain,(
% 2.12/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f14])).
% 2.12/0.72  fof(f14,axiom,(
% 2.12/0.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.12/0.72  fof(f43,plain,(
% 2.12/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.12/0.72    inference(cnf_transformation,[],[f10])).
% 2.12/0.72  fof(f10,axiom,(
% 2.12/0.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 2.12/0.72  fof(f611,plain,(
% 2.12/0.72    ( ! [X0] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,sK3))) )),
% 2.12/0.72    inference(unit_resulting_resolution,[],[f582,f245,f41])).
% 2.12/0.72  fof(f41,plain,(
% 2.12/0.72    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f24])).
% 2.12/0.72  fof(f24,plain,(
% 2.12/0.72    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.12/0.72    inference(flattening,[],[f23])).
% 2.12/0.72  fof(f23,plain,(
% 2.12/0.72    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.12/0.72    inference(ennf_transformation,[],[f3])).
% 2.12/0.72  fof(f3,axiom,(
% 2.12/0.72    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.12/0.72  fof(f245,plain,(
% 2.12/0.72    ( ! [X6,X4,X7,X5] : (r1_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) )),
% 2.12/0.72    inference(superposition,[],[f63,f68])).
% 2.12/0.72  fof(f582,plain,(
% 2.12/0.72    ( ! [X4] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X4,sK3))) )),
% 2.12/0.72    inference(superposition,[],[f557,f67])).
% 2.12/0.72  fof(f67,plain,(
% 2.12/0.72    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 2.12/0.72    inference(definition_unfolding,[],[f39,f59,f59])).
% 2.12/0.72  fof(f39,plain,(
% 2.12/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f18])).
% 2.12/0.72  fof(f18,axiom,(
% 2.12/0.72    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 2.12/0.72  fof(f557,plain,(
% 2.12/0.72    ( ! [X0] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,X0))) )),
% 2.12/0.72    inference(superposition,[],[f83,f68])).
% 2.12/0.72  fof(f83,plain,(
% 2.12/0.72    ( ! [X0] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))))) )),
% 2.12/0.72    inference(unit_resulting_resolution,[],[f63,f62,f41])).
% 2.12/0.72  fof(f62,plain,(
% 2.12/0.72    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 2.12/0.72    inference(definition_unfolding,[],[f26,f60,f60])).
% 2.12/0.72  fof(f26,plain,(
% 2.12/0.72    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.12/0.72    inference(cnf_transformation,[],[f21])).
% 2.12/0.72  fof(f21,plain,(
% 2.12/0.72    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.12/0.72    inference(ennf_transformation,[],[f20])).
% 2.12/0.72  fof(f20,negated_conjecture,(
% 2.12/0.72    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.12/0.72    inference(negated_conjecture,[],[f19])).
% 2.12/0.72  fof(f19,conjecture,(
% 2.12/0.72    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 2.12/0.72  fof(f1369,plain,(
% 2.12/0.72    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3)),
% 2.12/0.72    inference(superposition,[],[f1319,f67])).
% 2.12/0.72  fof(f165,plain,(
% 2.12/0.72    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 2.12/0.72    inference(unit_resulting_resolution,[],[f140,f73])).
% 2.12/0.72  fof(f73,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | sP5(X4,X2,X1,X0)) )),
% 2.12/0.72    inference(equality_resolution,[],[f71])).
% 2.12/0.72  fof(f71,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.12/0.72    inference(definition_unfolding,[],[f49,f59])).
% 2.12/0.72  fof(f49,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.12/0.72    inference(cnf_transformation,[],[f25])).
% 2.12/0.72  fof(f25,plain,(
% 2.12/0.72    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.12/0.72    inference(ennf_transformation,[],[f9])).
% 2.12/0.72  fof(f9,axiom,(
% 2.12/0.72    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.12/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.12/0.72  fof(f140,plain,(
% 2.12/0.72    ~sP5(sK0,sK3,sK2,sK2)),
% 2.12/0.72    inference(unit_resulting_resolution,[],[f27,f28,f27,f47])).
% 2.12/0.72  fof(f47,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 2.12/0.72    inference(cnf_transformation,[],[f25])).
% 2.12/0.72  fof(f28,plain,(
% 2.12/0.72    sK0 != sK3),
% 2.12/0.72    inference(cnf_transformation,[],[f21])).
% 2.12/0.72  fof(f27,plain,(
% 2.12/0.72    sK0 != sK2),
% 2.12/0.72    inference(cnf_transformation,[],[f21])).
% 2.12/0.72  fof(f1383,plain,(
% 2.12/0.72    ( ! [X29] : (r2_hidden(X29,k6_enumset1(sK2,sK2,sK2,sK2,sK2,X29,sK3,sK0))) )),
% 2.12/0.72    inference(superposition,[],[f168,f1319])).
% 2.12/0.72  fof(f168,plain,(
% 2.12/0.72    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2))) )),
% 2.12/0.72    inference(unit_resulting_resolution,[],[f76,f74])).
% 2.12/0.72  fof(f74,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 2.12/0.72    inference(equality_resolution,[],[f72])).
% 2.12/0.72  fof(f72,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.12/0.72    inference(definition_unfolding,[],[f48,f59])).
% 2.12/0.72  fof(f48,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.12/0.72    inference(cnf_transformation,[],[f25])).
% 2.12/0.72  fof(f76,plain,(
% 2.12/0.72    ( ! [X4,X2,X0] : (sP5(X4,X2,X4,X0)) )),
% 2.12/0.72    inference(equality_resolution,[],[f45])).
% 2.12/0.72  fof(f45,plain,(
% 2.12/0.72    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP5(X4,X2,X1,X0)) )),
% 2.12/0.72    inference(cnf_transformation,[],[f25])).
% 2.12/0.72  % SZS output end Proof for theBenchmark
% 2.12/0.72  % (30747)------------------------------
% 2.12/0.72  % (30747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.72  % (30747)Termination reason: Refutation
% 2.12/0.72  
% 2.12/0.72  % (30747)Memory used [KB]: 7675
% 2.12/0.72  % (30747)Time elapsed: 0.293 s
% 2.12/0.72  % (30747)------------------------------
% 2.12/0.72  % (30747)------------------------------
% 2.12/0.72  % (30720)Success in time 0.35 s
%------------------------------------------------------------------------------
