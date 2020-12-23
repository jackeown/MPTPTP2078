%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:23 EST 2020

% Result     : Theorem 9.15s
% Output     : Refutation 9.15s
% Verified   : 
% Statistics : Number of formulae       :  138 (1417 expanded)
%              Number of leaves         :   22 ( 450 expanded)
%              Depth                    :   24
%              Number of atoms          :  265 (1998 expanded)
%              Number of equality atoms :  106 (1343 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9888,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f8728,f8783,f8771,f8830,f1184])).

fof(f1184,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(trivial_inequality_removal,[],[f1173])).

fof(f1173,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f393,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f73,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f393,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f390,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f390,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f90,f387])).

fof(f387,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f358,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f358,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f51,f36])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f90,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f77,f38])).

fof(f77,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f73,f43,f73])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f8830,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1))) ),
    inference(forward_demodulation,[],[f8799,f39])).

fof(f8799,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),sK2)) ),
    inference(unit_resulting_resolution,[],[f1008,f8783,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1008,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f89,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f89,plain,(
    ! [X4,X2,X1] : sP5(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8771,plain,(
    ! [X0,X1] : r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1))) ),
    inference(forward_demodulation,[],[f8736,f39])).

fof(f8736,plain,(
    ! [X0,X1] : r2_hidden(sK1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f1006,f8728,f56])).

fof(f1006,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f87,f86])).

fof(f87,plain,(
    ! [X4,X0,X1] : sP5(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8783,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f8777])).

fof(f8777,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f8719,f88])).

fof(f88,plain,(
    ! [X4,X2,X0] : sP5(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8719,plain,(
    ! [X25] :
      ( ~ sP5(X25,sK1,sK0,sK0)
      | ~ r2_hidden(X25,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(resolution,[],[f1010,f3272])).

fof(f3272,plain,
    ( r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f3264])).

fof(f3264,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f47,f3219])).

fof(f3219,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3218,f94])).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3218,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3217,f1985])).

fof(f1985,plain,(
    ! [X70,X68,X69] : k3_xboole_0(k5_xboole_0(X68,X69),X70) = k3_xboole_0(k5_xboole_0(X69,X68),X70) ),
    inference(global_subsumption,[],[f227,f1950])).

fof(f1950,plain,(
    ! [X70,X68,X69] :
      ( k3_xboole_0(k5_xboole_0(X68,X69),X70) = k3_xboole_0(k5_xboole_0(X69,X68),X70)
      | ~ r1_xboole_0(k1_xboole_0,X70) ) ),
    inference(superposition,[],[f395,f539])).

fof(f539,plain,(
    ! [X43,X42] : k5_xboole_0(X43,X42) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X42,X43)) ),
    inference(superposition,[],[f153,f94])).

fof(f153,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f50,f39])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f395,plain,(
    ! [X6,X7,X5] :
      ( k3_xboole_0(X7,X6) = k3_xboole_0(k5_xboole_0(X5,X7),X6)
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(forward_demodulation,[],[f360,f94])).

fof(f360,plain,(
    ! [X6,X7,X5] :
      ( k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,X6))
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f51,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f227,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(global_subsumption,[],[f171,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k1_xboole_0,X0),X1)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f224,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f54,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f40,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f37,f43,f74])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_xboole_0,X0),X1)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f170,f45])).

fof(f170,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X2)
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f53,f93])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3217,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3216,f38])).

fof(f3216,plain,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3215,f93])).

fof(f3215,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3143,f153])).

fof(f3143,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f880,f392])).

fof(f392,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f389,f39])).

fof(f389,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f91,f387])).

fof(f91,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f76,f38])).

fof(f76,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f73,f43,f73])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f880,plain,(
    ! [X6,X5] : k3_xboole_0(X6,k5_xboole_0(X6,X5)) = k5_xboole_0(X6,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f387,f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1010,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ r1_xboole_0(X8,k6_enumset1(X7,X7,X7,X7,X7,X7,X6,X5))
      | ~ r2_hidden(X4,X8)
      | ~ sP5(X4,X5,X6,X7) ) ),
    inference(resolution,[],[f86,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8728,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f8722])).

fof(f8722,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f8718,f87])).

fof(f8718,plain,(
    ! [X24] :
      ( ~ sP5(X24,sK1,sK0,sK0)
      | ~ r2_hidden(X24,sK2)
      | ~ r2_hidden(sK1,sK2) ) ),
    inference(resolution,[],[f1010,f3297])).

fof(f3297,plain,
    ( r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f3289])).

fof(f3289,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f47,f3224])).

fof(f3224,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3223,f94])).

fof(f3223,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3222,f1985])).

fof(f3222,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3221,f38])).

fof(f3221,plain,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3220,f93])).

fof(f3220,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3144,f153])).

fof(f3144,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f880,f391])).

fof(f391,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f388,f39])).

fof(f388,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f92,f387])).

fof(f92,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f75,f38])).

fof(f75,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f34,f73,f43,f73])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:08:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (2700)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (2687)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (2679)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.54  % (2676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (2675)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (2703)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (2672)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.54  % (2677)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.55  % (2699)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (2702)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.55  % (2674)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.55  % (2685)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.55  % (2674)Refutation not found, incomplete strategy% (2674)------------------------------
% 1.35/0.55  % (2674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2674)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2674)Memory used [KB]: 10746
% 1.35/0.55  % (2674)Time elapsed: 0.132 s
% 1.35/0.55  % (2674)------------------------------
% 1.35/0.55  % (2674)------------------------------
% 1.35/0.55  % (2701)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (2697)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.55  % (2686)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.56  % (2691)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.56  % (2692)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.56  % (2693)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (2681)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.56  % (2688)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.56  % (2691)Refutation not found, incomplete strategy% (2691)------------------------------
% 1.50/0.56  % (2691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (2691)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (2691)Memory used [KB]: 10618
% 1.50/0.56  % (2691)Time elapsed: 0.146 s
% 1.50/0.56  % (2691)------------------------------
% 1.50/0.56  % (2691)------------------------------
% 1.50/0.56  % (2694)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.56  % (2681)Refutation not found, incomplete strategy% (2681)------------------------------
% 1.50/0.56  % (2681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (2681)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (2681)Memory used [KB]: 10618
% 1.50/0.56  % (2681)Time elapsed: 0.141 s
% 1.50/0.56  % (2681)------------------------------
% 1.50/0.56  % (2681)------------------------------
% 1.50/0.56  % (2682)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (2696)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.57  % (2684)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.57  % (2695)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.57  % (2680)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.57  % (2673)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.57  % (2698)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.57  % (2683)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.58  % (2690)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.31/0.70  % (2733)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.31/0.70  % (2734)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.31/0.71  % (2735)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.38/0.85  % (2677)Time limit reached!
% 3.38/0.85  % (2677)------------------------------
% 3.38/0.85  % (2677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.38/0.85  % (2677)Termination reason: Time limit
% 3.38/0.85  % (2677)Termination phase: Saturation
% 3.38/0.85  
% 3.38/0.85  % (2677)Memory used [KB]: 11001
% 3.38/0.85  % (2677)Time elapsed: 0.400 s
% 3.38/0.85  % (2677)------------------------------
% 3.38/0.85  % (2677)------------------------------
% 3.64/0.91  % (2683)Time limit reached!
% 3.64/0.91  % (2683)------------------------------
% 3.64/0.91  % (2683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.64/0.92  % (2673)Time limit reached!
% 3.64/0.92  % (2673)------------------------------
% 3.64/0.92  % (2673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.93  % (2683)Termination reason: Time limit
% 4.15/0.93  % (2683)Termination phase: Saturation
% 4.15/0.93  
% 4.15/0.93  % (2683)Memory used [KB]: 14967
% 4.15/0.93  % (2683)Time elapsed: 0.500 s
% 4.15/0.93  % (2683)------------------------------
% 4.15/0.93  % (2683)------------------------------
% 4.15/0.93  % (2672)Time limit reached!
% 4.15/0.93  % (2672)------------------------------
% 4.15/0.93  % (2672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.93  % (2672)Termination reason: Time limit
% 4.15/0.93  
% 4.15/0.93  % (2672)Memory used [KB]: 2302
% 4.15/0.93  % (2672)Time elapsed: 0.511 s
% 4.15/0.93  % (2672)------------------------------
% 4.15/0.93  % (2672)------------------------------
% 4.15/0.93  % (2673)Termination reason: Time limit
% 4.15/0.93  
% 4.15/0.93  % (2673)Memory used [KB]: 8187
% 4.15/0.93  % (2673)Time elapsed: 0.505 s
% 4.15/0.93  % (2673)------------------------------
% 4.15/0.93  % (2673)------------------------------
% 4.15/0.94  % (2685)Time limit reached!
% 4.15/0.94  % (2685)------------------------------
% 4.15/0.94  % (2685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.94  % (2685)Termination reason: Time limit
% 4.15/0.94  
% 4.15/0.94  % (2685)Memory used [KB]: 8955
% 4.15/0.94  % (2685)Time elapsed: 0.521 s
% 4.15/0.94  % (2685)------------------------------
% 4.15/0.94  % (2685)------------------------------
% 4.15/0.96  % (2747)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.44/1.01  % (2690)Time limit reached!
% 4.44/1.01  % (2690)------------------------------
% 4.44/1.01  % (2690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.02  % (2702)Time limit reached!
% 4.44/1.02  % (2702)------------------------------
% 4.44/1.02  % (2702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.03  % (2690)Termination reason: Time limit
% 4.44/1.03  % (2690)Termination phase: Saturation
% 4.44/1.03  
% 4.44/1.03  % (2690)Memory used [KB]: 16375
% 4.44/1.03  % (2690)Time elapsed: 0.600 s
% 4.44/1.03  % (2690)------------------------------
% 4.44/1.03  % (2690)------------------------------
% 4.44/1.03  % (2702)Termination reason: Time limit
% 4.44/1.03  % (2702)Termination phase: Saturation
% 4.44/1.03  
% 4.44/1.03  % (2702)Memory used [KB]: 9594
% 4.44/1.03  % (2702)Time elapsed: 0.600 s
% 4.44/1.03  % (2702)------------------------------
% 4.44/1.03  % (2702)------------------------------
% 4.85/1.04  % (2680)Time limit reached!
% 4.85/1.04  % (2680)------------------------------
% 4.85/1.04  % (2680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.04  % (2680)Termination reason: Time limit
% 4.85/1.04  
% 4.85/1.04  % (2680)Memory used [KB]: 11385
% 4.85/1.04  % (2680)Time elapsed: 0.618 s
% 4.85/1.04  % (2680)------------------------------
% 4.85/1.04  % (2680)------------------------------
% 4.85/1.05  % (2750)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.85/1.06  % (2749)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.85/1.07  % (2751)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.57/1.09  % (2748)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 6.05/1.15  % (2752)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.05/1.16  % (2752)Refutation not found, incomplete strategy% (2752)------------------------------
% 6.05/1.16  % (2752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.05/1.16  % (2752)Termination reason: Refutation not found, incomplete strategy
% 6.05/1.16  
% 6.05/1.16  % (2752)Memory used [KB]: 1791
% 6.05/1.16  % (2752)Time elapsed: 0.105 s
% 6.05/1.16  % (2752)------------------------------
% 6.05/1.16  % (2752)------------------------------
% 6.05/1.16  % (2753)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.33/1.18  % (2754)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.33/1.22  % (2695)Time limit reached!
% 6.33/1.22  % (2695)------------------------------
% 6.33/1.22  % (2695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.33/1.22  % (2695)Termination reason: Time limit
% 6.33/1.22  
% 6.33/1.22  % (2695)Memory used [KB]: 2942
% 6.33/1.22  % (2695)Time elapsed: 0.808 s
% 6.33/1.22  % (2695)------------------------------
% 6.33/1.22  % (2695)------------------------------
% 7.00/1.28  % (2755)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.00/1.32  % (2747)Time limit reached!
% 7.00/1.32  % (2747)------------------------------
% 7.00/1.32  % (2747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.00/1.32  % (2747)Termination reason: Time limit
% 7.00/1.32  % (2747)Termination phase: Saturation
% 7.00/1.32  
% 7.00/1.32  % (2747)Memory used [KB]: 8827
% 7.00/1.32  % (2747)Time elapsed: 0.400 s
% 7.00/1.32  % (2747)------------------------------
% 7.00/1.32  % (2747)------------------------------
% 7.77/1.37  % (2756)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.77/1.39  % (2748)Time limit reached!
% 7.77/1.39  % (2748)------------------------------
% 7.77/1.39  % (2748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.77/1.39  % (2748)Termination reason: Time limit
% 7.77/1.39  % (2748)Termination phase: Saturation
% 7.77/1.39  
% 7.77/1.39  % (2748)Memory used [KB]: 13048
% 7.77/1.39  % (2748)Time elapsed: 0.415 s
% 7.77/1.39  % (2748)------------------------------
% 7.77/1.39  % (2748)------------------------------
% 8.30/1.44  % (2757)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 8.30/1.44  % (2757)Refutation not found, incomplete strategy% (2757)------------------------------
% 8.30/1.44  % (2757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.30/1.44  % (2757)Termination reason: Refutation not found, incomplete strategy
% 8.30/1.44  
% 8.30/1.44  % (2757)Memory used [KB]: 1663
% 8.30/1.44  % (2757)Time elapsed: 0.106 s
% 8.30/1.44  % (2757)------------------------------
% 8.30/1.44  % (2757)------------------------------
% 8.55/1.53  % (2758)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.15/1.58  % (2759)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.15/1.62  % (2696)Time limit reached!
% 9.15/1.62  % (2696)------------------------------
% 9.15/1.62  % (2696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.15/1.62  % (2696)Termination reason: Time limit
% 9.15/1.62  
% 9.15/1.62  % (2696)Memory used [KB]: 19189
% 9.15/1.62  % (2696)Time elapsed: 1.206 s
% 9.15/1.62  % (2696)------------------------------
% 9.15/1.62  % (2696)------------------------------
% 9.15/1.62  % (2698)Refutation found. Thanks to Tanya!
% 9.15/1.62  % SZS status Theorem for theBenchmark
% 9.15/1.62  % SZS output start Proof for theBenchmark
% 9.15/1.62  fof(f9888,plain,(
% 9.15/1.62    $false),
% 9.15/1.62    inference(unit_resulting_resolution,[],[f8728,f8783,f8771,f8830,f1184])).
% 9.15/1.62  fof(f1184,plain,(
% 9.15/1.62    ~r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | ~r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 9.15/1.62    inference(trivial_inequality_removal,[],[f1173])).
% 9.15/1.62  fof(f1173,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 9.15/1.62    inference(superposition,[],[f393,f80])).
% 9.15/1.62  fof(f80,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 9.15/1.62    inference(definition_unfolding,[],[f52,f73,f73])).
% 9.15/1.62  fof(f73,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 9.15/1.62    inference(definition_unfolding,[],[f42,f72])).
% 9.15/1.62  fof(f72,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 9.15/1.62    inference(definition_unfolding,[],[f49,f71])).
% 9.15/1.62  fof(f71,plain,(
% 9.15/1.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 9.15/1.62    inference(definition_unfolding,[],[f57,f70])).
% 9.15/1.62  fof(f70,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 9.15/1.62    inference(definition_unfolding,[],[f66,f69])).
% 9.15/1.62  fof(f69,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 9.15/1.62    inference(definition_unfolding,[],[f67,f68])).
% 9.15/1.62  fof(f68,plain,(
% 9.15/1.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f19])).
% 9.15/1.62  fof(f19,axiom,(
% 9.15/1.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 9.15/1.62  fof(f67,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f18])).
% 9.15/1.62  fof(f18,axiom,(
% 9.15/1.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 9.15/1.62  fof(f66,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f17])).
% 9.15/1.62  fof(f17,axiom,(
% 9.15/1.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 9.15/1.62  fof(f57,plain,(
% 9.15/1.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f16])).
% 9.15/1.62  fof(f16,axiom,(
% 9.15/1.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 9.15/1.62  fof(f49,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f15])).
% 9.15/1.62  fof(f15,axiom,(
% 9.15/1.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 9.15/1.62  fof(f42,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f14])).
% 9.15/1.62  fof(f14,axiom,(
% 9.15/1.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 9.15/1.62  fof(f52,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f29])).
% 9.15/1.62  fof(f29,plain,(
% 9.15/1.62    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 9.15/1.62    inference(flattening,[],[f28])).
% 9.15/1.62  fof(f28,plain,(
% 9.15/1.62    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 9.15/1.62    inference(ennf_transformation,[],[f21])).
% 9.15/1.62  fof(f21,axiom,(
% 9.15/1.62    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 9.15/1.62  fof(f393,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f390,f39])).
% 9.15/1.62  fof(f39,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f2])).
% 9.15/1.62  fof(f2,axiom,(
% 9.15/1.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 9.15/1.62  fof(f390,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(backward_demodulation,[],[f90,f387])).
% 9.15/1.62  fof(f387,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 9.15/1.62    inference(forward_demodulation,[],[f358,f38])).
% 9.15/1.62  fof(f38,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f1])).
% 9.15/1.62  fof(f1,axiom,(
% 9.15/1.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.15/1.62  fof(f358,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 9.15/1.62    inference(superposition,[],[f51,f36])).
% 9.15/1.62  fof(f36,plain,(
% 9.15/1.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 9.15/1.62    inference(cnf_transformation,[],[f24])).
% 9.15/1.62  fof(f24,plain,(
% 9.15/1.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 9.15/1.62    inference(rectify,[],[f4])).
% 9.15/1.62  fof(f4,axiom,(
% 9.15/1.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 9.15/1.62  fof(f51,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f8])).
% 9.15/1.62  fof(f8,axiom,(
% 9.15/1.62    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 9.15/1.62  fof(f90,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(backward_demodulation,[],[f77,f38])).
% 9.15/1.62  fof(f77,plain,(
% 9.15/1.62    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 9.15/1.62    inference(definition_unfolding,[],[f32,f73,f43,f73])).
% 9.15/1.62  fof(f43,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.15/1.62    inference(cnf_transformation,[],[f7])).
% 9.15/1.62  fof(f7,axiom,(
% 9.15/1.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 9.15/1.62  fof(f32,plain,(
% 9.15/1.62    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 9.15/1.62    inference(cnf_transformation,[],[f26])).
% 9.15/1.62  fof(f26,plain,(
% 9.15/1.62    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 9.15/1.62    inference(ennf_transformation,[],[f23])).
% 9.15/1.62  fof(f23,negated_conjecture,(
% 9.15/1.62    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 9.15/1.62    inference(negated_conjecture,[],[f22])).
% 9.15/1.62  fof(f22,conjecture,(
% 9.15/1.62    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 9.15/1.62  fof(f8830,plain,(
% 9.15/1.62    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)))) )),
% 9.15/1.62    inference(forward_demodulation,[],[f8799,f39])).
% 9.15/1.62  fof(f8799,plain,(
% 9.15/1.62    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),sK2))) )),
% 9.15/1.62    inference(unit_resulting_resolution,[],[f1008,f8783,f56])).
% 9.15/1.62  fof(f56,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f30])).
% 9.15/1.62  fof(f30,plain,(
% 9.15/1.62    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 9.15/1.62    inference(ennf_transformation,[],[f5])).
% 9.15/1.62  fof(f5,axiom,(
% 9.15/1.62    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 9.15/1.62  fof(f1008,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 9.15/1.62    inference(unit_resulting_resolution,[],[f89,f86])).
% 9.15/1.62  fof(f86,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 9.15/1.62    inference(equality_resolution,[],[f84])).
% 9.15/1.62  fof(f84,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 9.15/1.62    inference(definition_unfolding,[],[f62,f72])).
% 9.15/1.62  fof(f62,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 9.15/1.62    inference(cnf_transformation,[],[f31])).
% 9.15/1.62  fof(f31,plain,(
% 9.15/1.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 9.15/1.62    inference(ennf_transformation,[],[f13])).
% 9.15/1.62  fof(f13,axiom,(
% 9.15/1.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 9.15/1.62  fof(f89,plain,(
% 9.15/1.62    ( ! [X4,X2,X1] : (sP5(X4,X2,X1,X4)) )),
% 9.15/1.62    inference(equality_resolution,[],[f58])).
% 9.15/1.62  fof(f58,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP5(X4,X2,X1,X0)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f31])).
% 9.15/1.62  fof(f8771,plain,(
% 9.15/1.62    ( ! [X0,X1] : (r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1)))) )),
% 9.15/1.62    inference(forward_demodulation,[],[f8736,f39])).
% 9.15/1.62  fof(f8736,plain,(
% 9.15/1.62    ( ! [X0,X1] : (r2_hidden(sK1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1),sK2))) )),
% 9.15/1.62    inference(unit_resulting_resolution,[],[f1006,f8728,f56])).
% 9.15/1.62  fof(f1006,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) )),
% 9.15/1.62    inference(unit_resulting_resolution,[],[f87,f86])).
% 9.15/1.62  fof(f87,plain,(
% 9.15/1.62    ( ! [X4,X0,X1] : (sP5(X4,X4,X1,X0)) )),
% 9.15/1.62    inference(equality_resolution,[],[f60])).
% 9.15/1.62  fof(f60,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP5(X4,X2,X1,X0)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f31])).
% 9.15/1.62  fof(f8783,plain,(
% 9.15/1.62    ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(duplicate_literal_removal,[],[f8777])).
% 9.15/1.62  fof(f8777,plain,(
% 9.15/1.62    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(resolution,[],[f8719,f88])).
% 9.15/1.62  fof(f88,plain,(
% 9.15/1.62    ( ! [X4,X2,X0] : (sP5(X4,X2,X4,X0)) )),
% 9.15/1.62    inference(equality_resolution,[],[f59])).
% 9.15/1.62  fof(f59,plain,(
% 9.15/1.62    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP5(X4,X2,X1,X0)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f31])).
% 9.15/1.62  fof(f8719,plain,(
% 9.15/1.62    ( ! [X25] : (~sP5(X25,sK1,sK0,sK0) | ~r2_hidden(X25,sK2) | ~r2_hidden(sK0,sK2)) )),
% 9.15/1.62    inference(resolution,[],[f1010,f3272])).
% 9.15/1.62  fof(f3272,plain,(
% 9.15/1.62    r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(trivial_inequality_removal,[],[f3264])).
% 9.15/1.62  fof(f3264,plain,(
% 9.15/1.62    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(superposition,[],[f47,f3219])).
% 9.15/1.62  fof(f3219,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3218,f94])).
% 9.15/1.62  fof(f94,plain,(
% 9.15/1.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 9.15/1.62    inference(superposition,[],[f39,f35])).
% 9.15/1.62  fof(f35,plain,(
% 9.15/1.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.15/1.62    inference(cnf_transformation,[],[f11])).
% 9.15/1.62  fof(f11,axiom,(
% 9.15/1.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 9.15/1.62  fof(f3218,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3217,f1985])).
% 9.15/1.62  fof(f1985,plain,(
% 9.15/1.62    ( ! [X70,X68,X69] : (k3_xboole_0(k5_xboole_0(X68,X69),X70) = k3_xboole_0(k5_xboole_0(X69,X68),X70)) )),
% 9.15/1.62    inference(global_subsumption,[],[f227,f1950])).
% 9.15/1.62  fof(f1950,plain,(
% 9.15/1.62    ( ! [X70,X68,X69] : (k3_xboole_0(k5_xboole_0(X68,X69),X70) = k3_xboole_0(k5_xboole_0(X69,X68),X70) | ~r1_xboole_0(k1_xboole_0,X70)) )),
% 9.15/1.62    inference(superposition,[],[f395,f539])).
% 9.15/1.62  fof(f539,plain,(
% 9.15/1.62    ( ! [X43,X42] : (k5_xboole_0(X43,X42) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X42,X43))) )),
% 9.15/1.62    inference(superposition,[],[f153,f94])).
% 9.15/1.62  fof(f153,plain,(
% 9.15/1.62    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 9.15/1.62    inference(superposition,[],[f50,f39])).
% 9.15/1.62  fof(f50,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 9.15/1.62    inference(cnf_transformation,[],[f12])).
% 9.15/1.62  fof(f12,axiom,(
% 9.15/1.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 9.15/1.62  fof(f395,plain,(
% 9.15/1.62    ( ! [X6,X7,X5] : (k3_xboole_0(X7,X6) = k3_xboole_0(k5_xboole_0(X5,X7),X6) | ~r1_xboole_0(X5,X6)) )),
% 9.15/1.62    inference(forward_demodulation,[],[f360,f94])).
% 9.15/1.62  fof(f360,plain,(
% 9.15/1.62    ( ! [X6,X7,X5] : (k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,X6)) | ~r1_xboole_0(X5,X6)) )),
% 9.15/1.62    inference(superposition,[],[f51,f48])).
% 9.15/1.62  fof(f48,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f3])).
% 9.15/1.62  fof(f3,axiom,(
% 9.15/1.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 9.15/1.62  fof(f227,plain,(
% 9.15/1.62    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 9.15/1.62    inference(global_subsumption,[],[f171,f225])).
% 9.15/1.62  fof(f225,plain,(
% 9.15/1.62    ( ! [X0,X1] : (~r2_hidden(sK3(k1_xboole_0,X0),X1) | r1_xboole_0(k1_xboole_0,X0)) )),
% 9.15/1.62    inference(resolution,[],[f224,f45])).
% 9.15/1.62  fof(f45,plain,(
% 9.15/1.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f27])).
% 9.15/1.62  fof(f27,plain,(
% 9.15/1.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 9.15/1.62    inference(ennf_transformation,[],[f25])).
% 9.15/1.62  fof(f25,plain,(
% 9.15/1.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 9.15/1.62    inference(rectify,[],[f6])).
% 9.15/1.62  fof(f6,axiom,(
% 9.15/1.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 9.15/1.62  fof(f224,plain,(
% 9.15/1.62    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 9.15/1.62    inference(duplicate_literal_removal,[],[f214])).
% 9.15/1.62  fof(f214,plain,(
% 9.15/1.62    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 9.15/1.62    inference(superposition,[],[f54,f93])).
% 9.15/1.62  fof(f93,plain,(
% 9.15/1.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 9.15/1.62    inference(backward_demodulation,[],[f78,f79])).
% 9.15/1.62  fof(f79,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 9.15/1.62    inference(definition_unfolding,[],[f40,f74])).
% 9.15/1.62  fof(f74,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 9.15/1.62    inference(definition_unfolding,[],[f41,f73])).
% 9.15/1.62  fof(f41,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 9.15/1.62    inference(cnf_transformation,[],[f20])).
% 9.15/1.62  fof(f20,axiom,(
% 9.15/1.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 9.15/1.62  fof(f40,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 9.15/1.62    inference(cnf_transformation,[],[f9])).
% 9.15/1.62  fof(f9,axiom,(
% 9.15/1.62    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 9.15/1.62  fof(f78,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 9.15/1.62    inference(definition_unfolding,[],[f37,f43,f74])).
% 9.15/1.62  fof(f37,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 9.15/1.62    inference(cnf_transformation,[],[f10])).
% 9.15/1.62  fof(f10,axiom,(
% 9.15/1.62    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 9.15/1.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 9.15/1.62  fof(f54,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f30])).
% 9.15/1.62  fof(f171,plain,(
% 9.15/1.62    ( ! [X0,X1] : (r2_hidden(sK3(k1_xboole_0,X0),X1) | r1_xboole_0(k1_xboole_0,X0)) )),
% 9.15/1.62    inference(resolution,[],[f170,f45])).
% 9.15/1.62  fof(f170,plain,(
% 9.15/1.62    ( ! [X2,X3] : (~r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,X2)) )),
% 9.15/1.62    inference(duplicate_literal_removal,[],[f165])).
% 9.15/1.62  fof(f165,plain,(
% 9.15/1.62    ( ! [X2,X3] : (~r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,X2) | r2_hidden(X3,X2)) )),
% 9.15/1.62    inference(superposition,[],[f53,f93])).
% 9.15/1.62  fof(f53,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f30])).
% 9.15/1.62  fof(f3217,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3216,f38])).
% 9.15/1.62  fof(f3216,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0)) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3215,f93])).
% 9.15/1.62  fof(f3215,plain,(
% 9.15/1.62    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3143,f153])).
% 9.15/1.62  fof(f3143,plain,(
% 9.15/1.62    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(superposition,[],[f880,f392])).
% 9.15/1.62  fof(f392,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f389,f39])).
% 9.15/1.62  fof(f389,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(backward_demodulation,[],[f91,f387])).
% 9.15/1.62  fof(f91,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 9.15/1.62    inference(backward_demodulation,[],[f76,f38])).
% 9.15/1.62  fof(f76,plain,(
% 9.15/1.62    ~r2_hidden(sK0,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 9.15/1.62    inference(definition_unfolding,[],[f33,f73,f43,f73])).
% 9.15/1.62  fof(f33,plain,(
% 9.15/1.62    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 9.15/1.62    inference(cnf_transformation,[],[f26])).
% 9.15/1.62  fof(f880,plain,(
% 9.15/1.62    ( ! [X6,X5] : (k3_xboole_0(X6,k5_xboole_0(X6,X5)) = k5_xboole_0(X6,k3_xboole_0(X6,X5))) )),
% 9.15/1.62    inference(superposition,[],[f387,f38])).
% 9.15/1.62  fof(f47,plain,(
% 9.15/1.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f3])).
% 9.15/1.62  fof(f1010,plain,(
% 9.15/1.62    ( ! [X6,X4,X8,X7,X5] : (~r1_xboole_0(X8,k6_enumset1(X7,X7,X7,X7,X7,X7,X6,X5)) | ~r2_hidden(X4,X8) | ~sP5(X4,X5,X6,X7)) )),
% 9.15/1.62    inference(resolution,[],[f86,f44])).
% 9.15/1.62  fof(f44,plain,(
% 9.15/1.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 9.15/1.62    inference(cnf_transformation,[],[f27])).
% 9.15/1.62  fof(f8728,plain,(
% 9.15/1.62    ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(duplicate_literal_removal,[],[f8722])).
% 9.15/1.62  fof(f8722,plain,(
% 9.15/1.62    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(resolution,[],[f8718,f87])).
% 9.15/1.62  fof(f8718,plain,(
% 9.15/1.62    ( ! [X24] : (~sP5(X24,sK1,sK0,sK0) | ~r2_hidden(X24,sK2) | ~r2_hidden(sK1,sK2)) )),
% 9.15/1.62    inference(resolution,[],[f1010,f3297])).
% 9.15/1.62  fof(f3297,plain,(
% 9.15/1.62    r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(trivial_inequality_removal,[],[f3289])).
% 9.15/1.62  fof(f3289,plain,(
% 9.15/1.62    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(superposition,[],[f47,f3224])).
% 9.15/1.62  fof(f3224,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3223,f94])).
% 9.15/1.62  fof(f3223,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3222,f1985])).
% 9.15/1.62  fof(f3222,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3221,f38])).
% 9.15/1.62  fof(f3221,plain,(
% 9.15/1.62    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0)) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3220,f93])).
% 9.15/1.62  fof(f3220,plain,(
% 9.15/1.62    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f3144,f153])).
% 9.15/1.62  fof(f3144,plain,(
% 9.15/1.62    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(superposition,[],[f880,f391])).
% 9.15/1.62  fof(f391,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(forward_demodulation,[],[f388,f39])).
% 9.15/1.62  fof(f388,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(backward_demodulation,[],[f92,f387])).
% 9.15/1.62  fof(f92,plain,(
% 9.15/1.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 9.15/1.62    inference(backward_demodulation,[],[f75,f38])).
% 9.15/1.62  fof(f75,plain,(
% 9.15/1.62    ~r2_hidden(sK1,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 9.15/1.62    inference(definition_unfolding,[],[f34,f73,f43,f73])).
% 9.15/1.62  fof(f34,plain,(
% 9.15/1.62    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 9.15/1.62    inference(cnf_transformation,[],[f26])).
% 9.15/1.62  % SZS output end Proof for theBenchmark
% 9.15/1.62  % (2698)------------------------------
% 9.15/1.62  % (2698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.15/1.62  % (2698)Termination reason: Refutation
% 9.15/1.62  
% 9.15/1.62  % (2698)Memory used [KB]: 18038
% 9.15/1.62  % (2698)Time elapsed: 1.185 s
% 9.15/1.62  % (2698)------------------------------
% 9.15/1.62  % (2698)------------------------------
% 9.15/1.62  % (2671)Success in time 1.243 s
%------------------------------------------------------------------------------
