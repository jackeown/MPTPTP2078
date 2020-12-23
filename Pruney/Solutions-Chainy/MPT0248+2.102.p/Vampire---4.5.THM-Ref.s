%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:04 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  113 (2168 expanded)
%              Number of leaves         :   21 ( 706 expanded)
%              Depth                    :   29
%              Number of atoms          :  198 (2661 expanded)
%              Number of equality atoms :  127 (2438 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f689,plain,(
    $false ),
    inference(global_subsumption,[],[f654,f688])).

fof(f688,plain,(
    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f677,f102])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f98,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f98,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f93,f86])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f85,f75])).

fof(f75,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f35,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f74,f32])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f34,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f66])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f93,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f52,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f677,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f98,f662])).

fof(f662,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f129,f649,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f649,plain,(
    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f420,f642])).

fof(f642,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f512,f511,f640])).

fof(f640,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f634])).

fof(f634,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f506,f588])).

fof(f588,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f584])).

fof(f584,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f556,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f556,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | k1_xboole_0 = sK1
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f549,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f549,plain,(
    ! [X11] :
      ( ~ r2_hidden(X11,sK2)
      | r2_hidden(X11,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f536])).

fof(f536,plain,(
    ! [X11] :
      ( ~ r2_hidden(X11,sK2)
      | r2_hidden(X11,sK1)
      | r2_hidden(X11,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f154,f513])).

fof(f513,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f505,f212])).

fof(f212,plain,(
    ! [X12,X11] : k5_xboole_0(X11,X12) = k5_xboole_0(X12,X11) ),
    inference(superposition,[],[f98,f192])).

fof(f192,plain,(
    ! [X12,X11] : k5_xboole_0(X12,k5_xboole_0(X11,X12)) = X11 ),
    inference(forward_demodulation,[],[f180,f102])).

fof(f180,plain,(
    ! [X12,X11] : k5_xboole_0(X11,k1_xboole_0) = k5_xboole_0(X12,k5_xboole_0(X11,X12)) ),
    inference(superposition,[],[f98,f96])).

fof(f96,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(superposition,[],[f52,f32])).

fof(f505,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f420,f496])).

fof(f496,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f80,f406])).

fof(f406,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f76,f70])).

fof(f70,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f31,f69,f66])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f65])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f66])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f69,f69])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f154,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_tarski(k5_xboole_0(X10,X11),X12)
      | ~ r2_hidden(X9,X11)
      | r2_hidden(X9,X12)
      | r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f506,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f80,f496])).

fof(f511,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f502])).

fof(f502,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f73,f496])).

fof(f73,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f28,f69])).

fof(f28,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f512,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f500])).

fof(f500,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f71,f496])).

fof(f71,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f30,f69,f69])).

fof(f30,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f420,plain,(
    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f99,f70])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(backward_demodulation,[],[f87,f98])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0) ),
    inference(backward_demodulation,[],[f77,f52])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(definition_unfolding,[],[f37,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f129,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f124,f47])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_xboole_0,X0),X1)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f53,f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f654,plain,(
    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_subsumption,[],[f72,f642])).

fof(f72,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f29,f69])).

fof(f29,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (5988)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (5985)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (6010)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (6008)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (6000)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (5986)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (5987)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (6009)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (5984)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (5986)Refutation not found, incomplete strategy% (5986)------------------------------
% 0.22/0.54  % (5986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5998)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (6006)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (6002)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (5995)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (5999)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (6004)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (5994)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (5992)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (6001)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (6007)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (6012)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (6011)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (6003)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (5989)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (5990)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (6006)Refutation not found, incomplete strategy% (6006)------------------------------
% 0.22/0.55  % (6006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5994)Refutation not found, incomplete strategy% (5994)------------------------------
% 0.22/0.55  % (5994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5991)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (5993)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (5986)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5986)Memory used [KB]: 10746
% 0.22/0.55  % (5986)Time elapsed: 0.125 s
% 0.22/0.55  % (5986)------------------------------
% 0.22/0.55  % (5986)------------------------------
% 0.22/0.55  % (6006)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6006)Memory used [KB]: 10746
% 0.22/0.55  % (6006)Time elapsed: 0.099 s
% 0.22/0.55  % (6006)------------------------------
% 0.22/0.55  % (6006)------------------------------
% 0.22/0.55  % (5996)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (5994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5994)Memory used [KB]: 10618
% 0.22/0.55  % (5994)Time elapsed: 0.141 s
% 0.22/0.55  % (5994)------------------------------
% 0.22/0.55  % (5994)------------------------------
% 0.22/0.56  % (5992)Refutation not found, incomplete strategy% (5992)------------------------------
% 0.22/0.56  % (5992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5992)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (5992)Memory used [KB]: 10746
% 0.22/0.56  % (5992)Time elapsed: 0.145 s
% 0.22/0.56  % (5992)------------------------------
% 0.22/0.56  % (5992)------------------------------
% 0.22/0.56  % (5997)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (5995)Refutation not found, incomplete strategy% (5995)------------------------------
% 0.22/0.56  % (5995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5995)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (5995)Memory used [KB]: 10618
% 0.22/0.56  % (5995)Time elapsed: 0.150 s
% 0.22/0.56  % (5995)------------------------------
% 0.22/0.56  % (5995)------------------------------
% 0.22/0.56  % (6001)Refutation not found, incomplete strategy% (6001)------------------------------
% 0.22/0.56  % (6001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6001)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6001)Memory used [KB]: 10618
% 0.22/0.56  % (6001)Time elapsed: 0.147 s
% 0.22/0.56  % (6001)------------------------------
% 0.22/0.56  % (6001)------------------------------
% 0.22/0.57  % (6013)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (6005)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.57  % (6005)Refutation not found, incomplete strategy% (6005)------------------------------
% 0.22/0.57  % (6005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (6005)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (6005)Memory used [KB]: 1791
% 0.22/0.57  % (6005)Time elapsed: 0.148 s
% 0.22/0.57  % (6005)------------------------------
% 0.22/0.57  % (6005)------------------------------
% 1.64/0.58  % (6008)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f689,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(global_subsumption,[],[f654,f688])).
% 1.64/0.58  fof(f688,plain,(
% 1.64/0.58    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.64/0.58    inference(forward_demodulation,[],[f677,f102])).
% 1.64/0.58  fof(f102,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.58    inference(superposition,[],[f98,f32])).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.64/0.58  fof(f98,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.64/0.58    inference(forward_demodulation,[],[f93,f86])).
% 1.64/0.58  fof(f86,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.64/0.58    inference(backward_demodulation,[],[f85,f75])).
% 1.64/0.58  fof(f75,plain,(
% 1.64/0.58    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f35,f66])).
% 1.64/0.58  fof(f66,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f38,f65])).
% 1.64/0.58  fof(f65,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f39,f64])).
% 1.64/0.58  fof(f64,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f51,f63])).
% 1.64/0.58  fof(f63,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f57,f62])).
% 1.64/0.58  fof(f62,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f58,f61])).
% 1.64/0.58  fof(f61,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f59,f60])).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f18])).
% 1.64/0.58  fof(f18,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f17])).
% 1.64/0.58  fof(f17,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.64/0.58  fof(f58,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f15])).
% 1.64/0.58  fof(f15,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.64/0.58  fof(f51,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f13])).
% 1.64/0.58  fof(f13,axiom,(
% 1.64/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f20])).
% 1.64/0.58  fof(f20,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.64/0.58    inference(rectify,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.64/0.58  fof(f85,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.64/0.58    inference(forward_demodulation,[],[f74,f32])).
% 1.64/0.58  fof(f74,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f34,f67])).
% 1.64/0.58  fof(f67,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f41,f66])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f23])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.64/0.58    inference(rectify,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.64/0.58  fof(f93,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.64/0.58    inference(superposition,[],[f52,f32])).
% 1.64/0.58  fof(f52,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.64/0.58  fof(f677,plain,(
% 1.64/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.64/0.58    inference(superposition,[],[f98,f662])).
% 1.64/0.58  fof(f662,plain,(
% 1.64/0.58    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f129,f649,f44])).
% 1.64/0.58  fof(f44,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.64/0.58    inference(cnf_transformation,[],[f5])).
% 1.64/0.58  fof(f5,axiom,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.58  fof(f649,plain,(
% 1.64/0.58    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.64/0.58    inference(backward_demodulation,[],[f420,f642])).
% 1.64/0.60  fof(f642,plain,(
% 1.64/0.60    k1_xboole_0 = sK1),
% 1.64/0.60    inference(global_subsumption,[],[f512,f511,f640])).
% 1.64/0.60  fof(f640,plain,(
% 1.64/0.60    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.64/0.60    inference(duplicate_literal_removal,[],[f634])).
% 1.64/0.60  fof(f634,plain,(
% 1.64/0.60    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.64/0.60    inference(resolution,[],[f506,f588])).
% 1.64/0.60  fof(f588,plain,(
% 1.64/0.60    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 1.64/0.60    inference(duplicate_literal_removal,[],[f584])).
% 1.64/0.60  fof(f584,plain,(
% 1.64/0.60    k1_xboole_0 = sK1 | r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 1.64/0.60    inference(resolution,[],[f556,f47])).
% 1.64/0.60  fof(f47,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f26])).
% 1.64/0.60  fof(f26,plain,(
% 1.64/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.64/0.60    inference(ennf_transformation,[],[f1])).
% 1.64/0.60  fof(f1,axiom,(
% 1.64/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.64/0.60  fof(f556,plain,(
% 1.64/0.60    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | k1_xboole_0 = sK1 | r1_tarski(sK2,X0)) )),
% 1.64/0.60    inference(resolution,[],[f549,f46])).
% 1.64/0.60  fof(f46,plain,(
% 1.64/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f26])).
% 1.64/0.60  fof(f549,plain,(
% 1.64/0.60    ( ! [X11] : (~r2_hidden(X11,sK2) | r2_hidden(X11,sK1) | k1_xboole_0 = sK1) )),
% 1.64/0.60    inference(duplicate_literal_removal,[],[f536])).
% 1.64/0.60  fof(f536,plain,(
% 1.64/0.60    ( ! [X11] : (~r2_hidden(X11,sK2) | r2_hidden(X11,sK1) | r2_hidden(X11,sK1) | k1_xboole_0 = sK1) )),
% 1.64/0.60    inference(resolution,[],[f154,f513])).
% 1.64/0.60  fof(f513,plain,(
% 1.64/0.60    r1_tarski(k5_xboole_0(sK1,sK2),sK1) | k1_xboole_0 = sK1),
% 1.64/0.60    inference(forward_demodulation,[],[f505,f212])).
% 1.64/0.60  fof(f212,plain,(
% 1.64/0.60    ( ! [X12,X11] : (k5_xboole_0(X11,X12) = k5_xboole_0(X12,X11)) )),
% 1.64/0.60    inference(superposition,[],[f98,f192])).
% 1.64/0.60  fof(f192,plain,(
% 1.64/0.60    ( ! [X12,X11] : (k5_xboole_0(X12,k5_xboole_0(X11,X12)) = X11) )),
% 1.64/0.60    inference(forward_demodulation,[],[f180,f102])).
% 1.64/0.60  fof(f180,plain,(
% 1.64/0.60    ( ! [X12,X11] : (k5_xboole_0(X11,k1_xboole_0) = k5_xboole_0(X12,k5_xboole_0(X11,X12))) )),
% 1.64/0.60    inference(superposition,[],[f98,f96])).
% 1.64/0.60  fof(f96,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 1.64/0.60    inference(superposition,[],[f52,f32])).
% 1.64/0.60  fof(f505,plain,(
% 1.64/0.60    r1_tarski(k5_xboole_0(sK2,sK1),sK1) | k1_xboole_0 = sK1),
% 1.64/0.60    inference(superposition,[],[f420,f496])).
% 1.64/0.60  fof(f496,plain,(
% 1.64/0.60    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 1.64/0.60    inference(resolution,[],[f80,f406])).
% 1.64/0.60  fof(f406,plain,(
% 1.64/0.60    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.64/0.60    inference(superposition,[],[f76,f70])).
% 1.64/0.60  fof(f70,plain,(
% 1.64/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.64/0.60    inference(definition_unfolding,[],[f31,f69,f66])).
% 1.64/0.60  fof(f69,plain,(
% 1.64/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.64/0.60    inference(definition_unfolding,[],[f33,f65])).
% 1.64/0.60  fof(f33,plain,(
% 1.64/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f12])).
% 1.64/0.60  fof(f12,axiom,(
% 1.64/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.60  fof(f31,plain,(
% 1.64/0.60    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.64/0.60    inference(cnf_transformation,[],[f25])).
% 1.64/0.60  fof(f25,plain,(
% 1.64/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.64/0.60    inference(ennf_transformation,[],[f22])).
% 1.64/0.60  fof(f22,negated_conjecture,(
% 1.64/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.64/0.60    inference(negated_conjecture,[],[f21])).
% 1.64/0.60  fof(f21,conjecture,(
% 1.64/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.64/0.60  fof(f76,plain,(
% 1.64/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.64/0.60    inference(definition_unfolding,[],[f36,f66])).
% 1.64/0.60  fof(f36,plain,(
% 1.64/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f8])).
% 1.64/0.60  fof(f8,axiom,(
% 1.64/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.64/0.60  fof(f80,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.64/0.60    inference(definition_unfolding,[],[f48,f69,f69])).
% 1.64/0.60  fof(f48,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f19])).
% 1.64/0.60  fof(f19,axiom,(
% 1.64/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.64/0.60  fof(f154,plain,(
% 1.64/0.60    ( ! [X12,X10,X11,X9] : (~r1_tarski(k5_xboole_0(X10,X11),X12) | ~r2_hidden(X9,X11) | r2_hidden(X9,X12) | r2_hidden(X9,X10)) )),
% 1.64/0.60    inference(resolution,[],[f55,f45])).
% 1.64/0.60  fof(f45,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f26])).
% 1.64/0.60  fof(f55,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f27])).
% 1.64/0.60  fof(f27,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.64/0.60    inference(ennf_transformation,[],[f4])).
% 1.64/0.60  fof(f4,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.64/0.60  fof(f506,plain,(
% 1.64/0.60    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0 | k1_xboole_0 = sK1) )),
% 1.64/0.60    inference(superposition,[],[f80,f496])).
% 1.64/0.60  fof(f511,plain,(
% 1.64/0.60    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.64/0.60    inference(trivial_inequality_removal,[],[f502])).
% 1.64/0.60  fof(f502,plain,(
% 1.64/0.60    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.64/0.60    inference(superposition,[],[f73,f496])).
% 1.64/0.60  fof(f73,plain,(
% 1.64/0.60    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.64/0.60    inference(definition_unfolding,[],[f28,f69])).
% 1.87/0.60  fof(f28,plain,(
% 1.87/0.60    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.87/0.60    inference(cnf_transformation,[],[f25])).
% 1.87/0.60  fof(f512,plain,(
% 1.87/0.60    sK1 != sK2 | k1_xboole_0 = sK1),
% 1.87/0.60    inference(trivial_inequality_removal,[],[f500])).
% 1.87/0.60  fof(f500,plain,(
% 1.87/0.60    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 1.87/0.60    inference(superposition,[],[f71,f496])).
% 1.87/0.60  fof(f71,plain,(
% 1.87/0.60    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.87/0.60    inference(definition_unfolding,[],[f30,f69,f69])).
% 1.87/0.60  fof(f30,plain,(
% 1.87/0.60    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.87/0.60    inference(cnf_transformation,[],[f25])).
% 1.87/0.60  fof(f420,plain,(
% 1.87/0.60    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 1.87/0.60    inference(superposition,[],[f99,f70])).
% 1.87/0.60  fof(f99,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.87/0.60    inference(backward_demodulation,[],[f87,f98])).
% 1.87/0.60  fof(f87,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0)) )),
% 1.87/0.60    inference(backward_demodulation,[],[f77,f52])).
% 1.87/0.60  fof(f77,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 1.87/0.60    inference(definition_unfolding,[],[f37,f68])).
% 1.87/0.60  fof(f68,plain,(
% 1.87/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.87/0.60    inference(definition_unfolding,[],[f40,f67])).
% 1.87/0.60  fof(f40,plain,(
% 1.87/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.87/0.60    inference(cnf_transformation,[],[f6])).
% 1.87/0.60  fof(f6,axiom,(
% 1.87/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.87/0.60  fof(f37,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f7])).
% 1.87/0.60  fof(f7,axiom,(
% 1.87/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.87/0.60  fof(f129,plain,(
% 1.87/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.87/0.60    inference(duplicate_literal_removal,[],[f125])).
% 1.87/0.60  fof(f125,plain,(
% 1.87/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.87/0.60    inference(resolution,[],[f124,f47])).
% 1.87/0.60  fof(f124,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r2_hidden(sK3(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,X0)) )),
% 1.87/0.60    inference(resolution,[],[f118,f46])).
% 1.87/0.60  fof(f118,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 1.87/0.60    inference(duplicate_literal_removal,[],[f114])).
% 1.87/0.60  fof(f114,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0) | r2_hidden(X1,X0)) )),
% 1.87/0.60    inference(superposition,[],[f53,f32])).
% 1.87/0.60  fof(f53,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f27])).
% 1.87/0.60  fof(f654,plain,(
% 1.87/0.60    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.87/0.60    inference(global_subsumption,[],[f72,f642])).
% 1.87/0.60  fof(f72,plain,(
% 1.87/0.60    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.87/0.60    inference(definition_unfolding,[],[f29,f69])).
% 1.87/0.60  fof(f29,plain,(
% 1.87/0.60    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.87/0.60    inference(cnf_transformation,[],[f25])).
% 1.87/0.60  % SZS output end Proof for theBenchmark
% 1.87/0.60  % (6008)------------------------------
% 1.87/0.60  % (6008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (6008)Termination reason: Refutation
% 1.87/0.60  
% 1.87/0.60  % (6008)Memory used [KB]: 6908
% 1.87/0.60  % (6008)Time elapsed: 0.152 s
% 1.87/0.60  % (6008)------------------------------
% 1.87/0.60  % (6008)------------------------------
% 1.87/0.60  % (5983)Success in time 0.234 s
%------------------------------------------------------------------------------
