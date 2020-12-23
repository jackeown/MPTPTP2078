%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:23 EST 2020

% Result     : Theorem 4.84s
% Output     : Refutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 805 expanded)
%              Number of leaves         :   17 ( 225 expanded)
%              Depth                    :   27
%              Number of atoms          :  185 (1502 expanded)
%              Number of equality atoms :   62 ( 366 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12189,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12186,f536])).

fof(f536,plain,(
    sK1 != k4_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f474,f144])).

fof(f144,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),sK2) ),
    inference(resolution,[],[f140,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f140,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK1,X0),sK2) ),
    inference(resolution,[],[f93,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f93,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_xboole_0(X1,sK2) ) ),
    inference(superposition,[],[f56,f75])).

fof(f75,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f73,f50])).

fof(f73,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f30,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f474,plain,(
    sK1 != k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) ),
    inference(superposition,[],[f163,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f54,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f163,plain,(
    sK1 != k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f113,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f113,plain,(
    ~ r1_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f59,f45])).

fof(f59,plain,(
    ~ r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f31,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f12186,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f11724,f50])).

fof(f11724,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f8392,f2465])).

fof(f2465,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f2408,f50])).

fof(f2408,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f2353,f45])).

fof(f2353,plain,(
    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f2348,f673])).

fof(f673,plain,(
    sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f102,f73])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ) ),
    inference(resolution,[],[f70,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f29,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f2348,plain,(
    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(resolution,[],[f2151,f60])).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f28,f39,f58])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2151,plain,(
    ! [X12,X11] :
      ( ~ r1_tarski(X12,X11)
      | r1_xboole_0(X12,k4_xboole_0(sK1,X11)) ) ),
    inference(superposition,[],[f56,f2051])).

fof(f2051,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = X0 ),
    inference(resolution,[],[f2049,f50])).

fof(f2049,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f2028,f144])).

fof(f2028,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK2)) ),
    inference(superposition,[],[f1941,f144])).

fof(f1941,plain,(
    ! [X2,X3] : r1_xboole_0(X3,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK2),sK2)) ),
    inference(resolution,[],[f1863,f45])).

fof(f1863,plain,(
    ! [X6,X5] : r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),sK2),sK2),X6) ),
    inference(resolution,[],[f1774,f56])).

fof(f1774,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),X0) ),
    inference(superposition,[],[f34,f185])).

fof(f185,plain,(
    ! [X2] : k4_xboole_0(k4_xboole_0(X2,sK2),sK2) = k4_xboole_0(X2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f66,f87])).

fof(f87,plain,(
    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f83,f75])).

fof(f83,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f61,f72])).

fof(f72,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f30,f50])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f39,f39])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f8392,plain,(
    ! [X6] : r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X6,k4_xboole_0(X6,sK1))),X6) ),
    inference(superposition,[],[f4632,f61])).

fof(f4632,plain,(
    ! [X6,X7] : r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X6,X7))),X7) ),
    inference(resolution,[],[f4564,f56])).

fof(f4564,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X0) ),
    inference(superposition,[],[f3450,f144])).

fof(f3450,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),sK2),X2) ),
    inference(backward_demodulation,[],[f1900,f3412])).

fof(f3412,plain,(
    ! [X2] : k4_xboole_0(X2,sK2) = k4_xboole_0(k4_xboole_0(X2,sK2),sK2) ),
    inference(backward_demodulation,[],[f185,f3410])).

fof(f3410,plain,(
    ! [X49] : sK2 = k5_xboole_0(sK2,k4_xboole_0(X49,X49)) ),
    inference(backward_demodulation,[],[f2308,f3399])).

fof(f3399,plain,(
    ! [X1] : sK2 = k5_xboole_0(k4_xboole_0(X1,X1),sK2) ),
    inference(backward_demodulation,[],[f826,f3387])).

fof(f3387,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(sK1,sK1)) = X0 ),
    inference(resolution,[],[f3330,f50])).

fof(f3330,plain,(
    ! [X1] : r1_xboole_0(X1,k4_xboole_0(sK1,sK1)) ),
    inference(resolution,[],[f3315,f45])).

fof(f3315,plain,(
    ! [X7] : r1_xboole_0(k4_xboole_0(sK1,sK1),X7) ),
    inference(resolution,[],[f3293,f56])).

fof(f3293,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,sK1),X0) ),
    inference(resolution,[],[f3290,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3290,plain,(
    ! [X8] : r1_tarski(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,sK1)) ),
    inference(forward_demodulation,[],[f3289,f630])).

fof(f630,plain,(
    ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k5_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f627,f50])).

fof(f627,plain,(
    ! [X1] : r1_xboole_0(sK1,k4_xboole_0(X1,k5_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f612,f45])).

fof(f612,plain,(
    ! [X1] : r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(sK1,sK2)),sK1) ),
    inference(resolution,[],[f575,f56])).

fof(f575,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(X2,k5_xboole_0(sK1,sK2)),k4_xboole_0(X2,sK1)) ),
    inference(superposition,[],[f34,f86])).

fof(f86,plain,(
    ! [X2] : k4_xboole_0(k4_xboole_0(X2,sK1),sK2) = k4_xboole_0(X2,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f66,f72])).

fof(f3289,plain,(
    ! [X8] : r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X8,k5_xboole_0(sK1,sK2)))),k4_xboole_0(X8,sK1)) ),
    inference(forward_demodulation,[],[f3266,f591])).

fof(f591,plain,(
    ! [X0] : k4_xboole_0(X0,k5_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK1,sK2)),sK2) ),
    inference(resolution,[],[f576,f50])).

fof(f576,plain,(
    ! [X3] : r1_xboole_0(k4_xboole_0(X3,k5_xboole_0(sK1,sK2)),sK2) ),
    inference(superposition,[],[f35,f86])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f3266,plain,(
    ! [X8] : r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X8,k5_xboole_0(sK1,sK2)),sK2))),k4_xboole_0(X8,sK1)) ),
    inference(resolution,[],[f3215,f579])).

fof(f579,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,k4_xboole_0(X6,k5_xboole_0(sK1,sK2)))
      | r1_tarski(X7,k4_xboole_0(X6,sK1)) ) ),
    inference(superposition,[],[f55,f86])).

fof(f3215,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))),X0) ),
    inference(superposition,[],[f3066,f61])).

fof(f3066,plain,(
    ! [X10,X9] : r1_tarski(k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(X10,sK1)),X9) ),
    inference(superposition,[],[f34,f584])).

fof(f584,plain,(
    ! [X15,X16] : k4_xboole_0(k4_xboole_0(X16,sK2),k4_xboole_0(X15,sK1)) = k4_xboole_0(X16,k5_xboole_0(sK2,k4_xboole_0(X15,k5_xboole_0(sK1,sK2)))) ),
    inference(superposition,[],[f66,f86])).

fof(f826,plain,(
    ! [X1] : sK2 = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1))),sK2) ),
    inference(superposition,[],[f400,f61])).

fof(f400,plain,(
    ! [X3] : sK2 = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X3),sK2) ),
    inference(forward_demodulation,[],[f393,f312])).

fof(f312,plain,(
    ! [X4,X5] : sK2 = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X4),X5)) ),
    inference(superposition,[],[f153,f66])).

fof(f153,plain,(
    ! [X0] : sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f145,f50])).

fof(f145,plain,(
    ! [X1] : r1_xboole_0(sK2,k4_xboole_0(sK1,X1)) ),
    inference(resolution,[],[f140,f45])).

fof(f393,plain,(
    ! [X3] : sK2 = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X3),k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X3))) ),
    inference(resolution,[],[f381,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f381,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK1),X0),sK2) ),
    inference(resolution,[],[f182,f34])).

fof(f182,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_xboole_0(sK1,sK1))
      | r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f55,f87])).

fof(f2308,plain,(
    ! [X49] : k5_xboole_0(k4_xboole_0(X49,X49),sK2) = k5_xboole_0(sK2,k4_xboole_0(X49,X49)) ),
    inference(forward_demodulation,[],[f2301,f2244])).

fof(f2244,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),sK2) ),
    inference(resolution,[],[f2140,f50])).

fof(f2140,plain,(
    ! [X1] : r1_xboole_0(k4_xboole_0(X1,X1),sK2) ),
    inference(superposition,[],[f291,f2051])).

fof(f291,plain,(
    ! [X2,X3] : r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK1,X2))),sK2) ),
    inference(superposition,[],[f151,f61])).

fof(f151,plain,(
    ! [X4,X3] : r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X3),X4),sK2) ),
    inference(superposition,[],[f140,f66])).

fof(f2301,plain,(
    ! [X49] : k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X49,X49),sK2)) = k5_xboole_0(k4_xboole_0(X49,X49),sK2) ),
    inference(superposition,[],[f62,f2235])).

fof(f2235,plain,(
    ! [X1] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X1,X1)) ),
    inference(resolution,[],[f2139,f50])).

fof(f2139,plain,(
    ! [X0] : r1_xboole_0(sK2,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f351,f2051])).

fof(f351,plain,(
    ! [X2,X3] : r1_xboole_0(sK2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK1,X2)))) ),
    inference(superposition,[],[f160,f61])).

fof(f160,plain,(
    ! [X4,X3] : r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X3),X4)) ),
    inference(superposition,[],[f145,f66])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f37,f40,f40])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1900,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),sK2),sK2),X2) ),
    inference(superposition,[],[f1862,f61])).

fof(f1862,plain,(
    ! [X4,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),sK2),sK2),X3) ),
    inference(resolution,[],[f1774,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (24664)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (24645)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (24646)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (24657)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (24668)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (24656)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (24660)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (24651)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (24652)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (24649)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (24647)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (24648)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (24650)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (24667)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (24671)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (24655)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (24674)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24661)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (24674)Refutation not found, incomplete strategy% (24674)------------------------------
% 0.21/0.54  % (24674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24674)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24674)Memory used [KB]: 1663
% 0.21/0.54  % (24674)Time elapsed: 0.127 s
% 0.21/0.54  % (24674)------------------------------
% 0.21/0.54  % (24674)------------------------------
% 0.21/0.54  % (24672)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (24661)Refutation not found, incomplete strategy% (24661)------------------------------
% 0.21/0.54  % (24661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24661)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24661)Memory used [KB]: 10618
% 0.21/0.54  % (24661)Time elapsed: 0.131 s
% 0.21/0.54  % (24661)------------------------------
% 0.21/0.54  % (24661)------------------------------
% 0.21/0.54  % (24654)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (24658)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (24663)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (24673)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (24665)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (24666)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (24670)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (24673)Refutation not found, incomplete strategy% (24673)------------------------------
% 0.21/0.55  % (24673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24653)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (24659)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (24673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24673)Memory used [KB]: 10746
% 0.21/0.55  % (24673)Time elapsed: 0.139 s
% 0.21/0.55  % (24673)------------------------------
% 0.21/0.55  % (24673)------------------------------
% 0.21/0.55  % (24662)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (24655)Refutation not found, incomplete strategy% (24655)------------------------------
% 0.21/0.56  % (24655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24655)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24655)Memory used [KB]: 10746
% 0.21/0.56  % (24655)Time elapsed: 0.148 s
% 0.21/0.56  % (24655)------------------------------
% 0.21/0.56  % (24655)------------------------------
% 0.21/0.56  % (24669)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.15/0.68  % (24681)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.15/0.69  % (24680)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.15/0.70  % (24683)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.15/0.70  % (24682)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.14/0.81  % (24647)Time limit reached!
% 3.14/0.81  % (24647)------------------------------
% 3.14/0.81  % (24647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.81  % (24647)Termination reason: Time limit
% 3.14/0.81  
% 3.14/0.81  % (24647)Memory used [KB]: 6524
% 3.14/0.81  % (24647)Time elapsed: 0.407 s
% 3.14/0.81  % (24647)------------------------------
% 3.14/0.81  % (24647)------------------------------
% 3.14/0.82  % (24669)Time limit reached!
% 3.14/0.82  % (24669)------------------------------
% 3.14/0.82  % (24669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.82  % (24669)Termination reason: Time limit
% 3.14/0.82  % (24669)Termination phase: Saturation
% 3.14/0.82  
% 3.14/0.82  % (24669)Memory used [KB]: 13176
% 3.14/0.82  % (24669)Time elapsed: 0.400 s
% 3.14/0.82  % (24669)------------------------------
% 3.14/0.82  % (24669)------------------------------
% 3.91/0.91  % (24651)Time limit reached!
% 3.91/0.91  % (24651)------------------------------
% 3.91/0.91  % (24651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.91  % (24651)Termination reason: Time limit
% 3.91/0.91  
% 3.91/0.91  % (24651)Memory used [KB]: 14839
% 3.91/0.91  % (24651)Time elapsed: 0.506 s
% 3.91/0.91  % (24651)------------------------------
% 3.91/0.91  % (24651)------------------------------
% 4.27/0.93  % (24659)Time limit reached!
% 4.27/0.93  % (24659)------------------------------
% 4.27/0.93  % (24659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.93  % (24659)Termination reason: Time limit
% 4.27/0.93  % (24659)Termination phase: Saturation
% 4.27/0.93  
% 4.27/0.93  % (24659)Memory used [KB]: 4733
% 4.27/0.93  % (24659)Time elapsed: 0.500 s
% 4.27/0.93  % (24659)------------------------------
% 4.27/0.93  % (24659)------------------------------
% 4.27/0.93  % (24690)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.34/0.96  % (24691)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.84/1.04  % (24693)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.84/1.04  % (24692)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.84/1.05  % (24652)Time limit reached!
% 4.84/1.05  % (24652)------------------------------
% 4.84/1.05  % (24652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.05  % (24652)Termination reason: Time limit
% 4.84/1.05  
% 4.84/1.05  % (24652)Memory used [KB]: 6524
% 4.84/1.05  % (24652)Time elapsed: 0.610 s
% 4.84/1.05  % (24652)------------------------------
% 4.84/1.05  % (24652)------------------------------
% 4.84/1.06  % (24662)Refutation found. Thanks to Tanya!
% 4.84/1.06  % SZS status Theorem for theBenchmark
% 4.84/1.06  % SZS output start Proof for theBenchmark
% 4.84/1.06  fof(f12189,plain,(
% 4.84/1.06    $false),
% 4.84/1.06    inference(subsumption_resolution,[],[f12186,f536])).
% 4.84/1.06  fof(f536,plain,(
% 4.84/1.06    sK1 != k4_xboole_0(sK1,sK0)),
% 4.84/1.06    inference(superposition,[],[f474,f144])).
% 4.84/1.06  fof(f144,plain,(
% 4.84/1.06    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(k4_xboole_0(sK1,X0),sK2)) )),
% 4.84/1.06    inference(resolution,[],[f140,f50])).
% 4.84/1.06  fof(f50,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f13])).
% 4.84/1.06  fof(f13,axiom,(
% 4.84/1.06    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 4.84/1.06  fof(f140,plain,(
% 4.84/1.06    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK1,X0),sK2)) )),
% 4.84/1.06    inference(resolution,[],[f93,f34])).
% 4.84/1.06  fof(f34,plain,(
% 4.84/1.06    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f8])).
% 4.84/1.06  fof(f8,axiom,(
% 4.84/1.06    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.84/1.06  fof(f93,plain,(
% 4.84/1.06    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_xboole_0(X1,sK2)) )),
% 4.84/1.06    inference(superposition,[],[f56,f75])).
% 4.84/1.06  fof(f75,plain,(
% 4.84/1.06    sK1 = k4_xboole_0(sK1,sK2)),
% 4.84/1.06    inference(resolution,[],[f73,f50])).
% 4.84/1.06  fof(f73,plain,(
% 4.84/1.06    r1_xboole_0(sK1,sK2)),
% 4.84/1.06    inference(resolution,[],[f30,f45])).
% 4.84/1.06  fof(f45,plain,(
% 4.84/1.06    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f26])).
% 4.84/1.06  fof(f26,plain,(
% 4.84/1.06    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 4.84/1.06    inference(ennf_transformation,[],[f3])).
% 4.84/1.06  fof(f3,axiom,(
% 4.84/1.06    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 4.84/1.06  fof(f30,plain,(
% 4.84/1.06    r1_xboole_0(sK2,sK1)),
% 4.84/1.06    inference(cnf_transformation,[],[f23])).
% 4.84/1.06  fof(f23,plain,(
% 4.84/1.06    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 4.84/1.06    inference(flattening,[],[f22])).
% 4.84/1.06  fof(f22,plain,(
% 4.84/1.06    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 4.84/1.06    inference(ennf_transformation,[],[f20])).
% 4.84/1.06  fof(f20,negated_conjecture,(
% 4.84/1.06    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 4.84/1.06    inference(negated_conjecture,[],[f19])).
% 4.84/1.06  fof(f19,conjecture,(
% 4.84/1.06    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 4.84/1.06  fof(f56,plain,(
% 4.84/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f27])).
% 4.84/1.06  fof(f27,plain,(
% 4.84/1.06    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 4.84/1.06    inference(ennf_transformation,[],[f6])).
% 4.84/1.06  fof(f6,axiom,(
% 4.84/1.06    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 4.84/1.06  fof(f474,plain,(
% 4.84/1.06    sK1 != k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)),
% 4.84/1.06    inference(superposition,[],[f163,f66])).
% 4.84/1.06  fof(f66,plain,(
% 4.84/1.06    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 4.84/1.06    inference(definition_unfolding,[],[f54,f40])).
% 4.84/1.06  fof(f40,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.84/1.06    inference(cnf_transformation,[],[f14])).
% 4.84/1.06  fof(f14,axiom,(
% 4.84/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.84/1.06  fof(f54,plain,(
% 4.84/1.06    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.84/1.06    inference(cnf_transformation,[],[f9])).
% 4.84/1.06  fof(f9,axiom,(
% 4.84/1.06    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.84/1.06  fof(f163,plain,(
% 4.84/1.06    sK1 != k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)))),
% 4.84/1.06    inference(resolution,[],[f113,f49])).
% 4.84/1.06  fof(f49,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f13])).
% 4.84/1.06  fof(f113,plain,(
% 4.84/1.06    ~r1_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)))),
% 4.84/1.06    inference(resolution,[],[f59,f45])).
% 4.84/1.06  fof(f59,plain,(
% 4.84/1.06    ~r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1)),
% 4.84/1.06    inference(definition_unfolding,[],[f31,f40])).
% 4.84/1.06  fof(f31,plain,(
% 4.84/1.06    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 4.84/1.06    inference(cnf_transformation,[],[f23])).
% 4.84/1.06  fof(f12186,plain,(
% 4.84/1.06    sK1 = k4_xboole_0(sK1,sK0)),
% 4.84/1.06    inference(resolution,[],[f11724,f50])).
% 4.84/1.06  fof(f11724,plain,(
% 4.84/1.06    r1_xboole_0(sK1,sK0)),
% 4.84/1.06    inference(superposition,[],[f8392,f2465])).
% 4.84/1.06  fof(f2465,plain,(
% 4.84/1.06    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 4.84/1.06    inference(resolution,[],[f2408,f50])).
% 4.84/1.06  fof(f2408,plain,(
% 4.84/1.06    r1_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 4.84/1.06    inference(resolution,[],[f2353,f45])).
% 4.84/1.06  fof(f2353,plain,(
% 4.84/1.06    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),
% 4.84/1.06    inference(forward_demodulation,[],[f2348,f673])).
% 4.84/1.06  fof(f673,plain,(
% 4.84/1.06    sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))),
% 4.84/1.06    inference(resolution,[],[f102,f73])).
% 4.84/1.06  fof(f102,plain,(
% 4.84/1.06    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = X0) )),
% 4.84/1.06    inference(resolution,[],[f70,f65])).
% 4.84/1.06  fof(f65,plain,(
% 4.84/1.06    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 4.84/1.06    inference(definition_unfolding,[],[f51,f58])).
% 4.84/1.06  fof(f58,plain,(
% 4.84/1.06    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.84/1.06    inference(definition_unfolding,[],[f33,f57])).
% 4.84/1.06  fof(f57,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.84/1.06    inference(definition_unfolding,[],[f38,f53])).
% 4.84/1.06  fof(f53,plain,(
% 4.84/1.06    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f17])).
% 4.84/1.06  fof(f17,axiom,(
% 4.84/1.06    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.84/1.06  fof(f38,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f16])).
% 4.84/1.06  fof(f16,axiom,(
% 4.84/1.06    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.84/1.06  fof(f33,plain,(
% 4.84/1.06    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f15])).
% 4.84/1.06  fof(f15,axiom,(
% 4.84/1.06    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.84/1.06  fof(f51,plain,(
% 4.84/1.06    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 4.84/1.06    inference(cnf_transformation,[],[f18])).
% 4.84/1.06  fof(f18,axiom,(
% 4.84/1.06    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 4.84/1.06  fof(f70,plain,(
% 4.84/1.06    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 4.84/1.06    inference(resolution,[],[f29,f41])).
% 4.84/1.06  fof(f41,plain,(
% 4.84/1.06    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f24])).
% 4.84/1.06  fof(f24,plain,(
% 4.84/1.06    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.84/1.06    inference(ennf_transformation,[],[f21])).
% 4.84/1.06  fof(f21,plain,(
% 4.84/1.06    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.84/1.06    inference(rectify,[],[f4])).
% 4.84/1.06  fof(f4,axiom,(
% 4.84/1.06    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.84/1.06  fof(f29,plain,(
% 4.84/1.06    r2_hidden(sK3,sK2)),
% 4.84/1.06    inference(cnf_transformation,[],[f23])).
% 4.84/1.06  fof(f2348,plain,(
% 4.84/1.06    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 4.84/1.06    inference(resolution,[],[f2151,f60])).
% 4.84/1.06  fof(f60,plain,(
% 4.84/1.06    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 4.84/1.06    inference(definition_unfolding,[],[f28,f39,f58])).
% 4.84/1.06  fof(f39,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.84/1.06    inference(cnf_transformation,[],[f10])).
% 4.84/1.06  fof(f10,axiom,(
% 4.84/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.84/1.06  fof(f28,plain,(
% 4.84/1.06    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 4.84/1.06    inference(cnf_transformation,[],[f23])).
% 4.84/1.06  fof(f2151,plain,(
% 4.84/1.06    ( ! [X12,X11] : (~r1_tarski(X12,X11) | r1_xboole_0(X12,k4_xboole_0(sK1,X11))) )),
% 4.84/1.06    inference(superposition,[],[f56,f2051])).
% 4.84/1.06  fof(f2051,plain,(
% 4.84/1.06    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(sK1,X0)) = X0) )),
% 4.84/1.06    inference(resolution,[],[f2049,f50])).
% 4.84/1.06  fof(f2049,plain,(
% 4.84/1.06    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK1,X0))) )),
% 4.84/1.06    inference(forward_demodulation,[],[f2028,f144])).
% 4.84/1.06  fof(f2028,plain,(
% 4.84/1.06    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK2))) )),
% 4.84/1.06    inference(superposition,[],[f1941,f144])).
% 4.84/1.06  fof(f1941,plain,(
% 4.84/1.06    ( ! [X2,X3] : (r1_xboole_0(X3,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK2),sK2))) )),
% 4.84/1.06    inference(resolution,[],[f1863,f45])).
% 4.84/1.06  fof(f1863,plain,(
% 4.84/1.06    ( ! [X6,X5] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),sK2),sK2),X6)) )),
% 4.84/1.06    inference(resolution,[],[f1774,f56])).
% 4.84/1.06  fof(f1774,plain,(
% 4.84/1.06    ( ! [X0] : (r1_tarski(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),X0)) )),
% 4.84/1.06    inference(superposition,[],[f34,f185])).
% 4.84/1.06  fof(f185,plain,(
% 4.84/1.06    ( ! [X2] : (k4_xboole_0(k4_xboole_0(X2,sK2),sK2) = k4_xboole_0(X2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK1)))) )),
% 4.84/1.06    inference(superposition,[],[f66,f87])).
% 4.84/1.06  fof(f87,plain,(
% 4.84/1.06    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK1,sK1)),
% 4.84/1.06    inference(forward_demodulation,[],[f83,f75])).
% 4.84/1.06  fof(f83,plain,(
% 4.84/1.06    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,sK2)),
% 4.84/1.06    inference(superposition,[],[f61,f72])).
% 4.84/1.06  fof(f72,plain,(
% 4.84/1.06    sK2 = k4_xboole_0(sK2,sK1)),
% 4.84/1.06    inference(resolution,[],[f30,f50])).
% 4.84/1.06  fof(f61,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.84/1.06    inference(definition_unfolding,[],[f36,f39,f39])).
% 4.84/1.06  fof(f36,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f2])).
% 4.84/1.06  fof(f2,axiom,(
% 4.84/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.84/1.06  fof(f8392,plain,(
% 4.84/1.06    ( ! [X6] : (r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X6,k4_xboole_0(X6,sK1))),X6)) )),
% 4.84/1.06    inference(superposition,[],[f4632,f61])).
% 4.84/1.06  fof(f4632,plain,(
% 4.84/1.06    ( ! [X6,X7] : (r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X6,X7))),X7)) )),
% 4.84/1.06    inference(resolution,[],[f4564,f56])).
% 4.84/1.06  fof(f4564,plain,(
% 4.84/1.06    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X0)) )),
% 4.84/1.06    inference(superposition,[],[f3450,f144])).
% 4.84/1.06  fof(f3450,plain,(
% 4.84/1.06    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),sK2),X2)) )),
% 4.84/1.06    inference(backward_demodulation,[],[f1900,f3412])).
% 4.84/1.06  fof(f3412,plain,(
% 4.84/1.06    ( ! [X2] : (k4_xboole_0(X2,sK2) = k4_xboole_0(k4_xboole_0(X2,sK2),sK2)) )),
% 4.84/1.06    inference(backward_demodulation,[],[f185,f3410])).
% 4.84/1.06  fof(f3410,plain,(
% 4.84/1.06    ( ! [X49] : (sK2 = k5_xboole_0(sK2,k4_xboole_0(X49,X49))) )),
% 4.84/1.06    inference(backward_demodulation,[],[f2308,f3399])).
% 4.84/1.06  fof(f3399,plain,(
% 4.84/1.06    ( ! [X1] : (sK2 = k5_xboole_0(k4_xboole_0(X1,X1),sK2)) )),
% 4.84/1.06    inference(backward_demodulation,[],[f826,f3387])).
% 4.84/1.06  fof(f3387,plain,(
% 4.84/1.06    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(sK1,sK1)) = X0) )),
% 4.84/1.06    inference(resolution,[],[f3330,f50])).
% 4.84/1.06  fof(f3330,plain,(
% 4.84/1.06    ( ! [X1] : (r1_xboole_0(X1,k4_xboole_0(sK1,sK1))) )),
% 4.84/1.06    inference(resolution,[],[f3315,f45])).
% 4.84/1.06  fof(f3315,plain,(
% 4.84/1.06    ( ! [X7] : (r1_xboole_0(k4_xboole_0(sK1,sK1),X7)) )),
% 4.84/1.06    inference(resolution,[],[f3293,f56])).
% 4.84/1.06  fof(f3293,plain,(
% 4.84/1.06    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK1),X0)) )),
% 4.84/1.06    inference(resolution,[],[f3290,f55])).
% 4.84/1.06  fof(f55,plain,(
% 4.84/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f27])).
% 4.84/1.06  fof(f3290,plain,(
% 4.84/1.06    ( ! [X8] : (r1_tarski(k4_xboole_0(sK1,sK1),k4_xboole_0(X8,sK1))) )),
% 4.84/1.06    inference(forward_demodulation,[],[f3289,f630])).
% 4.84/1.06  fof(f630,plain,(
% 4.84/1.06    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k5_xboole_0(sK1,sK2)))) )),
% 4.84/1.06    inference(resolution,[],[f627,f50])).
% 4.84/1.06  fof(f627,plain,(
% 4.84/1.06    ( ! [X1] : (r1_xboole_0(sK1,k4_xboole_0(X1,k5_xboole_0(sK1,sK2)))) )),
% 4.84/1.06    inference(resolution,[],[f612,f45])).
% 4.84/1.06  fof(f612,plain,(
% 4.84/1.06    ( ! [X1] : (r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(sK1,sK2)),sK1)) )),
% 4.84/1.06    inference(resolution,[],[f575,f56])).
% 4.84/1.06  fof(f575,plain,(
% 4.84/1.06    ( ! [X2] : (r1_tarski(k4_xboole_0(X2,k5_xboole_0(sK1,sK2)),k4_xboole_0(X2,sK1))) )),
% 4.84/1.06    inference(superposition,[],[f34,f86])).
% 4.84/1.06  fof(f86,plain,(
% 4.84/1.06    ( ! [X2] : (k4_xboole_0(k4_xboole_0(X2,sK1),sK2) = k4_xboole_0(X2,k5_xboole_0(sK1,sK2))) )),
% 4.84/1.06    inference(superposition,[],[f66,f72])).
% 4.84/1.06  fof(f3289,plain,(
% 4.84/1.06    ( ! [X8] : (r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X8,k5_xboole_0(sK1,sK2)))),k4_xboole_0(X8,sK1))) )),
% 4.84/1.06    inference(forward_demodulation,[],[f3266,f591])).
% 4.84/1.06  fof(f591,plain,(
% 4.84/1.06    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK1,sK2)),sK2)) )),
% 4.84/1.06    inference(resolution,[],[f576,f50])).
% 4.84/1.06  fof(f576,plain,(
% 4.84/1.06    ( ! [X3] : (r1_xboole_0(k4_xboole_0(X3,k5_xboole_0(sK1,sK2)),sK2)) )),
% 4.84/1.06    inference(superposition,[],[f35,f86])).
% 4.84/1.06  fof(f35,plain,(
% 4.84/1.06    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f12])).
% 4.84/1.06  fof(f12,axiom,(
% 4.84/1.06    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 4.84/1.06  fof(f3266,plain,(
% 4.84/1.06    ( ! [X8] : (r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X8,k5_xboole_0(sK1,sK2)),sK2))),k4_xboole_0(X8,sK1))) )),
% 4.84/1.06    inference(resolution,[],[f3215,f579])).
% 4.84/1.06  fof(f579,plain,(
% 4.84/1.06    ( ! [X6,X7] : (~r1_tarski(X7,k4_xboole_0(X6,k5_xboole_0(sK1,sK2))) | r1_tarski(X7,k4_xboole_0(X6,sK1))) )),
% 4.84/1.06    inference(superposition,[],[f55,f86])).
% 4.84/1.06  fof(f3215,plain,(
% 4.84/1.06    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))),X0)) )),
% 4.84/1.06    inference(superposition,[],[f3066,f61])).
% 4.84/1.06  fof(f3066,plain,(
% 4.84/1.06    ( ! [X10,X9] : (r1_tarski(k4_xboole_0(k4_xboole_0(X9,sK2),k4_xboole_0(X10,sK1)),X9)) )),
% 4.84/1.06    inference(superposition,[],[f34,f584])).
% 4.84/1.06  fof(f584,plain,(
% 4.84/1.06    ( ! [X15,X16] : (k4_xboole_0(k4_xboole_0(X16,sK2),k4_xboole_0(X15,sK1)) = k4_xboole_0(X16,k5_xboole_0(sK2,k4_xboole_0(X15,k5_xboole_0(sK1,sK2))))) )),
% 4.84/1.06    inference(superposition,[],[f66,f86])).
% 4.84/1.06  fof(f826,plain,(
% 4.84/1.06    ( ! [X1] : (sK2 = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1))),sK2)) )),
% 4.84/1.06    inference(superposition,[],[f400,f61])).
% 4.84/1.06  fof(f400,plain,(
% 4.84/1.06    ( ! [X3] : (sK2 = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X3),sK2)) )),
% 4.84/1.06    inference(forward_demodulation,[],[f393,f312])).
% 4.84/1.06  fof(f312,plain,(
% 4.84/1.06    ( ! [X4,X5] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X4),X5))) )),
% 4.84/1.06    inference(superposition,[],[f153,f66])).
% 4.84/1.06  fof(f153,plain,(
% 4.84/1.06    ( ! [X0] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,X0))) )),
% 4.84/1.06    inference(resolution,[],[f145,f50])).
% 4.84/1.06  fof(f145,plain,(
% 4.84/1.06    ( ! [X1] : (r1_xboole_0(sK2,k4_xboole_0(sK1,X1))) )),
% 4.84/1.06    inference(resolution,[],[f140,f45])).
% 4.84/1.06  fof(f393,plain,(
% 4.84/1.06    ( ! [X3] : (sK2 = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK1),X3),k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK1),X3)))) )),
% 4.84/1.06    inference(resolution,[],[f381,f63])).
% 4.84/1.06  fof(f63,plain,(
% 4.84/1.06    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 4.84/1.06    inference(definition_unfolding,[],[f44,f40])).
% 4.84/1.06  fof(f44,plain,(
% 4.84/1.06    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.84/1.06    inference(cnf_transformation,[],[f25])).
% 4.84/1.06  fof(f25,plain,(
% 4.84/1.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.84/1.06    inference(ennf_transformation,[],[f7])).
% 4.84/1.06  fof(f7,axiom,(
% 4.84/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.84/1.06  fof(f381,plain,(
% 4.84/1.06    ( ! [X0] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK1),X0),sK2)) )),
% 4.84/1.06    inference(resolution,[],[f182,f34])).
% 4.84/1.06  fof(f182,plain,(
% 4.84/1.06    ( ! [X0] : (~r1_tarski(X0,k4_xboole_0(sK1,sK1)) | r1_tarski(X0,sK2)) )),
% 4.84/1.06    inference(superposition,[],[f55,f87])).
% 4.84/1.06  fof(f2308,plain,(
% 4.84/1.06    ( ! [X49] : (k5_xboole_0(k4_xboole_0(X49,X49),sK2) = k5_xboole_0(sK2,k4_xboole_0(X49,X49))) )),
% 4.84/1.06    inference(forward_demodulation,[],[f2301,f2244])).
% 4.84/1.06  fof(f2244,plain,(
% 4.84/1.06    ( ! [X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),sK2)) )),
% 4.84/1.06    inference(resolution,[],[f2140,f50])).
% 4.84/1.06  fof(f2140,plain,(
% 4.84/1.06    ( ! [X1] : (r1_xboole_0(k4_xboole_0(X1,X1),sK2)) )),
% 4.84/1.06    inference(superposition,[],[f291,f2051])).
% 4.84/1.06  fof(f291,plain,(
% 4.84/1.06    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK1,X2))),sK2)) )),
% 4.84/1.06    inference(superposition,[],[f151,f61])).
% 4.84/1.06  fof(f151,plain,(
% 4.84/1.06    ( ! [X4,X3] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X3),X4),sK2)) )),
% 4.84/1.06    inference(superposition,[],[f140,f66])).
% 4.84/1.06  fof(f2301,plain,(
% 4.84/1.06    ( ! [X49] : (k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X49,X49),sK2)) = k5_xboole_0(k4_xboole_0(X49,X49),sK2)) )),
% 4.84/1.06    inference(superposition,[],[f62,f2235])).
% 4.84/1.06  fof(f2235,plain,(
% 4.84/1.06    ( ! [X1] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X1,X1))) )),
% 4.84/1.06    inference(resolution,[],[f2139,f50])).
% 4.84/1.06  fof(f2139,plain,(
% 4.84/1.06    ( ! [X0] : (r1_xboole_0(sK2,k4_xboole_0(X0,X0))) )),
% 4.84/1.06    inference(superposition,[],[f351,f2051])).
% 4.84/1.06  fof(f351,plain,(
% 4.84/1.06    ( ! [X2,X3] : (r1_xboole_0(sK2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK1,X2))))) )),
% 4.84/1.06    inference(superposition,[],[f160,f61])).
% 4.84/1.06  fof(f160,plain,(
% 4.84/1.06    ( ! [X4,X3] : (r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X3),X4))) )),
% 4.84/1.06    inference(superposition,[],[f145,f66])).
% 4.84/1.06  fof(f62,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 4.84/1.06    inference(definition_unfolding,[],[f37,f40,f40])).
% 4.84/1.06  fof(f37,plain,(
% 4.84/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.84/1.06    inference(cnf_transformation,[],[f1])).
% 4.84/1.06  fof(f1,axiom,(
% 4.84/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.84/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.84/1.06  fof(f1900,plain,(
% 4.84/1.06    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),sK2),sK2),X2)) )),
% 4.84/1.06    inference(superposition,[],[f1862,f61])).
% 4.84/1.06  fof(f1862,plain,(
% 4.84/1.06    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),sK2),sK2),X3)) )),
% 4.84/1.06    inference(resolution,[],[f1774,f55])).
% 4.84/1.06  % SZS output end Proof for theBenchmark
% 4.84/1.06  % (24662)------------------------------
% 4.84/1.06  % (24662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.06  % (24662)Termination reason: Refutation
% 4.84/1.06  
% 4.84/1.06  % (24662)Memory used [KB]: 6012
% 4.84/1.06  % (24662)Time elapsed: 0.639 s
% 4.84/1.06  % (24662)------------------------------
% 4.84/1.06  % (24662)------------------------------
% 4.84/1.06  % (24644)Success in time 0.7 s
%------------------------------------------------------------------------------
