%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:26 EST 2020

% Result     : Theorem 7.80s
% Output     : Refutation 8.49s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 301 expanded)
%              Number of leaves         :   22 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  134 ( 374 expanded)
%              Number of equality atoms :   87 ( 313 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6244,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1600,f94,f1520])).

fof(f1520,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ sP5(X8,X7,X6,X5,X4,X3,X2,X1,X0,X0)
      | r2_hidden(X8,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ) ),
    inference(superposition,[],[f93,f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f54,f75,f72,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f74])).

% (7942)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))))
      | ~ sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X10,X9)
      | k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) != X9 ) ),
    inference(definition_unfolding,[],[f66,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f55,f75,f71,f72])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X10,X7,X5,X3,X1] : sP5(X10,X10,X7,X6,X5,X4,X3,X2,X1,X0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( X8 != X10
      | sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1600,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f1582,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1582,plain,(
    ~ sP3(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f29,f1579])).

fof(f1579,plain,(
    ! [X2] :
      ( ~ sP3(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
      | r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f91,f916])).

fof(f916,plain,(
    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f913,f132])).

fof(f132,plain,(
    ! [X0,X1] : k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f80,f104])).

fof(f104,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(X4,X3) = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f39,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f75])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f913,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(backward_demodulation,[],[f566,f876])).

fof(f876,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,X0))) ),
    inference(superposition,[],[f594,f34])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f594,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f81,f577])).

fof(f577,plain,(
    ! [X6,X5] : k3_xboole_0(X6,k5_xboole_0(X6,X5)) = k5_xboole_0(X6,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f557,f33])).

fof(f557,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f532,f33])).

fof(f532,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f42,f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f75,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f566,plain,(
    k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    inference(forward_demodulation,[],[f560,f34])).

fof(f560,plain,(
    k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),sK1) ),
    inference(backward_demodulation,[],[f265,f557])).

fof(f265,plain,(
    k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    inference(unit_resulting_resolution,[],[f131,f39])).

fof(f131,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    inference(forward_demodulation,[],[f130,f34])).

fof(f130,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(backward_demodulation,[],[f103,f124])).

fof(f124,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f41,f34])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f103,plain,(
    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    inference(backward_demodulation,[],[f79,f81])).

fof(f79,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f28,f75,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f74])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:20:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.46  % (7732)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.47  % (7748)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.51  % (7725)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.52  % (7741)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.53  % (7729)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.54  % (7723)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.54  % (7727)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.54  % (7721)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.54  % (7746)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.18/0.55  % (7720)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.55  % (7728)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.55  % (7724)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.55  % (7749)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.56  % (7738)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.56  % (7736)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.56  % (7722)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.57  % (7745)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.57  % (7730)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.57  % (7740)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.58  % (7733)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.58  % (7742)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.58  % (7737)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.58  % (7737)Refutation not found, incomplete strategy% (7737)------------------------------
% 0.18/0.58  % (7737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.58  % (7737)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.58  
% 0.18/0.58  % (7737)Memory used [KB]: 10618
% 0.18/0.58  % (7737)Time elapsed: 0.187 s
% 0.18/0.58  % (7737)------------------------------
% 0.18/0.58  % (7737)------------------------------
% 0.18/0.58  % (7744)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.18/0.59  % (7735)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.59  % (7734)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.60  % (7731)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.61  % (7739)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.61  % (7726)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.62  % (7747)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.62  % (7742)Refutation not found, incomplete strategy% (7742)------------------------------
% 0.18/0.62  % (7742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.62  % (7742)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.62  
% 0.18/0.62  % (7742)Memory used [KB]: 10874
% 0.18/0.62  % (7742)Time elapsed: 0.162 s
% 0.18/0.62  % (7742)------------------------------
% 0.18/0.62  % (7742)------------------------------
% 0.18/0.62  % (7743)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 3.08/0.78  % (7774)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.08/0.81  % (7777)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.66/0.84  % (7725)Time limit reached!
% 3.66/0.84  % (7725)------------------------------
% 3.66/0.84  % (7725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.85  % (7725)Termination reason: Time limit
% 3.66/0.85  % (7725)Termination phase: Saturation
% 3.66/0.85  
% 3.66/0.85  % (7725)Memory used [KB]: 9338
% 3.66/0.85  % (7725)Time elapsed: 0.419 s
% 3.66/0.85  % (7725)------------------------------
% 3.66/0.85  % (7725)------------------------------
% 4.01/0.90  % (7720)Time limit reached!
% 4.01/0.90  % (7720)------------------------------
% 4.01/0.90  % (7720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.90  % (7720)Termination reason: Time limit
% 4.01/0.90  
% 4.01/0.90  % (7720)Memory used [KB]: 3326
% 4.01/0.90  % (7720)Time elapsed: 0.504 s
% 4.01/0.90  % (7720)------------------------------
% 4.01/0.90  % (7720)------------------------------
% 4.01/0.91  % (7732)Time limit reached!
% 4.01/0.91  % (7732)------------------------------
% 4.01/0.91  % (7732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.91  % (7732)Termination reason: Time limit
% 4.01/0.91  % (7732)Termination phase: Saturation
% 4.01/0.91  
% 4.01/0.91  % (7732)Memory used [KB]: 10618
% 4.01/0.91  % (7732)Time elapsed: 0.500 s
% 4.01/0.91  % (7732)------------------------------
% 4.01/0.91  % (7732)------------------------------
% 4.01/0.92  % (7730)Time limit reached!
% 4.01/0.92  % (7730)------------------------------
% 4.01/0.92  % (7730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (7730)Termination reason: Time limit
% 4.01/0.92  % (7730)Termination phase: Saturation
% 4.01/0.92  
% 4.01/0.92  % (7730)Memory used [KB]: 14456
% 4.01/0.92  % (7730)Time elapsed: 0.500 s
% 4.01/0.92  % (7730)------------------------------
% 4.01/0.92  % (7730)------------------------------
% 4.01/0.94  % (7721)Time limit reached!
% 4.01/0.94  % (7721)------------------------------
% 4.01/0.94  % (7721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.94  % (7721)Termination reason: Time limit
% 4.01/0.94  % (7721)Termination phase: Saturation
% 4.01/0.94  
% 4.01/0.94  % (7721)Memory used [KB]: 7547
% 4.01/0.94  % (7721)Time elapsed: 0.500 s
% 4.01/0.94  % (7721)------------------------------
% 4.01/0.94  % (7721)------------------------------
% 4.62/1.00  % (7727)Time limit reached!
% 4.62/1.00  % (7727)------------------------------
% 4.62/1.00  % (7727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/1.01  % (7780)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.97/1.02  % (7748)Time limit reached!
% 4.97/1.02  % (7748)------------------------------
% 4.97/1.02  % (7748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.02  % (7748)Termination reason: Time limit
% 4.97/1.02  
% 4.97/1.02  % (7748)Memory used [KB]: 10490
% 4.97/1.02  % (7748)Time elapsed: 0.619 s
% 4.97/1.02  % (7748)------------------------------
% 4.97/1.02  % (7748)------------------------------
% 4.97/1.02  % (7727)Termination reason: Time limit
% 4.97/1.02  
% 4.97/1.02  % (7727)Memory used [KB]: 9338
% 4.97/1.02  % (7727)Time elapsed: 0.615 s
% 4.97/1.02  % (7727)------------------------------
% 4.97/1.02  % (7727)------------------------------
% 4.97/1.03  % (7782)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.97/1.03  % (7784)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.97/1.04  % (7781)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.97/1.05  % (7736)Time limit reached!
% 4.97/1.05  % (7736)------------------------------
% 4.97/1.05  % (7736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.05  % (7736)Termination reason: Time limit
% 4.97/1.05  
% 4.97/1.05  % (7736)Memory used [KB]: 15735
% 4.97/1.05  % (7736)Time elapsed: 0.634 s
% 4.97/1.05  % (7736)------------------------------
% 4.97/1.05  % (7736)------------------------------
% 4.97/1.05  % (7783)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.16/1.15  % (7807)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.16/1.16  % (7811)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.57/1.19  % (7826)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.10/1.26  % (7741)Time limit reached!
% 7.10/1.26  % (7741)------------------------------
% 7.10/1.26  % (7741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.18/1.26  % (7741)Termination reason: Time limit
% 7.18/1.26  
% 7.18/1.26  % (7741)Memory used [KB]: 7419
% 7.18/1.26  % (7741)Time elapsed: 0.840 s
% 7.18/1.26  % (7741)------------------------------
% 7.18/1.26  % (7741)------------------------------
% 7.53/1.34  % (7782)Time limit reached!
% 7.53/1.34  % (7782)------------------------------
% 7.53/1.34  % (7782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.34  % (7781)Time limit reached!
% 7.80/1.34  % (7781)------------------------------
% 7.80/1.34  % (7781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.34  % (7782)Termination reason: Time limit
% 7.80/1.34  
% 7.80/1.34  % (7782)Memory used [KB]: 13432
% 7.80/1.34  % (7782)Time elapsed: 0.405 s
% 7.80/1.34  % (7782)------------------------------
% 7.80/1.34  % (7782)------------------------------
% 7.80/1.35  % (7781)Termination reason: Time limit
% 7.80/1.35  
% 7.80/1.35  % (7781)Memory used [KB]: 7803
% 7.80/1.35  % (7781)Time elapsed: 0.421 s
% 7.80/1.35  % (7781)------------------------------
% 7.80/1.35  % (7781)------------------------------
% 7.80/1.41  % (7722)Time limit reached!
% 7.80/1.41  % (7722)------------------------------
% 7.80/1.41  % (7722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.41  % (7722)Termination reason: Time limit
% 7.80/1.41  % (7722)Termination phase: Saturation
% 7.80/1.41  
% 7.80/1.41  % (7722)Memory used [KB]: 16502
% 7.80/1.41  % (7722)Time elapsed: 1.0000 s
% 7.80/1.41  % (7722)------------------------------
% 7.80/1.41  % (7722)------------------------------
% 7.80/1.41  % (7744)Refutation found. Thanks to Tanya!
% 7.80/1.41  % SZS status Theorem for theBenchmark
% 7.80/1.41  % SZS output start Proof for theBenchmark
% 7.80/1.41  fof(f6244,plain,(
% 7.80/1.41    $false),
% 7.80/1.41    inference(unit_resulting_resolution,[],[f1600,f94,f1520])).
% 7.80/1.41  fof(f1520,plain,(
% 7.80/1.41    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~sP5(X8,X7,X6,X5,X4,X3,X2,X1,X0,X0) | r2_hidden(X8,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 7.80/1.41    inference(superposition,[],[f93,f78])).
% 7.80/1.41  fof(f78,plain,(
% 7.80/1.41    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7)))) )),
% 7.80/1.41    inference(definition_unfolding,[],[f54,f75,f72,f72])).
% 7.80/1.41  fof(f72,plain,(
% 7.80/1.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.80/1.41    inference(definition_unfolding,[],[f50,f71])).
% 7.80/1.41  fof(f71,plain,(
% 7.80/1.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.80/1.41    inference(definition_unfolding,[],[f51,f70])).
% 7.80/1.41  fof(f70,plain,(
% 7.80/1.41    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.80/1.41    inference(definition_unfolding,[],[f52,f53])).
% 7.80/1.41  fof(f53,plain,(
% 7.80/1.41    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.80/1.41    inference(cnf_transformation,[],[f20])).
% 7.80/1.41  fof(f20,axiom,(
% 7.80/1.41    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.80/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 7.80/1.41  fof(f52,plain,(
% 7.80/1.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.80/1.41    inference(cnf_transformation,[],[f19])).
% 7.80/1.41  fof(f19,axiom,(
% 7.80/1.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.80/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 7.80/1.41  fof(f51,plain,(
% 7.80/1.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.80/1.41    inference(cnf_transformation,[],[f18])).
% 7.80/1.41  fof(f18,axiom,(
% 7.80/1.41    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.80/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 7.80/1.41  fof(f50,plain,(
% 7.80/1.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.80/1.41    inference(cnf_transformation,[],[f17])).
% 7.80/1.41  fof(f17,axiom,(
% 7.80/1.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.80/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 7.80/1.41  fof(f75,plain,(
% 7.80/1.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.80/1.41    inference(definition_unfolding,[],[f35,f74])).
% 7.80/1.42  % (7942)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.80/1.43  fof(f74,plain,(
% 7.80/1.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.80/1.43    inference(definition_unfolding,[],[f36,f73])).
% 7.80/1.43  fof(f73,plain,(
% 7.80/1.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.80/1.43    inference(definition_unfolding,[],[f40,f72])).
% 7.80/1.43  fof(f40,plain,(
% 7.80/1.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.80/1.43    inference(cnf_transformation,[],[f16])).
% 7.80/1.43  fof(f16,axiom,(
% 7.80/1.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 7.80/1.43  fof(f36,plain,(
% 7.80/1.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.80/1.43    inference(cnf_transformation,[],[f15])).
% 7.80/1.43  fof(f15,axiom,(
% 7.80/1.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 7.80/1.43  fof(f35,plain,(
% 7.80/1.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.80/1.43    inference(cnf_transformation,[],[f21])).
% 7.80/1.43  fof(f21,axiom,(
% 7.80/1.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 7.80/1.43  fof(f54,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 7.80/1.43    inference(cnf_transformation,[],[f12])).
% 7.80/1.43  fof(f12,axiom,(
% 7.80/1.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 7.80/1.43  fof(f93,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) | ~sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) )),
% 7.80/1.43    inference(equality_resolution,[],[f89])).
% 7.80/1.43  fof(f89,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (~sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9) | k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) != X9) )),
% 7.80/1.43    inference(definition_unfolding,[],[f66,f76])).
% 7.80/1.43  fof(f76,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) )),
% 7.80/1.43    inference(definition_unfolding,[],[f55,f75,f71,f72])).
% 7.80/1.43  fof(f55,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 7.80/1.43    inference(cnf_transformation,[],[f13])).
% 7.80/1.43  fof(f13,axiom,(
% 7.80/1.43    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 7.80/1.43  fof(f66,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (~sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 7.80/1.43    inference(cnf_transformation,[],[f27])).
% 7.80/1.43  fof(f27,plain,(
% 7.80/1.43    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 7.80/1.43    inference(ennf_transformation,[],[f11])).
% 7.80/1.43  fof(f11,axiom,(
% 7.80/1.43    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).
% 7.80/1.43  fof(f94,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X10,X7,X5,X3,X1] : (sP5(X10,X10,X7,X6,X5,X4,X3,X2,X1,X0)) )),
% 7.80/1.43    inference(equality_resolution,[],[f64])).
% 7.80/1.43  fof(f64,plain,(
% 7.80/1.43    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (X8 != X10 | sP5(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) )),
% 7.80/1.43    inference(cnf_transformation,[],[f27])).
% 7.80/1.43  fof(f1600,plain,(
% 7.80/1.43    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 7.80/1.43    inference(unit_resulting_resolution,[],[f1582,f44])).
% 7.80/1.43  fof(f44,plain,(
% 7.80/1.43    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 7.80/1.43    inference(cnf_transformation,[],[f3])).
% 7.80/1.43  fof(f3,axiom,(
% 7.80/1.43    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 7.80/1.43  fof(f1582,plain,(
% 7.80/1.43    ~sP3(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 7.80/1.43    inference(unit_resulting_resolution,[],[f29,f1579])).
% 7.80/1.43  fof(f1579,plain,(
% 7.80/1.43    ( ! [X2] : (~sP3(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | r2_hidden(X2,sK1)) )),
% 7.80/1.43    inference(superposition,[],[f91,f916])).
% 7.80/1.43  fof(f916,plain,(
% 7.80/1.43    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 7.80/1.43    inference(forward_demodulation,[],[f913,f132])).
% 7.80/1.43  fof(f132,plain,(
% 7.80/1.43    ( ! [X0,X1] : (k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = X0) )),
% 7.80/1.43    inference(unit_resulting_resolution,[],[f80,f104])).
% 7.80/1.43  fof(f104,plain,(
% 7.80/1.43    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = X3 | ~r1_tarski(X3,X4)) )),
% 7.80/1.43    inference(superposition,[],[f39,f33])).
% 7.80/1.43  fof(f33,plain,(
% 7.80/1.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.80/1.43    inference(cnf_transformation,[],[f1])).
% 7.80/1.43  fof(f1,axiom,(
% 7.80/1.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.80/1.43  fof(f39,plain,(
% 7.80/1.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.80/1.43    inference(cnf_transformation,[],[f26])).
% 7.80/1.43  fof(f26,plain,(
% 7.80/1.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.80/1.43    inference(ennf_transformation,[],[f7])).
% 7.80/1.43  fof(f7,axiom,(
% 7.80/1.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.80/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 7.80/1.43  fof(f80,plain,(
% 7.80/1.43    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.80/1.43    inference(definition_unfolding,[],[f32,f75])).
% 8.49/1.44  fof(f32,plain,(
% 8.49/1.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.49/1.44    inference(cnf_transformation,[],[f8])).
% 8.49/1.44  fof(f8,axiom,(
% 8.49/1.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 8.49/1.44  fof(f913,plain,(
% 8.49/1.44    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 8.49/1.44    inference(backward_demodulation,[],[f566,f876])).
% 8.49/1.44  fof(f876,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,X0)))) )),
% 8.49/1.44    inference(superposition,[],[f594,f34])).
% 8.49/1.44  fof(f34,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 8.49/1.44    inference(cnf_transformation,[],[f2])).
% 8.49/1.44  fof(f2,axiom,(
% 8.49/1.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 8.49/1.44  fof(f594,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0)))) )),
% 8.49/1.44    inference(backward_demodulation,[],[f81,f577])).
% 8.49/1.44  fof(f577,plain,(
% 8.49/1.44    ( ! [X6,X5] : (k3_xboole_0(X6,k5_xboole_0(X6,X5)) = k5_xboole_0(X6,k3_xboole_0(X6,X5))) )),
% 8.49/1.44    inference(superposition,[],[f557,f33])).
% 8.49/1.44  fof(f557,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 8.49/1.44    inference(forward_demodulation,[],[f532,f33])).
% 8.49/1.44  fof(f532,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 8.49/1.44    inference(superposition,[],[f42,f31])).
% 8.49/1.44  fof(f31,plain,(
% 8.49/1.44    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.49/1.44    inference(cnf_transformation,[],[f24])).
% 8.49/1.44  fof(f24,plain,(
% 8.49/1.44    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 8.49/1.44    inference(rectify,[],[f4])).
% 8.49/1.44  fof(f4,axiom,(
% 8.49/1.44    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 8.49/1.44  fof(f42,plain,(
% 8.49/1.44    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 8.49/1.44    inference(cnf_transformation,[],[f6])).
% 8.49/1.44  fof(f6,axiom,(
% 8.49/1.44    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 8.49/1.44  fof(f81,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 8.49/1.44    inference(definition_unfolding,[],[f38,f75,f37])).
% 8.49/1.44  fof(f37,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.49/1.44    inference(cnf_transformation,[],[f5])).
% 8.49/1.44  fof(f5,axiom,(
% 8.49/1.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 8.49/1.44  fof(f38,plain,(
% 8.49/1.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.49/1.44    inference(cnf_transformation,[],[f10])).
% 8.49/1.44  fof(f10,axiom,(
% 8.49/1.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 8.49/1.44  fof(f566,plain,(
% 8.49/1.44    k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 8.49/1.44    inference(forward_demodulation,[],[f560,f34])).
% 8.49/1.44  fof(f560,plain,(
% 8.49/1.44    k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),sK1)),
% 8.49/1.44    inference(backward_demodulation,[],[f265,f557])).
% 8.49/1.44  fof(f265,plain,(
% 8.49/1.44    k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 8.49/1.44    inference(unit_resulting_resolution,[],[f131,f39])).
% 8.49/1.44  fof(f131,plain,(
% 8.49/1.44    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 8.49/1.44    inference(forward_demodulation,[],[f130,f34])).
% 8.49/1.44  fof(f130,plain,(
% 8.49/1.44    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 8.49/1.44    inference(backward_demodulation,[],[f103,f124])).
% 8.49/1.44  fof(f124,plain,(
% 8.49/1.44    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 8.49/1.44    inference(superposition,[],[f41,f34])).
% 8.49/1.44  fof(f41,plain,(
% 8.49/1.44    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 8.49/1.44    inference(cnf_transformation,[],[f9])).
% 8.49/1.44  fof(f9,axiom,(
% 8.49/1.44    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 8.49/1.44  fof(f103,plain,(
% 8.49/1.44    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 8.49/1.44    inference(backward_demodulation,[],[f79,f81])).
% 8.49/1.44  fof(f79,plain,(
% 8.49/1.44    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 8.49/1.44    inference(definition_unfolding,[],[f28,f75,f77])).
% 8.49/1.44  fof(f77,plain,(
% 8.49/1.44    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 8.49/1.44    inference(definition_unfolding,[],[f30,f74])).
% 8.49/1.44  fof(f30,plain,(
% 8.49/1.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 8.49/1.44    inference(cnf_transformation,[],[f14])).
% 8.49/1.44  fof(f14,axiom,(
% 8.49/1.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 8.49/1.44  fof(f28,plain,(
% 8.49/1.44    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 8.49/1.44    inference(cnf_transformation,[],[f25])).
% 8.49/1.44  fof(f25,plain,(
% 8.49/1.44    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 8.49/1.44    inference(ennf_transformation,[],[f23])).
% 8.49/1.44  fof(f23,negated_conjecture,(
% 8.49/1.44    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 8.49/1.44    inference(negated_conjecture,[],[f22])).
% 8.49/1.44  fof(f22,conjecture,(
% 8.49/1.44    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 8.49/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 8.49/1.44  fof(f91,plain,(
% 8.49/1.44    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~sP3(X3,X1,X0)) )),
% 8.49/1.44    inference(equality_resolution,[],[f85])).
% 8.49/1.44  fof(f85,plain,(
% 8.49/1.44    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 8.49/1.44    inference(definition_unfolding,[],[f46,f75])).
% 8.49/1.44  fof(f46,plain,(
% 8.49/1.44    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 8.49/1.44    inference(cnf_transformation,[],[f3])).
% 8.49/1.44  fof(f29,plain,(
% 8.49/1.44    ~r2_hidden(sK0,sK1)),
% 8.49/1.44    inference(cnf_transformation,[],[f25])).
% 8.49/1.44  % SZS output end Proof for theBenchmark
% 8.49/1.44  % (7744)------------------------------
% 8.49/1.44  % (7744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.49/1.44  % (7744)Termination reason: Refutation
% 8.49/1.44  
% 8.49/1.44  % (7744)Memory used [KB]: 13688
% 8.49/1.44  % (7744)Time elapsed: 1.024 s
% 8.49/1.44  % (7744)------------------------------
% 8.49/1.44  % (7744)------------------------------
% 8.49/1.44  % (7719)Success in time 1.103 s
%------------------------------------------------------------------------------
