%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:58 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 349 expanded)
%              Number of leaves         :   20 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  162 ( 516 expanded)
%              Number of equality atoms :   76 ( 353 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3723,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1269,f1332,f917,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f917,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f98,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP7(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f71,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f98,plain,(
    ! [X4,X0,X1] : sP7(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP7(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1332,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(global_subsumption,[],[f1269,f1331])).

fof(f1331,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(trivial_inequality_removal,[],[f1292])).

fof(f1292,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f593,f93])).

fof(f93,plain,(
    ! [X2,X1] :
      ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ) ),
    inference(definition_unfolding,[],[f53,f83,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f81])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f82])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f593,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f591,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f591,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f102,f590])).

fof(f590,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f546,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f546,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f51,f38])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f102,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f84,f40])).

fof(f84,plain,
    ( r2_hidden(sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f35,f83,f43,f83])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f1269,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1264])).

fof(f1264,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f1256,f98])).

fof(f1256,plain,(
    ! [X0] :
      ( ~ sP7(X0,sK0,sK0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK0,sK1) ) ),
    inference(resolution,[],[f1110,f97])).

fof(f1110,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f1072,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
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

fof(f1072,plain,
    ( r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f923,f594])).

fof(f594,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f592,f39])).

fof(f592,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f101,f590])).

fof(f101,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f85,f40])).

fof(f85,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f34,f83,f43,f83])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f923,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f679,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f679,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f120,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f120,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.48  % (22877)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.49  % (22885)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (22871)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (22869)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (22872)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (22873)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (22872)Refutation not found, incomplete strategy% (22872)------------------------------
% 0.22/0.52  % (22872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22872)Memory used [KB]: 10746
% 0.22/0.52  % (22872)Time elapsed: 0.106 s
% 0.22/0.52  % (22872)------------------------------
% 0.22/0.52  % (22872)------------------------------
% 0.22/0.52  % (22886)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (22893)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (22868)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (22866)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (22878)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (22892)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (22870)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (22891)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (22876)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (22888)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (22882)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (22887)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (22867)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (22890)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (22865)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (22874)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (22884)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (22883)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (22880)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (22889)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (22875)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (22881)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (22864)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (22881)Refutation not found, incomplete strategy% (22881)------------------------------
% 0.22/0.56  % (22881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22881)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22881)Memory used [KB]: 10746
% 0.22/0.56  % (22881)Time elapsed: 0.150 s
% 0.22/0.56  % (22881)------------------------------
% 0.22/0.56  % (22881)------------------------------
% 1.56/0.57  % (22879)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.23/0.67  % (22895)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.69/0.72  % (22894)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.02/0.81  % (22888)Refutation found. Thanks to Tanya!
% 3.02/0.81  % SZS status Theorem for theBenchmark
% 3.02/0.81  % SZS output start Proof for theBenchmark
% 3.02/0.81  fof(f3723,plain,(
% 3.02/0.81    $false),
% 3.02/0.81    inference(unit_resulting_resolution,[],[f1269,f1332,f917,f63])).
% 3.02/0.81  fof(f63,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f32])).
% 3.02/0.81  fof(f32,plain,(
% 3.02/0.81    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.02/0.81    inference(ennf_transformation,[],[f6])).
% 3.02/0.81  fof(f6,axiom,(
% 3.02/0.81    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 3.02/0.81  fof(f917,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) )),
% 3.02/0.81    inference(unit_resulting_resolution,[],[f98,f97])).
% 3.02/0.81  fof(f97,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP7(X4,X2,X1,X0)) )),
% 3.02/0.81    inference(equality_resolution,[],[f92])).
% 3.02/0.81  fof(f92,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.02/0.81    inference(definition_unfolding,[],[f71,f81])).
% 3.02/0.81  fof(f81,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.02/0.81    inference(definition_unfolding,[],[f49,f80])).
% 3.02/0.81  fof(f80,plain,(
% 3.02/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.02/0.81    inference(definition_unfolding,[],[f66,f79])).
% 3.02/0.81  fof(f79,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.02/0.81    inference(definition_unfolding,[],[f75,f78])).
% 3.02/0.81  fof(f78,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.02/0.81    inference(definition_unfolding,[],[f76,f77])).
% 3.02/0.81  fof(f77,plain,(
% 3.02/0.81    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f21])).
% 3.02/0.81  fof(f21,axiom,(
% 3.02/0.81    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.02/0.81  fof(f76,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f20])).
% 3.02/0.81  fof(f20,axiom,(
% 3.02/0.81    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.02/0.81  fof(f75,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f19])).
% 3.02/0.81  fof(f19,axiom,(
% 3.02/0.81    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.02/0.81  fof(f66,plain,(
% 3.02/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f18])).
% 3.02/0.81  fof(f18,axiom,(
% 3.02/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.02/0.81  fof(f49,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f17])).
% 3.02/0.81  fof(f17,axiom,(
% 3.02/0.81    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.02/0.81  fof(f71,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.02/0.81    inference(cnf_transformation,[],[f33])).
% 3.02/0.81  fof(f33,plain,(
% 3.02/0.81    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.02/0.81    inference(ennf_transformation,[],[f13])).
% 3.02/0.81  fof(f13,axiom,(
% 3.02/0.81    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 3.02/0.81  fof(f98,plain,(
% 3.02/0.81    ( ! [X4,X0,X1] : (sP7(X4,X4,X1,X0)) )),
% 3.02/0.81    inference(equality_resolution,[],[f69])).
% 3.02/0.81  fof(f69,plain,(
% 3.02/0.81    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP7(X4,X2,X1,X0)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f33])).
% 3.02/0.81  fof(f1332,plain,(
% 3.02/0.81    ~r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.02/0.81    inference(global_subsumption,[],[f1269,f1331])).
% 3.02/0.81  fof(f1331,plain,(
% 3.02/0.81    r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.02/0.81    inference(trivial_inequality_removal,[],[f1292])).
% 3.02/0.81  fof(f1292,plain,(
% 3.02/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.02/0.81    inference(superposition,[],[f593,f93])).
% 3.02/0.81  fof(f93,plain,(
% 3.02/0.81    ( ! [X2,X1] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1) | ~r2_hidden(X2,X1)) )),
% 3.02/0.81    inference(equality_resolution,[],[f86])).
% 3.02/0.81  fof(f86,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) )),
% 3.02/0.81    inference(definition_unfolding,[],[f53,f83,f82])).
% 3.02/0.81  fof(f82,plain,(
% 3.02/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.02/0.81    inference(definition_unfolding,[],[f42,f81])).
% 3.02/0.81  fof(f42,plain,(
% 3.02/0.81    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f16])).
% 3.02/0.81  fof(f16,axiom,(
% 3.02/0.81    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.02/0.81  fof(f83,plain,(
% 3.02/0.81    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.02/0.81    inference(definition_unfolding,[],[f36,f82])).
% 3.02/0.81  fof(f36,plain,(
% 3.02/0.81    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f15])).
% 3.02/0.81  fof(f15,axiom,(
% 3.02/0.81    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.02/0.81  fof(f53,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f31])).
% 3.02/0.81  fof(f31,plain,(
% 3.02/0.81    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.02/0.81    inference(flattening,[],[f30])).
% 3.02/0.81  fof(f30,plain,(
% 3.02/0.81    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 3.02/0.81    inference(ennf_transformation,[],[f22])).
% 3.02/0.81  fof(f22,axiom,(
% 3.02/0.81    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 3.02/0.81  fof(f593,plain,(
% 3.02/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(forward_demodulation,[],[f591,f39])).
% 3.02/0.81  fof(f39,plain,(
% 3.02/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f2])).
% 3.02/0.81  fof(f2,axiom,(
% 3.02/0.81    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.02/0.81  fof(f591,plain,(
% 3.02/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(backward_demodulation,[],[f102,f590])).
% 3.02/0.81  fof(f590,plain,(
% 3.02/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 3.02/0.81    inference(forward_demodulation,[],[f546,f40])).
% 3.02/0.81  fof(f40,plain,(
% 3.02/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f1])).
% 3.02/0.81  fof(f1,axiom,(
% 3.02/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.02/0.81  fof(f546,plain,(
% 3.02/0.81    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 3.02/0.81    inference(superposition,[],[f51,f38])).
% 3.02/0.81  fof(f38,plain,(
% 3.02/0.81    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.02/0.81    inference(cnf_transformation,[],[f25])).
% 3.02/0.81  fof(f25,plain,(
% 3.02/0.81    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.02/0.81    inference(rectify,[],[f5])).
% 3.02/0.81  fof(f5,axiom,(
% 3.02/0.81    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.02/0.81  fof(f51,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f11])).
% 3.02/0.81  fof(f11,axiom,(
% 3.02/0.81    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 3.02/0.81  fof(f102,plain,(
% 3.02/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(backward_demodulation,[],[f84,f40])).
% 3.02/0.81  fof(f84,plain,(
% 3.02/0.81    r2_hidden(sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 3.02/0.81    inference(definition_unfolding,[],[f35,f83,f43,f83])).
% 3.02/0.81  fof(f43,plain,(
% 3.02/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.02/0.81    inference(cnf_transformation,[],[f10])).
% 3.02/0.81  fof(f10,axiom,(
% 3.02/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.02/0.81  fof(f35,plain,(
% 3.02/0.81    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.02/0.81    inference(cnf_transformation,[],[f27])).
% 3.02/0.81  fof(f27,plain,(
% 3.02/0.81    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 3.02/0.81    inference(ennf_transformation,[],[f24])).
% 3.02/0.81  fof(f24,negated_conjecture,(
% 3.02/0.81    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 3.02/0.81    inference(negated_conjecture,[],[f23])).
% 3.02/0.81  fof(f23,conjecture,(
% 3.02/0.81    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 3.02/0.81  fof(f1269,plain,(
% 3.02/0.81    ~r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(duplicate_literal_removal,[],[f1264])).
% 3.02/0.81  fof(f1264,plain,(
% 3.02/0.81    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(resolution,[],[f1256,f98])).
% 3.02/0.81  fof(f1256,plain,(
% 3.02/0.81    ( ! [X0] : (~sP7(X0,sK0,sK0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK0,sK1)) )),
% 3.02/0.81    inference(resolution,[],[f1110,f97])).
% 3.02/0.81  fof(f1110,plain,(
% 3.02/0.81    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(X0,sK1)) )),
% 3.02/0.81    inference(resolution,[],[f1072,f44])).
% 3.02/0.81  fof(f44,plain,(
% 3.02/0.81    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.02/0.81    inference(cnf_transformation,[],[f29])).
% 3.02/0.81  fof(f29,plain,(
% 3.02/0.81    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.02/0.81    inference(ennf_transformation,[],[f26])).
% 3.02/0.81  fof(f26,plain,(
% 3.02/0.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.02/0.81    inference(rectify,[],[f7])).
% 3.02/0.81  fof(f7,axiom,(
% 3.02/0.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.02/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.02/0.81  fof(f1072,plain,(
% 3.02/0.81    r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(superposition,[],[f923,f594])).
% 3.02/0.81  fof(f594,plain,(
% 3.02/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(forward_demodulation,[],[f592,f39])).
% 3.02/0.81  fof(f592,plain,(
% 3.02/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(backward_demodulation,[],[f101,f590])).
% 3.02/0.81  fof(f101,plain,(
% 3.02/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,sK1)),
% 3.02/0.81    inference(backward_demodulation,[],[f85,f40])).
% 3.02/0.81  fof(f85,plain,(
% 3.02/0.81    ~r2_hidden(sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 3.02/0.81    inference(definition_unfolding,[],[f34,f83,f43,f83])).
% 3.02/0.81  fof(f34,plain,(
% 3.02/0.81    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.02/0.81    inference(cnf_transformation,[],[f27])).
% 3.02/0.82  fof(f923,plain,(
% 3.02/0.82    ( ! [X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 3.02/0.82    inference(unit_resulting_resolution,[],[f679,f47])).
% 3.02/0.82  fof(f47,plain,(
% 3.02/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 3.02/0.82    inference(cnf_transformation,[],[f4])).
% 3.02/0.82  fof(f4,axiom,(
% 3.02/0.82    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.02/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.02/0.82  fof(f679,plain,(
% 3.02/0.82    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 3.02/0.82    inference(superposition,[],[f120,f50])).
% 3.02/0.82  fof(f50,plain,(
% 3.02/0.82    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 3.02/0.82    inference(cnf_transformation,[],[f12])).
% 3.02/0.82  fof(f12,axiom,(
% 3.02/0.82    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 3.02/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 3.02/0.82  fof(f120,plain,(
% 3.02/0.82    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.02/0.82    inference(unit_resulting_resolution,[],[f41,f48])).
% 3.02/0.82  fof(f48,plain,(
% 3.02/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.02/0.82    inference(cnf_transformation,[],[f4])).
% 3.02/0.82  fof(f41,plain,(
% 3.02/0.82    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.02/0.82    inference(cnf_transformation,[],[f9])).
% 3.02/0.82  fof(f9,axiom,(
% 3.02/0.82    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.02/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 3.02/0.82  % SZS output end Proof for theBenchmark
% 3.02/0.82  % (22888)------------------------------
% 3.02/0.82  % (22888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.82  % (22888)Termination reason: Refutation
% 3.02/0.82  
% 3.02/0.82  % (22888)Memory used [KB]: 9338
% 3.02/0.82  % (22888)Time elapsed: 0.401 s
% 3.02/0.82  % (22888)------------------------------
% 3.02/0.82  % (22888)------------------------------
% 3.02/0.82  % (22863)Success in time 0.462 s
%------------------------------------------------------------------------------
