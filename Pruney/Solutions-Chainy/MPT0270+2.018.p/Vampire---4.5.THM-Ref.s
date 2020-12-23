%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:58 EST 2020

% Result     : Theorem 3.78s
% Output     : Refutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 369 expanded)
%              Number of leaves         :   18 ( 115 expanded)
%              Depth                    :   19
%              Number of atoms          :  155 ( 528 expanded)
%              Number of equality atoms :   69 ( 367 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3708,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f100,f1739,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP7(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1739,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f1110,f1280,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1280,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(global_subsumption,[],[f1110,f1279])).

fof(f1279,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(trivial_inequality_removal,[],[f1231])).

fof(f1231,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f597,f95])).

fof(f95,plain,(
    ! [X2,X1] :
      ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ) ),
    inference(definition_unfolding,[],[f54,f84,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f83])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f597,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f595,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f595,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f104,f589])).

fof(f589,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f558,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f558,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f52,f40])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f104,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f85,f43])).

fof(f85,plain,
    ( r2_hidden(sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f36,f84,f46,f84])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f1110,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1105])).

fof(f1105,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f1101,f100])).

fof(f1101,plain,(
    ! [X0] :
      ( ~ sP7(X0,sK0,sK0,sK0)
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f1074,f99])).

fof(f1074,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK0,sK1) ) ),
    inference(resolution,[],[f1032,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1032,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f627,f598])).

fof(f598,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f596,f42])).

fof(f596,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f103,f589])).

fof(f103,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f86,f43])).

fof(f86,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f35,f84,f46,f84])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f627,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X2) ),
    inference(superposition,[],[f594,f42])).

fof(f594,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),X2) ),
    inference(backward_demodulation,[],[f129,f589])).

fof(f129,plain,(
    ! [X2,X1] : r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(superposition,[],[f87,f43])).

fof(f87,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f100,plain,(
    ! [X4,X0,X1] : sP7(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP7(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (15875)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (15869)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (15883)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (15880)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (15887)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (15876)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (15878)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (15898)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (15890)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (15886)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (15871)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (15888)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (15881)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (15882)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (15872)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (15892)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.55  % (15884)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.55  % (15874)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.55  % (15895)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.55  % (15873)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.56  % (15896)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.56  % (15885)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.56  % (15870)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.56  % (15879)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.56  % (15894)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.57  % (15877)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.57  % (15889)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.57  % (15893)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.58  % (15897)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.58  % (15891)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.58  % (15877)Refutation not found, incomplete strategy% (15877)------------------------------
% 1.53/0.58  % (15877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (15877)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (15877)Memory used [KB]: 10746
% 1.53/0.59  % (15877)Time elapsed: 0.165 s
% 1.53/0.59  % (15877)------------------------------
% 1.53/0.59  % (15877)------------------------------
% 3.06/0.76  % (15899)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.78/0.86  % (15874)Time limit reached!
% 3.78/0.86  % (15874)------------------------------
% 3.78/0.86  % (15874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.86  % (15874)Termination reason: Time limit
% 3.78/0.86  % (15874)Termination phase: Saturation
% 3.78/0.86  
% 3.78/0.86  % (15874)Memory used [KB]: 8955
% 3.78/0.86  % (15874)Time elapsed: 0.400 s
% 3.78/0.86  % (15874)------------------------------
% 3.78/0.86  % (15874)------------------------------
% 3.78/0.91  % (15893)Refutation found. Thanks to Tanya!
% 3.78/0.91  % SZS status Theorem for theBenchmark
% 3.78/0.91  % SZS output start Proof for theBenchmark
% 3.78/0.91  fof(f3708,plain,(
% 3.78/0.91    $false),
% 3.78/0.91    inference(unit_resulting_resolution,[],[f100,f1739,f99])).
% 3.78/0.91  fof(f99,plain,(
% 3.78/0.91    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP7(X4,X2,X1,X0)) )),
% 3.78/0.91    inference(equality_resolution,[],[f94])).
% 3.78/0.91  fof(f94,plain,(
% 3.78/0.91    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.78/0.91    inference(definition_unfolding,[],[f72,f82])).
% 3.78/0.92  fof(f82,plain,(
% 3.78/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f50,f81])).
% 3.78/0.92  fof(f81,plain,(
% 3.78/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f67,f80])).
% 3.78/0.92  fof(f80,plain,(
% 3.78/0.92    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f76,f79])).
% 3.78/0.92  fof(f79,plain,(
% 3.78/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f77,f78])).
% 3.78/0.92  fof(f78,plain,(
% 3.78/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f22])).
% 3.78/0.92  fof(f22,axiom,(
% 3.78/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 3.78/0.92  fof(f77,plain,(
% 3.78/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f21])).
% 3.78/0.92  fof(f21,axiom,(
% 3.78/0.92    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 3.78/0.92  fof(f76,plain,(
% 3.78/0.92    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f20])).
% 3.78/0.92  fof(f20,axiom,(
% 3.78/0.92    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.78/0.92  fof(f67,plain,(
% 3.78/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f19])).
% 3.78/0.92  fof(f19,axiom,(
% 3.78/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.78/0.92  fof(f50,plain,(
% 3.78/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f18])).
% 3.78/0.92  fof(f18,axiom,(
% 3.78/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.78/0.92  fof(f72,plain,(
% 3.78/0.92    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.78/0.92    inference(cnf_transformation,[],[f34])).
% 3.78/0.92  fof(f34,plain,(
% 3.78/0.92    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.78/0.92    inference(ennf_transformation,[],[f14])).
% 3.78/0.92  fof(f14,axiom,(
% 3.78/0.92    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 3.78/0.92  fof(f1739,plain,(
% 3.78/0.92    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.92    inference(unit_resulting_resolution,[],[f1110,f1280,f64])).
% 3.78/0.92  fof(f64,plain,(
% 3.78/0.92    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f33])).
% 3.78/0.92  fof(f33,plain,(
% 3.78/0.92    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.78/0.92    inference(ennf_transformation,[],[f5])).
% 3.78/0.92  fof(f5,axiom,(
% 3.78/0.92    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 3.78/0.92  fof(f1280,plain,(
% 3.78/0.92    ~r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.78/0.92    inference(global_subsumption,[],[f1110,f1279])).
% 3.78/0.92  fof(f1279,plain,(
% 3.78/0.92    r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.78/0.92    inference(trivial_inequality_removal,[],[f1231])).
% 3.78/0.92  fof(f1231,plain,(
% 3.78/0.92    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 3.78/0.92    inference(superposition,[],[f597,f95])).
% 3.78/0.92  fof(f95,plain,(
% 3.78/0.92    ( ! [X2,X1] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1) | ~r2_hidden(X2,X1)) )),
% 3.78/0.92    inference(equality_resolution,[],[f88])).
% 3.78/0.92  fof(f88,plain,(
% 3.78/0.92    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f54,f84,f83])).
% 3.78/0.92  fof(f83,plain,(
% 3.78/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f45,f82])).
% 3.78/0.92  fof(f45,plain,(
% 3.78/0.92    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f17])).
% 3.78/0.92  fof(f17,axiom,(
% 3.78/0.92    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.78/0.92  fof(f84,plain,(
% 3.78/0.92    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f38,f83])).
% 3.78/0.92  fof(f38,plain,(
% 3.78/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f16])).
% 3.78/0.92  fof(f16,axiom,(
% 3.78/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.78/0.92  fof(f54,plain,(
% 3.78/0.92    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f32])).
% 3.78/0.92  fof(f32,plain,(
% 3.78/0.92    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.78/0.92    inference(flattening,[],[f31])).
% 3.78/0.92  fof(f31,plain,(
% 3.78/0.92    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 3.78/0.92    inference(ennf_transformation,[],[f23])).
% 3.78/0.92  fof(f23,axiom,(
% 3.78/0.92    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 3.78/0.92  fof(f597,plain,(
% 3.78/0.92    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(forward_demodulation,[],[f595,f42])).
% 3.78/0.92  fof(f42,plain,(
% 3.78/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f2])).
% 3.78/0.92  fof(f2,axiom,(
% 3.78/0.92    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.78/0.92  fof(f595,plain,(
% 3.78/0.92    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(backward_demodulation,[],[f104,f589])).
% 3.78/0.92  fof(f589,plain,(
% 3.78/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.78/0.92    inference(forward_demodulation,[],[f558,f43])).
% 3.78/0.92  fof(f43,plain,(
% 3.78/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f1])).
% 3.78/0.92  fof(f1,axiom,(
% 3.78/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.78/0.92  fof(f558,plain,(
% 3.78/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 3.78/0.92    inference(superposition,[],[f52,f40])).
% 3.78/0.92  fof(f40,plain,(
% 3.78/0.92    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.78/0.92    inference(cnf_transformation,[],[f26])).
% 3.78/0.92  fof(f26,plain,(
% 3.78/0.92    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.78/0.92    inference(rectify,[],[f4])).
% 3.78/0.92  fof(f4,axiom,(
% 3.78/0.92    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.78/0.92  fof(f52,plain,(
% 3.78/0.92    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f10])).
% 3.78/0.92  fof(f10,axiom,(
% 3.78/0.92    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 3.78/0.92  fof(f104,plain,(
% 3.78/0.92    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(backward_demodulation,[],[f85,f43])).
% 3.78/0.92  fof(f85,plain,(
% 3.78/0.92    r2_hidden(sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 3.78/0.92    inference(definition_unfolding,[],[f36,f84,f46,f84])).
% 3.78/0.92  fof(f46,plain,(
% 3.78/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.78/0.92    inference(cnf_transformation,[],[f9])).
% 3.78/0.92  fof(f9,axiom,(
% 3.78/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.78/0.92  fof(f36,plain,(
% 3.78/0.92    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.78/0.92    inference(cnf_transformation,[],[f28])).
% 3.78/0.92  fof(f28,plain,(
% 3.78/0.92    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 3.78/0.92    inference(ennf_transformation,[],[f25])).
% 3.78/0.92  fof(f25,negated_conjecture,(
% 3.78/0.92    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 3.78/0.92    inference(negated_conjecture,[],[f24])).
% 3.78/0.92  fof(f24,conjecture,(
% 3.78/0.92    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 3.78/0.92  fof(f1110,plain,(
% 3.78/0.92    ~r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(duplicate_literal_removal,[],[f1105])).
% 3.78/0.92  fof(f1105,plain,(
% 3.78/0.92    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(resolution,[],[f1101,f100])).
% 3.78/0.92  fof(f1101,plain,(
% 3.78/0.92    ( ! [X0] : (~sP7(X0,sK0,sK0,sK0) | ~r2_hidden(sK0,sK1) | ~r2_hidden(X0,sK1)) )),
% 3.78/0.92    inference(resolution,[],[f1074,f99])).
% 3.78/0.92  fof(f1074,plain,(
% 3.78/0.92    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK0,sK1)) )),
% 3.78/0.92    inference(resolution,[],[f1032,f47])).
% 3.78/0.92  fof(f47,plain,(
% 3.78/0.92    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f30])).
% 3.78/0.92  fof(f30,plain,(
% 3.78/0.92    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.78/0.92    inference(ennf_transformation,[],[f27])).
% 3.78/0.92  fof(f27,plain,(
% 3.78/0.92    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.78/0.92    inference(rectify,[],[f6])).
% 3.78/0.92  fof(f6,axiom,(
% 3.78/0.92    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.78/0.92  fof(f1032,plain,(
% 3.78/0.92    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(superposition,[],[f627,f598])).
% 3.78/0.92  fof(f598,plain,(
% 3.78/0.92    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(forward_demodulation,[],[f596,f42])).
% 3.78/0.92  fof(f596,plain,(
% 3.78/0.92    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(backward_demodulation,[],[f103,f589])).
% 3.78/0.92  fof(f103,plain,(
% 3.78/0.92    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,sK1)),
% 3.78/0.92    inference(backward_demodulation,[],[f86,f43])).
% 3.78/0.92  fof(f86,plain,(
% 3.78/0.92    ~r2_hidden(sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 3.78/0.92    inference(definition_unfolding,[],[f35,f84,f46,f84])).
% 3.78/0.92  fof(f35,plain,(
% 3.78/0.92    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.78/0.92    inference(cnf_transformation,[],[f28])).
% 3.78/0.92  fof(f627,plain,(
% 3.78/0.92    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X2)) )),
% 3.78/0.92    inference(superposition,[],[f594,f42])).
% 3.78/0.92  fof(f594,plain,(
% 3.78/0.92    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),X2)) )),
% 3.78/0.92    inference(backward_demodulation,[],[f129,f589])).
% 3.78/0.92  fof(f129,plain,(
% 3.78/0.92    ( ! [X2,X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)) )),
% 3.78/0.92    inference(superposition,[],[f87,f43])).
% 3.78/0.92  fof(f87,plain,(
% 3.78/0.92    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.78/0.92    inference(definition_unfolding,[],[f41,f46])).
% 3.78/0.92  fof(f41,plain,(
% 3.78/0.92    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f13])).
% 3.78/0.92  fof(f13,axiom,(
% 3.78/0.92    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.78/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.78/0.92  fof(f100,plain,(
% 3.78/0.92    ( ! [X4,X0,X1] : (sP7(X4,X4,X1,X0)) )),
% 3.78/0.92    inference(equality_resolution,[],[f70])).
% 3.78/0.92  fof(f70,plain,(
% 3.78/0.92    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP7(X4,X2,X1,X0)) )),
% 3.78/0.92    inference(cnf_transformation,[],[f34])).
% 3.78/0.92  % SZS output end Proof for theBenchmark
% 3.78/0.92  % (15893)------------------------------
% 3.78/0.92  % (15893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.92  % (15893)Termination reason: Refutation
% 3.78/0.92  
% 3.78/0.92  % (15893)Memory used [KB]: 9210
% 3.78/0.92  % (15893)Time elapsed: 0.491 s
% 3.78/0.92  % (15893)------------------------------
% 3.78/0.92  % (15893)------------------------------
% 3.78/0.92  % (15868)Success in time 0.554 s
%------------------------------------------------------------------------------
