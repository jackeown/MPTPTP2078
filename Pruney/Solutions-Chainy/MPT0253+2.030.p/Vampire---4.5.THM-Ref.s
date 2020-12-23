%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:10 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 376 expanded)
%              Number of leaves         :   27 ( 124 expanded)
%              Depth                    :   21
%              Number of atoms          :  206 ( 579 expanded)
%              Number of equality atoms :   83 ( 295 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3255,f3257,f3428,f7344])).

fof(f7344,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f7342])).

fof(f7342,plain,
    ( $false
    | ~ spl5_9 ),
    inference(resolution,[],[f5656,f3239])).

fof(f3239,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f3238])).

fof(f3238,plain,
    ( spl5_9
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f5656,plain,(
    ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f5655])).

fof(f5655,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f5654,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f5654,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f5653,f4522])).

fof(f4522,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f115,f4299])).

fof(f4299,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f4269,f4121])).

fof(f4121,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f433,f801])).

fof(f801,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f781,f41])).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f781,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f762,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f762,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X16,k4_xboole_0(k1_xboole_0,X15))
      | ~ r1_xboole_0(X15,k1_xboole_0) ) ),
    inference(superposition,[],[f137,f117])).

fof(f117,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f70,f81])).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f137,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k4_xboole_0(X6,k4_xboole_0(X6,X5)))
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f75,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f50,f50])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f433,plain,(
    ! [X14] :
      ( ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14))
      | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X14) ) ),
    inference(superposition,[],[f422,f117])).

fof(f422,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f400,f42])).

fof(f400,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f70,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f4269,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f73,f4221])).

fof(f4221,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(forward_demodulation,[],[f4163,f42])).

fof(f4163,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = k5_xboole_0(X11,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1251,f4121])).

fof(f1251,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = k5_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) ),
    inference(superposition,[],[f135,f117])).

fof(f135,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f70,f73])).

fof(f115,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f70,f72])).

fof(f72,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f5653,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f5652,f105])).

fof(f105,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f56,f46])).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f5652,plain,
    ( sK1 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f5618,f46])).

fof(f5618,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(superposition,[],[f373,f133])).

fof(f133,plain,(
    ! [X6,X5] :
      ( k4_xboole_0(X6,k4_xboole_0(X6,X5)) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f73,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f373,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))) ),
    inference(forward_demodulation,[],[f372,f46])).

fof(f372,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))) ),
    inference(forward_demodulation,[],[f371,f73])).

fof(f371,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))) ),
    inference(superposition,[],[f71,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f69,f50])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f71,plain,(
    sK1 != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f40,f69,f68])).

fof(f40,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f3428,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f3427])).

fof(f3427,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f3254,f39])).

fof(f39,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3254,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f3252])).

fof(f3252,plain,
    ( spl5_12
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f3257,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f3256])).

fof(f3256,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f3250,f38])).

fof(f38,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3250,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f3248])).

fof(f3248,plain,
    ( spl5_11
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f3255,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_9 ),
    inference(avatar_split_clause,[],[f3246,f3238,f3252,f3248])).

fof(f3246,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK0,sK1)
    | spl5_9 ),
    inference(resolution,[],[f3240,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f3240,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f3238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (15172)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (15180)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (15183)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (15181)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (15173)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (15177)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (15168)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (15169)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (15179)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (15171)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (15170)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (15179)Refutation not found, incomplete strategy% (15179)------------------------------
% 0.20/0.49  % (15179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15179)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15179)Memory used [KB]: 10618
% 0.20/0.49  % (15179)Time elapsed: 0.088 s
% 0.20/0.49  % (15179)------------------------------
% 0.20/0.49  % (15179)------------------------------
% 0.20/0.49  % (15174)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (15175)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (15184)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (15178)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (15186)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (15185)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (15176)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.48/0.58  % (15172)Refutation found. Thanks to Tanya!
% 1.48/0.58  % SZS status Theorem for theBenchmark
% 1.48/0.58  % SZS output start Proof for theBenchmark
% 1.48/0.58  fof(f7345,plain,(
% 1.48/0.58    $false),
% 1.48/0.58    inference(avatar_sat_refutation,[],[f3255,f3257,f3428,f7344])).
% 1.48/0.58  fof(f7344,plain,(
% 1.48/0.58    ~spl5_9),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f7342])).
% 1.48/0.58  fof(f7342,plain,(
% 1.48/0.58    $false | ~spl5_9),
% 1.48/0.58    inference(resolution,[],[f5656,f3239])).
% 1.48/0.58  fof(f3239,plain,(
% 1.48/0.58    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_9),
% 1.48/0.58    inference(avatar_component_clause,[],[f3238])).
% 1.48/0.58  fof(f3238,plain,(
% 1.48/0.58    spl5_9 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.48/0.58  fof(f5656,plain,(
% 1.48/0.58    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.48/0.58    inference(trivial_inequality_removal,[],[f5655])).
% 1.48/0.58  fof(f5655,plain,(
% 1.48/0.58    sK1 != sK1 | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.48/0.58    inference(forward_demodulation,[],[f5654,f42])).
% 1.48/0.58  fof(f42,plain,(
% 1.48/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f9])).
% 1.48/0.58  fof(f9,axiom,(
% 1.48/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.48/0.58  fof(f5654,plain,(
% 1.48/0.58    sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.48/0.58    inference(forward_demodulation,[],[f5653,f4522])).
% 1.48/0.58  fof(f4522,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.48/0.58    inference(backward_demodulation,[],[f115,f4299])).
% 1.48/0.58  fof(f4299,plain,(
% 1.48/0.58    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.48/0.58    inference(forward_demodulation,[],[f4269,f4121])).
% 1.48/0.58  fof(f4121,plain,(
% 1.48/0.58    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.48/0.58    inference(resolution,[],[f433,f801])).
% 1.48/0.58  fof(f801,plain,(
% 1.48/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.48/0.58    inference(resolution,[],[f781,f41])).
% 1.48/0.58  fof(f41,plain,(
% 1.48/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f10])).
% 1.48/0.58  fof(f10,axiom,(
% 1.48/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.48/0.58  fof(f781,plain,(
% 1.48/0.58    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 1.48/0.58    inference(resolution,[],[f762,f76])).
% 1.48/0.58  fof(f76,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f52,f50])).
% 1.48/0.58  fof(f50,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f8])).
% 1.48/0.58  fof(f8,axiom,(
% 1.48/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.48/0.58  fof(f52,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f35])).
% 1.48/0.58  fof(f35,plain,(
% 1.48/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f34])).
% 1.48/0.58  fof(f34,plain,(
% 1.48/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f28,plain,(
% 1.48/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.48/0.58    inference(ennf_transformation,[],[f24])).
% 1.48/0.58  fof(f24,plain,(
% 1.48/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.58    inference(rectify,[],[f4])).
% 1.48/0.58  fof(f4,axiom,(
% 1.48/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.48/0.58  fof(f762,plain,(
% 1.48/0.58    ( ! [X15,X16] : (~r2_hidden(X16,k4_xboole_0(k1_xboole_0,X15)) | ~r1_xboole_0(X15,k1_xboole_0)) )),
% 1.48/0.58    inference(superposition,[],[f137,f117])).
% 1.48/0.58  fof(f117,plain,(
% 1.48/0.58    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 1.48/0.58    inference(superposition,[],[f70,f81])).
% 1.48/0.58  fof(f81,plain,(
% 1.48/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.48/0.58    inference(superposition,[],[f46,f42])).
% 1.48/0.58  fof(f46,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f2])).
% 1.48/0.58  fof(f2,axiom,(
% 1.48/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.48/0.58  fof(f70,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.48/0.58    inference(definition_unfolding,[],[f49,f50])).
% 1.48/0.58  fof(f49,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f6])).
% 1.48/0.58  fof(f6,axiom,(
% 1.48/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.58  fof(f137,plain,(
% 1.48/0.58    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(X6,k4_xboole_0(X6,X5))) | ~r1_xboole_0(X5,X6)) )),
% 1.48/0.58    inference(superposition,[],[f75,f73])).
% 1.48/0.58  fof(f73,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.48/0.58    inference(definition_unfolding,[],[f45,f50,f50])).
% 1.48/0.58  fof(f45,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f1])).
% 1.48/0.58  fof(f1,axiom,(
% 1.48/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.48/0.58  fof(f75,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f53,f50])).
% 1.48/0.58  fof(f53,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f35])).
% 1.48/0.58  fof(f433,plain,(
% 1.48/0.58    ( ! [X14] : (~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X14)) )),
% 1.48/0.58    inference(superposition,[],[f422,f117])).
% 1.48/0.58  fof(f422,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(forward_demodulation,[],[f400,f42])).
% 1.48/0.58  fof(f400,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(superposition,[],[f70,f89])).
% 1.48/0.58  fof(f89,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(resolution,[],[f75,f43])).
% 1.48/0.58  fof(f43,plain,(
% 1.48/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f33])).
% 1.48/0.58  fof(f33,plain,(
% 1.48/0.58    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f32])).
% 1.48/0.58  fof(f32,plain,(
% 1.48/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f27,plain,(
% 1.48/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.48/0.58    inference(ennf_transformation,[],[f5])).
% 1.48/0.58  fof(f5,axiom,(
% 1.48/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.48/0.58  fof(f4269,plain,(
% 1.48/0.58    ( ! [X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 1.48/0.58    inference(superposition,[],[f73,f4221])).
% 1.48/0.58  fof(f4221,plain,(
% 1.48/0.58    ( ! [X11] : (k4_xboole_0(X11,k1_xboole_0) = X11) )),
% 1.48/0.58    inference(forward_demodulation,[],[f4163,f42])).
% 1.48/0.58  fof(f4163,plain,(
% 1.48/0.58    ( ! [X11] : (k4_xboole_0(X11,k1_xboole_0) = k5_xboole_0(X11,k1_xboole_0)) )),
% 1.48/0.58    inference(backward_demodulation,[],[f1251,f4121])).
% 1.48/0.58  fof(f1251,plain,(
% 1.48/0.58    ( ! [X11] : (k4_xboole_0(X11,k1_xboole_0) = k5_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))) )),
% 1.48/0.58    inference(superposition,[],[f135,f117])).
% 1.48/0.58  fof(f135,plain,(
% 1.48/0.58    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 1.48/0.58    inference(superposition,[],[f70,f73])).
% 1.48/0.58  fof(f115,plain,(
% 1.48/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.48/0.58    inference(superposition,[],[f70,f72])).
% 1.48/0.58  fof(f72,plain,(
% 1.48/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.48/0.58    inference(definition_unfolding,[],[f44,f50])).
% 1.48/0.58  fof(f44,plain,(
% 1.48/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f23])).
% 1.48/0.58  fof(f23,plain,(
% 1.48/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.48/0.58    inference(rectify,[],[f3])).
% 1.48/0.58  fof(f3,axiom,(
% 1.48/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.48/0.58  fof(f5653,plain,(
% 1.48/0.58    sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.48/0.58    inference(forward_demodulation,[],[f5652,f105])).
% 1.48/0.58  fof(f105,plain,(
% 1.48/0.58    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 1.48/0.58    inference(superposition,[],[f56,f46])).
% 1.48/0.58  fof(f56,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f11])).
% 1.48/0.58  fof(f11,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.48/0.58  fof(f5652,plain,(
% 1.48/0.58    sK1 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.48/0.58    inference(forward_demodulation,[],[f5618,f46])).
% 1.48/0.58  fof(f5618,plain,(
% 1.48/0.58    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.48/0.58    inference(superposition,[],[f373,f133])).
% 1.48/0.58  fof(f133,plain,(
% 1.48/0.58    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,X5)) = X5 | ~r1_tarski(X5,X6)) )),
% 1.48/0.58    inference(superposition,[],[f73,f77])).
% 1.48/0.58  fof(f77,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f54,f50])).
% 1.48/0.58  fof(f54,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f29])).
% 1.48/0.58  fof(f29,plain,(
% 1.48/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.48/0.58    inference(ennf_transformation,[],[f7])).
% 1.48/0.58  fof(f7,axiom,(
% 1.48/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.48/0.58  fof(f373,plain,(
% 1.48/0.58    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))),
% 1.48/0.58    inference(forward_demodulation,[],[f372,f46])).
% 1.48/0.58  fof(f372,plain,(
% 1.48/0.58    sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))),
% 1.48/0.58    inference(forward_demodulation,[],[f371,f73])).
% 1.48/0.58  fof(f371,plain,(
% 1.48/0.58    sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)))),
% 1.48/0.58    inference(superposition,[],[f71,f74])).
% 1.48/0.58  fof(f74,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.48/0.58    inference(definition_unfolding,[],[f51,f69,f50])).
% 1.48/0.58  fof(f69,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.58    inference(definition_unfolding,[],[f47,f68])).
% 1.48/0.58  fof(f68,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f48,f67])).
% 1.48/0.58  fof(f67,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f55,f66])).
% 1.48/0.58  fof(f66,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f60,f65])).
% 1.48/0.58  fof(f65,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f61,f64])).
% 1.48/0.58  fof(f64,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f62,f63])).
% 1.48/0.58  fof(f63,plain,(
% 1.48/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f18])).
% 1.48/0.58  fof(f18,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.48/0.58  fof(f62,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f17])).
% 1.48/0.58  fof(f17,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.48/0.58  fof(f61,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f16])).
% 1.48/0.58  fof(f16,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.48/0.58  fof(f60,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f15])).
% 1.48/0.58  fof(f15,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.58  fof(f55,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f14])).
% 1.48/0.58  fof(f14,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.58  fof(f48,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f13])).
% 1.48/0.58  fof(f13,axiom,(
% 1.48/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.58  fof(f47,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f19])).
% 1.48/0.58  fof(f19,axiom,(
% 1.48/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.48/0.58  fof(f51,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f12])).
% 1.48/0.58  fof(f12,axiom,(
% 1.48/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.48/0.58  fof(f71,plain,(
% 1.48/0.58    sK1 != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))),
% 1.48/0.58    inference(definition_unfolding,[],[f40,f69,f68])).
% 1.48/0.58  fof(f40,plain,(
% 1.48/0.58    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f31])).
% 1.48/0.58  fof(f31,plain,(
% 1.48/0.58    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).
% 1.48/0.58  fof(f30,plain,(
% 1.48/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f26,plain,(
% 1.48/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.48/0.58    inference(flattening,[],[f25])).
% 1.48/0.58  fof(f25,plain,(
% 1.48/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.48/0.58    inference(ennf_transformation,[],[f22])).
% 1.48/0.58  fof(f22,negated_conjecture,(
% 1.48/0.58    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.48/0.58    inference(negated_conjecture,[],[f21])).
% 1.48/0.58  fof(f21,conjecture,(
% 1.48/0.58    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.48/0.58  fof(f3428,plain,(
% 1.48/0.58    spl5_12),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f3427])).
% 1.48/0.58  fof(f3427,plain,(
% 1.48/0.58    $false | spl5_12),
% 1.48/0.58    inference(resolution,[],[f3254,f39])).
% 1.48/0.58  fof(f39,plain,(
% 1.48/0.58    r2_hidden(sK2,sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f31])).
% 1.48/0.58  fof(f3254,plain,(
% 1.48/0.58    ~r2_hidden(sK2,sK1) | spl5_12),
% 1.48/0.58    inference(avatar_component_clause,[],[f3252])).
% 1.48/0.58  fof(f3252,plain,(
% 1.48/0.58    spl5_12 <=> r2_hidden(sK2,sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.48/0.58  fof(f3257,plain,(
% 1.48/0.58    spl5_11),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f3256])).
% 1.48/0.58  fof(f3256,plain,(
% 1.48/0.58    $false | spl5_11),
% 1.48/0.58    inference(resolution,[],[f3250,f38])).
% 1.48/0.58  fof(f38,plain,(
% 1.48/0.58    r2_hidden(sK0,sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f31])).
% 1.48/0.58  fof(f3250,plain,(
% 1.48/0.58    ~r2_hidden(sK0,sK1) | spl5_11),
% 1.48/0.58    inference(avatar_component_clause,[],[f3248])).
% 1.48/0.58  fof(f3248,plain,(
% 1.48/0.58    spl5_11 <=> r2_hidden(sK0,sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.48/0.58  fof(f3255,plain,(
% 1.48/0.58    ~spl5_11 | ~spl5_12 | spl5_9),
% 1.48/0.58    inference(avatar_split_clause,[],[f3246,f3238,f3252,f3248])).
% 1.48/0.58  fof(f3246,plain,(
% 1.48/0.58    ~r2_hidden(sK2,sK1) | ~r2_hidden(sK0,sK1) | spl5_9),
% 1.48/0.58    inference(resolution,[],[f3240,f78])).
% 1.48/0.58  fof(f78,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f59,f68])).
% 1.48/0.58  fof(f59,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f37])).
% 1.48/0.58  fof(f37,plain,(
% 1.48/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.48/0.58    inference(flattening,[],[f36])).
% 1.48/0.58  fof(f36,plain,(
% 1.48/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.48/0.58    inference(nnf_transformation,[],[f20])).
% 1.48/0.58  fof(f20,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.48/0.58  fof(f3240,plain,(
% 1.48/0.58    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) | spl5_9),
% 1.48/0.58    inference(avatar_component_clause,[],[f3238])).
% 1.48/0.58  % SZS output end Proof for theBenchmark
% 1.48/0.58  % (15172)------------------------------
% 1.48/0.58  % (15172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (15172)Termination reason: Refutation
% 1.48/0.58  
% 1.48/0.58  % (15172)Memory used [KB]: 11257
% 1.48/0.58  % (15172)Time elapsed: 0.128 s
% 1.48/0.58  % (15172)------------------------------
% 1.48/0.58  % (15172)------------------------------
% 1.48/0.58  % (15164)Success in time 0.224 s
%------------------------------------------------------------------------------
