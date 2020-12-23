%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:58 EST 2020

% Result     : Theorem 4.46s
% Output     : Refutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 172 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  264 ( 367 expanded)
%              Number of equality atoms :  174 ( 240 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3814,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3813])).

fof(f3813,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f49,f3795])).

fof(f3795,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f3634,f106])).

fof(f106,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f31])).

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

fof(f3634,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK0))
      | sK1 = X3 ) ),
    inference(superposition,[],[f104,f3402])).

fof(f3402,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0) ),
    inference(superposition,[],[f3288,f79])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3288,plain,(
    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = k2_enumset1(sK1,sK1,sK1,sK0) ),
    inference(backward_demodulation,[],[f249,f2856])).

fof(f2856,plain,(
    ! [X13] : k1_xboole_0 = k5_xboole_0(X13,X13) ),
    inference(forward_demodulation,[],[f2855,f174])).

fof(f174,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X4,X4),X4) ),
    inference(resolution,[],[f122,f116])).

fof(f116,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f101,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f101,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f77,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f58,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f2855,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),X13) ),
    inference(forward_demodulation,[],[f2854,f79])).

fof(f2854,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(X13,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2853,f167])).

fof(f167,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f157,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f157,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X2),X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f78,f133])).

fof(f133,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f91,f62])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f64,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f64,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f2853,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X13,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f2836,f78])).

fof(f2836,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(X13,k1_xboole_0))) ),
    inference(superposition,[],[f189,f174])).

fof(f189,plain,(
    ! [X2,X1] : k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2 ),
    inference(superposition,[],[f90,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f60,f81])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f249,plain,(
    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) = k2_enumset1(sK1,sK1,sK1,sK0) ),
    inference(superposition,[],[f84,f120])).

fof(f120,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f50,f85])).

fof(f85,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f48,f83,f83])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f73])).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f51,f81,f73,f83])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f104,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f49,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:24:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (25776)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (25760)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (25768)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (25763)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (25758)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (25754)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (25753)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (25754)Refutation not found, incomplete strategy% (25754)------------------------------
% 0.22/0.53  % (25754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25754)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25754)Memory used [KB]: 1663
% 0.22/0.53  % (25754)Time elapsed: 0.123 s
% 0.22/0.53  % (25754)------------------------------
% 0.22/0.53  % (25754)------------------------------
% 0.22/0.54  % (25757)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (25755)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (25756)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (25777)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (25781)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (25782)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (25782)Refutation not found, incomplete strategy% (25782)------------------------------
% 0.22/0.54  % (25782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25782)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25782)Memory used [KB]: 1663
% 0.22/0.54  % (25782)Time elapsed: 0.139 s
% 0.22/0.54  % (25782)------------------------------
% 0.22/0.54  % (25782)------------------------------
% 0.22/0.55  % (25764)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (25770)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (25769)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (25773)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (25769)Refutation not found, incomplete strategy% (25769)------------------------------
% 0.22/0.55  % (25769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25769)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (25769)Memory used [KB]: 10618
% 0.22/0.55  % (25769)Time elapsed: 0.138 s
% 0.22/0.55  % (25769)------------------------------
% 0.22/0.55  % (25769)------------------------------
% 0.22/0.55  % (25774)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (25761)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (25762)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (25779)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (25759)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (25780)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (25765)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (25771)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (25766)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (25772)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (25778)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (25775)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % (25767)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.59  % (25767)Refutation not found, incomplete strategy% (25767)------------------------------
% 0.22/0.59  % (25767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (25767)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (25767)Memory used [KB]: 1791
% 0.22/0.59  % (25767)Time elapsed: 0.161 s
% 0.22/0.59  % (25767)------------------------------
% 0.22/0.59  % (25767)------------------------------
% 2.21/0.69  % (25804)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.21/0.70  % (25756)Refutation not found, incomplete strategy% (25756)------------------------------
% 2.21/0.70  % (25756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.70  % (25756)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.70  
% 2.21/0.70  % (25756)Memory used [KB]: 6140
% 2.21/0.70  % (25756)Time elapsed: 0.287 s
% 2.21/0.70  % (25756)------------------------------
% 2.21/0.70  % (25756)------------------------------
% 2.21/0.71  % (25805)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.69/0.73  % (25806)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.69/0.75  % (25807)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.05/0.76  % (25806)Refutation not found, incomplete strategy% (25806)------------------------------
% 3.05/0.76  % (25806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.76  % (25806)Termination reason: Refutation not found, incomplete strategy
% 3.05/0.76  
% 3.05/0.76  % (25806)Memory used [KB]: 6268
% 3.05/0.76  % (25806)Time elapsed: 0.161 s
% 3.05/0.76  % (25806)------------------------------
% 3.05/0.76  % (25806)------------------------------
% 3.05/0.81  % (25777)Time limit reached!
% 3.05/0.81  % (25777)------------------------------
% 3.05/0.81  % (25777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.81  % (25777)Termination reason: Time limit
% 3.05/0.81  
% 3.05/0.81  % (25777)Memory used [KB]: 13176
% 3.05/0.81  % (25777)Time elapsed: 0.408 s
% 3.05/0.81  % (25777)------------------------------
% 3.05/0.81  % (25777)------------------------------
% 3.05/0.82  % (25755)Time limit reached!
% 3.05/0.82  % (25755)------------------------------
% 3.05/0.82  % (25755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.82  % (25755)Termination reason: Time limit
% 3.05/0.82  
% 3.05/0.82  % (25755)Memory used [KB]: 6652
% 3.05/0.82  % (25755)Time elapsed: 0.407 s
% 3.05/0.82  % (25755)------------------------------
% 3.05/0.82  % (25755)------------------------------
% 3.72/0.85  % (25808)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.03/0.89  % (25809)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.03/0.93  % (25759)Time limit reached!
% 4.03/0.93  % (25759)------------------------------
% 4.03/0.93  % (25759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.93  % (25759)Termination reason: Time limit
% 4.03/0.93  % (25759)Termination phase: Saturation
% 4.03/0.93  
% 4.03/0.93  % (25759)Memory used [KB]: 16375
% 4.03/0.93  % (25759)Time elapsed: 0.500 s
% 4.03/0.93  % (25759)------------------------------
% 4.03/0.93  % (25759)------------------------------
% 4.46/0.95  % (25810)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.46/0.95  % (25811)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.46/0.96  % (25758)Refutation found. Thanks to Tanya!
% 4.46/0.96  % SZS status Theorem for theBenchmark
% 4.46/0.98  % SZS output start Proof for theBenchmark
% 4.46/0.98  fof(f3814,plain,(
% 4.46/0.98    $false),
% 4.46/0.98    inference(trivial_inequality_removal,[],[f3813])).
% 4.46/0.98  fof(f3813,plain,(
% 4.46/0.98    sK0 != sK0),
% 4.46/0.98    inference(superposition,[],[f49,f3795])).
% 4.46/0.98  fof(f3795,plain,(
% 4.46/0.98    sK0 = sK1),
% 4.46/0.98    inference(resolution,[],[f3634,f106])).
% 4.46/0.98  fof(f106,plain,(
% 4.46/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 4.46/0.98    inference(equality_resolution,[],[f105])).
% 4.46/0.98  fof(f105,plain,(
% 4.46/0.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 4.46/0.98    inference(equality_resolution,[],[f96])).
% 4.46/0.98  fof(f96,plain,(
% 4.46/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 4.46/0.98    inference(definition_unfolding,[],[f68,f73])).
% 4.46/0.98  fof(f73,plain,(
% 4.46/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.46/0.98    inference(cnf_transformation,[],[f18])).
% 4.46/0.98  fof(f18,axiom,(
% 4.46/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.46/0.98  fof(f68,plain,(
% 4.46/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.46/0.98    inference(cnf_transformation,[],[f45])).
% 4.46/0.98  fof(f45,plain,(
% 4.46/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 4.46/0.98  fof(f44,plain,(
% 4.46/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 4.46/0.98    introduced(choice_axiom,[])).
% 4.46/0.98  fof(f43,plain,(
% 4.46/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.46/0.98    inference(rectify,[],[f42])).
% 4.46/0.98  fof(f42,plain,(
% 4.46/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.46/0.98    inference(flattening,[],[f41])).
% 4.46/0.98  fof(f41,plain,(
% 4.46/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.46/0.98    inference(nnf_transformation,[],[f31])).
% 4.46/0.98  fof(f31,plain,(
% 4.46/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.46/0.98    inference(ennf_transformation,[],[f13])).
% 4.46/0.98  fof(f13,axiom,(
% 4.46/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 4.46/0.98  fof(f3634,plain,(
% 4.46/0.98    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK0)) | sK1 = X3) )),
% 4.46/0.98    inference(superposition,[],[f104,f3402])).
% 4.46/0.98  fof(f3402,plain,(
% 4.46/0.98    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0)),
% 4.46/0.98    inference(superposition,[],[f3288,f79])).
% 4.46/0.98  fof(f79,plain,(
% 4.46/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.46/0.98    inference(cnf_transformation,[],[f9])).
% 4.46/0.98  fof(f9,axiom,(
% 4.46/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 4.46/0.98  fof(f3288,plain,(
% 4.46/0.98    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = k2_enumset1(sK1,sK1,sK1,sK0)),
% 4.46/0.98    inference(backward_demodulation,[],[f249,f2856])).
% 4.46/0.98  fof(f2856,plain,(
% 4.46/0.98    ( ! [X13] : (k1_xboole_0 = k5_xboole_0(X13,X13)) )),
% 4.46/0.98    inference(forward_demodulation,[],[f2855,f174])).
% 4.46/0.98  fof(f174,plain,(
% 4.46/0.98    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X4,X4),X4)) )),
% 4.46/0.98    inference(resolution,[],[f122,f116])).
% 4.46/0.98  fof(f116,plain,(
% 4.46/0.98    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 4.46/0.98    inference(superposition,[],[f101,f62])).
% 4.46/0.98  fof(f62,plain,(
% 4.46/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.46/0.98    inference(cnf_transformation,[],[f26])).
% 4.46/0.98  fof(f26,plain,(
% 4.46/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.46/0.98    inference(rectify,[],[f3])).
% 4.46/0.98  fof(f3,axiom,(
% 4.46/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.46/0.98  fof(f101,plain,(
% 4.46/0.98    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 4.46/0.98    inference(definition_unfolding,[],[f77,f59])).
% 4.46/0.98  fof(f59,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.46/0.98    inference(cnf_transformation,[],[f6])).
% 4.46/0.98  fof(f6,axiom,(
% 4.46/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.46/0.98  fof(f77,plain,(
% 4.46/0.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.46/0.98    inference(cnf_transformation,[],[f10])).
% 4.46/0.98  fof(f10,axiom,(
% 4.46/0.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 4.46/0.98  fof(f122,plain,(
% 4.46/0.98    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 4.46/0.98    inference(resolution,[],[f58,f76])).
% 4.46/0.98  fof(f76,plain,(
% 4.46/0.98    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 4.46/0.98    inference(cnf_transformation,[],[f47])).
% 4.46/0.98  fof(f47,plain,(
% 4.46/0.98    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 4.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f46])).
% 4.46/0.98  fof(f46,plain,(
% 4.46/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 4.46/0.98    introduced(choice_axiom,[])).
% 4.46/0.98  fof(f32,plain,(
% 4.46/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.46/0.98    inference(ennf_transformation,[],[f5])).
% 4.46/0.98  fof(f5,axiom,(
% 4.46/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 4.46/0.98  fof(f58,plain,(
% 4.46/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.46/0.98    inference(cnf_transformation,[],[f40])).
% 4.46/0.98  fof(f40,plain,(
% 4.46/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f39])).
% 4.46/0.98  fof(f39,plain,(
% 4.46/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 4.46/0.98    introduced(choice_axiom,[])).
% 4.46/0.98  fof(f30,plain,(
% 4.46/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.46/0.98    inference(ennf_transformation,[],[f25])).
% 4.46/0.98  fof(f25,plain,(
% 4.46/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.46/0.98    inference(rectify,[],[f4])).
% 4.46/0.98  fof(f4,axiom,(
% 4.46/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 4.46/0.98  fof(f2855,plain,(
% 4.46/0.98    ( ! [X13] : (k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),X13)) )),
% 4.46/0.98    inference(forward_demodulation,[],[f2854,f79])).
% 4.46/0.98  fof(f2854,plain,(
% 4.46/0.98    ( ! [X13] : (k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(X13,k1_xboole_0))) )),
% 4.46/0.98    inference(forward_demodulation,[],[f2853,f167])).
% 4.46/0.98  fof(f167,plain,(
% 4.46/0.98    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X3)))) )),
% 4.46/0.98    inference(forward_demodulation,[],[f157,f78])).
% 4.46/0.98  fof(f78,plain,(
% 4.46/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.46/0.98    inference(cnf_transformation,[],[f11])).
% 4.46/0.98  fof(f11,axiom,(
% 4.46/0.98    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.46/0.98  fof(f157,plain,(
% 4.46/0.98    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X2),X3)) = k5_xboole_0(X2,X3)) )),
% 4.46/0.98    inference(superposition,[],[f78,f133])).
% 4.46/0.98  fof(f133,plain,(
% 4.46/0.98    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 4.46/0.98    inference(forward_demodulation,[],[f91,f62])).
% 4.46/0.98  fof(f91,plain,(
% 4.46/0.98    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 4.46/0.98    inference(definition_unfolding,[],[f64,f81])).
% 4.46/0.98  fof(f81,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.46/0.98    inference(definition_unfolding,[],[f63,f59])).
% 4.46/0.98  fof(f63,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.46/0.98    inference(cnf_transformation,[],[f12])).
% 4.46/0.98  fof(f12,axiom,(
% 4.46/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.46/0.98  fof(f64,plain,(
% 4.46/0.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.46/0.98    inference(cnf_transformation,[],[f27])).
% 4.46/0.98  fof(f27,plain,(
% 4.46/0.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.46/0.98    inference(rectify,[],[f2])).
% 4.46/0.98  fof(f2,axiom,(
% 4.46/0.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.46/0.98  fof(f2853,plain,(
% 4.46/0.98    ( ! [X13] : (k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X13,k1_xboole_0))))) )),
% 4.46/0.98    inference(forward_demodulation,[],[f2836,f78])).
% 4.46/0.98  fof(f2836,plain,(
% 4.46/0.98    ( ! [X13] : (k5_xboole_0(X13,X13) = k3_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(k5_xboole_0(X13,X13),k5_xboole_0(X13,k1_xboole_0)))) )),
% 4.46/0.98    inference(superposition,[],[f189,f174])).
% 4.46/0.98  fof(f189,plain,(
% 4.46/0.98    ( ! [X2,X1] : (k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2) )),
% 4.46/0.98    inference(superposition,[],[f90,f61])).
% 4.46/0.98  fof(f61,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.46/0.98    inference(cnf_transformation,[],[f1])).
% 4.46/0.98  fof(f1,axiom,(
% 4.46/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.46/0.98  fof(f90,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 4.46/0.98    inference(definition_unfolding,[],[f60,f81])).
% 4.46/0.98  fof(f60,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 4.46/0.98    inference(cnf_transformation,[],[f7])).
% 4.46/0.98  fof(f7,axiom,(
% 4.46/0.98    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 4.46/0.98  fof(f249,plain,(
% 4.46/0.98    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) = k2_enumset1(sK1,sK1,sK1,sK0)),
% 4.46/0.98    inference(superposition,[],[f84,f120])).
% 4.46/0.98  fof(f120,plain,(
% 4.46/0.98    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 4.46/0.98    inference(resolution,[],[f50,f85])).
% 4.46/0.98  fof(f85,plain,(
% 4.46/0.98    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 4.46/0.98    inference(definition_unfolding,[],[f48,f83,f83])).
% 4.46/0.98  fof(f83,plain,(
% 4.46/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.46/0.98    inference(definition_unfolding,[],[f56,f82])).
% 4.46/0.98  fof(f82,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.46/0.98    inference(definition_unfolding,[],[f74,f73])).
% 4.46/0.98  fof(f74,plain,(
% 4.46/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.46/0.98    inference(cnf_transformation,[],[f17])).
% 4.46/0.98  fof(f17,axiom,(
% 4.46/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.46/0.98  fof(f56,plain,(
% 4.46/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.46/0.98    inference(cnf_transformation,[],[f16])).
% 4.46/0.98  fof(f16,axiom,(
% 4.46/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.46/0.98  fof(f48,plain,(
% 4.46/0.98    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 4.46/0.98    inference(cnf_transformation,[],[f34])).
% 4.46/0.98  fof(f34,plain,(
% 4.46/0.98    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 4.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f33])).
% 4.46/0.98  fof(f33,plain,(
% 4.46/0.98    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 4.46/0.98    introduced(choice_axiom,[])).
% 4.46/0.98  fof(f28,plain,(
% 4.46/0.98    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 4.46/0.98    inference(ennf_transformation,[],[f24])).
% 4.46/0.98  fof(f24,negated_conjecture,(
% 4.46/0.98    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 4.46/0.98    inference(negated_conjecture,[],[f23])).
% 4.46/0.98  fof(f23,conjecture,(
% 4.46/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 4.46/0.98  fof(f50,plain,(
% 4.46/0.98    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 4.46/0.98    inference(cnf_transformation,[],[f29])).
% 4.46/0.98  fof(f29,plain,(
% 4.46/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.46/0.98    inference(ennf_transformation,[],[f8])).
% 4.46/0.98  fof(f8,axiom,(
% 4.46/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.46/0.98  fof(f84,plain,(
% 4.46/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))))) )),
% 4.46/0.98    inference(definition_unfolding,[],[f51,f81,f73,f83])).
% 4.46/0.98  fof(f51,plain,(
% 4.46/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 4.46/0.98    inference(cnf_transformation,[],[f15])).
% 4.46/0.98  fof(f15,axiom,(
% 4.46/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 4.46/0.98  fof(f104,plain,(
% 4.46/0.98    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 4.46/0.98    inference(equality_resolution,[],[f89])).
% 4.46/0.98  fof(f89,plain,(
% 4.46/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 4.46/0.98    inference(definition_unfolding,[],[f52,f83])).
% 4.46/0.98  fof(f52,plain,(
% 4.46/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.46/0.98    inference(cnf_transformation,[],[f38])).
% 4.46/0.98  fof(f38,plain,(
% 4.46/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 4.46/0.98  fof(f37,plain,(
% 4.46/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 4.46/0.98    introduced(choice_axiom,[])).
% 4.46/0.98  fof(f36,plain,(
% 4.46/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.46/0.98    inference(rectify,[],[f35])).
% 4.46/0.98  fof(f35,plain,(
% 4.46/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.46/0.98    inference(nnf_transformation,[],[f14])).
% 4.46/0.98  fof(f14,axiom,(
% 4.46/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 4.46/0.98  fof(f49,plain,(
% 4.46/0.98    sK0 != sK1),
% 4.46/0.98    inference(cnf_transformation,[],[f34])).
% 4.46/0.98  % SZS output end Proof for theBenchmark
% 4.46/0.98  % (25758)------------------------------
% 4.46/0.98  % (25758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.98  % (25758)Termination reason: Refutation
% 4.46/0.98  
% 4.46/0.98  % (25758)Memory used [KB]: 3965
% 4.46/0.98  % (25758)Time elapsed: 0.539 s
% 4.46/0.98  % (25758)------------------------------
% 4.46/0.98  % (25758)------------------------------
% 4.46/0.98  % (25752)Success in time 0.613 s
%------------------------------------------------------------------------------
