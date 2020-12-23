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
% DateTime   : Thu Dec  3 12:41:24 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 548 expanded)
%              Number of leaves         :   16 ( 168 expanded)
%              Depth                    :   20
%              Number of atoms          :  181 ( 857 expanded)
%              Number of equality atoms :   64 ( 534 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1505,plain,(
    $false ),
    inference(global_subsumption,[],[f1079,f1100,f1504])).

fof(f1504,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f1503])).

fof(f1503,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f551,f1496])).

fof(f1496,plain,(
    ! [X0] : k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(X0,X0,X0,X0,X0,sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1189,f1447,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f65,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f1447,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(sK2,k5_enumset1(X0,X0,X0,X0,X0,sK0,X1))) ),
    inference(forward_demodulation,[],[f1430,f37])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1430,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,sK0,X1),sK2)) ),
    inference(unit_resulting_resolution,[],[f1100,f797,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
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

fof(f797,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
    inference(unit_resulting_resolution,[],[f78,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0] : sP5(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1189,plain,(
    ! [X0,X1] : r2_hidden(sK1,k5_xboole_0(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,sK1))) ),
    inference(forward_demodulation,[],[f1175,f37])).

fof(f1175,plain,(
    ! [X0,X1] : r2_hidden(sK1,k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f1079,f796,f50])).

fof(f796,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f77,f76])).

fof(f77,plain,(
    ! [X4,X0,X1] : sP5(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f551,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f546,f37])).

fof(f546,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f80,f539])).

fof(f539,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f513,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f513,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f45,f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f80,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f68,f36])).

fof(f68,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f29,f65,f39,f65])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f1100,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f1097])).

fof(f1097,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f1095,f78])).

fof(f1095,plain,(
    ! [X2] :
      ( ~ sP5(X2,sK1,sK0,sK0)
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f1089,f76])).

fof(f1089,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(resolution,[],[f1054,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
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
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f1054,plain,
    ( r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f594,f550])).

fof(f550,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f545,f37])).

fof(f545,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f81,f539])).

fof(f81,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f67,f36])).

fof(f67,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f30,f65,f39,f65])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f594,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X2) ),
    inference(superposition,[],[f543,f37])).

fof(f543,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),X2) ),
    inference(backward_demodulation,[],[f92,f539])).

fof(f92,plain,(
    ! [X2,X1] : r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(superposition,[],[f69,f36])).

fof(f69,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1079,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f1076])).

fof(f1076,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f1052,f77])).

fof(f1052,plain,(
    ! [X2] :
      ( ~ sP5(X2,sK1,sK0,sK0)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f1048,f76])).

fof(f1048,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(sK1,sK2) ) ),
    inference(resolution,[],[f1026,f40])).

fof(f1026,plain,
    ( r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f594,f549])).

fof(f549,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f544,f37])).

fof(f544,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f82,f539])).

fof(f82,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f66,f36])).

fof(f66,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f65,f39,f65])).

fof(f31,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:16:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (27484)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.48  % (27469)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (27462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (27460)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (27460)Refutation not found, incomplete strategy% (27460)------------------------------
% 0.22/0.52  % (27460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27465)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (27466)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (27461)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (27483)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (27480)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (27463)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (27470)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (27477)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (27472)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (27459)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (27479)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (27458)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (27467)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (27475)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (27468)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (27474)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (27486)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (27476)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (27485)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (27464)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (27460)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27460)Memory used [KB]: 10746
% 0.22/0.54  % (27460)Time elapsed: 0.107 s
% 0.22/0.54  % (27460)------------------------------
% 0.22/0.54  % (27460)------------------------------
% 0.22/0.54  % (27481)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (27466)Refutation not found, incomplete strategy% (27466)------------------------------
% 0.22/0.54  % (27466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27466)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27466)Memory used [KB]: 10618
% 0.22/0.54  % (27466)Time elapsed: 0.133 s
% 0.22/0.54  % (27466)------------------------------
% 0.22/0.54  % (27466)------------------------------
% 0.22/0.54  % (27487)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (27482)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (27478)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (27475)Refutation not found, incomplete strategy% (27475)------------------------------
% 0.22/0.55  % (27475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27475)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27475)Memory used [KB]: 10746
% 0.22/0.55  % (27475)Time elapsed: 0.128 s
% 0.22/0.55  % (27475)------------------------------
% 0.22/0.55  % (27475)------------------------------
% 0.22/0.55  % (27473)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (27471)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.18/0.66  % (27545)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.18/0.66  % (27547)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.18/0.67  % (27482)Refutation found. Thanks to Tanya!
% 2.18/0.67  % SZS status Theorem for theBenchmark
% 2.18/0.67  % SZS output start Proof for theBenchmark
% 2.18/0.67  fof(f1505,plain,(
% 2.18/0.67    $false),
% 2.18/0.67    inference(global_subsumption,[],[f1079,f1100,f1504])).
% 2.18/0.67  fof(f1504,plain,(
% 2.18/0.67    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 2.18/0.67    inference(trivial_inequality_removal,[],[f1503])).
% 2.18/0.67  fof(f1503,plain,(
% 2.18/0.67    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 2.18/0.67    inference(backward_demodulation,[],[f551,f1496])).
% 2.18/0.67  fof(f1496,plain,(
% 2.18/0.67    ( ! [X0] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(X0,X0,X0,X0,X0,sK0,sK1)))) )),
% 2.18/0.67    inference(unit_resulting_resolution,[],[f1189,f1447,f70])).
% 2.18/0.67  fof(f70,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f46,f65,f65])).
% 2.18/0.67  fof(f65,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f38,f64])).
% 2.18/0.67  fof(f64,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f43,f63])).
% 2.18/0.67  fof(f63,plain,(
% 2.18/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f51,f62])).
% 2.18/0.67  fof(f62,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f60,f61])).
% 2.18/0.67  fof(f61,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f17])).
% 2.18/0.67  fof(f17,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.18/0.67  fof(f60,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f16])).
% 2.18/0.67  fof(f16,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.18/0.67  fof(f51,plain,(
% 2.18/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f15])).
% 2.18/0.67  fof(f15,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.18/0.67  fof(f43,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f14])).
% 2.18/0.67  fof(f14,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.18/0.67  fof(f38,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f13])).
% 2.18/0.67  fof(f13,axiom,(
% 2.18/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.18/0.67  fof(f46,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f26,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 2.18/0.67    inference(flattening,[],[f25])).
% 2.18/0.67  fof(f25,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 2.18/0.67    inference(ennf_transformation,[],[f18])).
% 2.18/0.67  fof(f18,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 2.18/0.67  fof(f1447,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(sK2,k5_enumset1(X0,X0,X0,X0,X0,sK0,X1)))) )),
% 2.18/0.67    inference(forward_demodulation,[],[f1430,f37])).
% 2.18/0.67  fof(f37,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f2])).
% 2.18/0.67  fof(f2,axiom,(
% 2.18/0.67    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.18/0.67  fof(f1430,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,sK0,X1),sK2))) )),
% 2.18/0.67    inference(unit_resulting_resolution,[],[f1100,f797,f50])).
% 2.18/0.67  fof(f50,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f27])).
% 2.18/0.67  fof(f27,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.18/0.67    inference(ennf_transformation,[],[f4])).
% 2.18/0.67  fof(f4,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.18/0.67  fof(f797,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2))) )),
% 2.18/0.67    inference(unit_resulting_resolution,[],[f78,f76])).
% 2.18/0.67  fof(f76,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 2.18/0.67    inference(equality_resolution,[],[f74])).
% 2.18/0.67  fof(f74,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.18/0.67    inference(definition_unfolding,[],[f56,f64])).
% 2.18/0.67  fof(f56,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.18/0.67    inference(cnf_transformation,[],[f28])).
% 2.18/0.67  fof(f28,plain,(
% 2.18/0.67    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.18/0.67    inference(ennf_transformation,[],[f12])).
% 2.18/0.67  fof(f12,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.18/0.67  fof(f78,plain,(
% 2.18/0.67    ( ! [X4,X2,X0] : (sP5(X4,X2,X4,X0)) )),
% 2.18/0.67    inference(equality_resolution,[],[f53])).
% 2.18/0.67  fof(f53,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP5(X4,X2,X1,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f28])).
% 2.18/0.68  fof(f1189,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(sK1,k5_xboole_0(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,sK1)))) )),
% 2.18/0.68    inference(forward_demodulation,[],[f1175,f37])).
% 2.18/0.68  fof(f1175,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(sK1,k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,sK1),sK2))) )),
% 2.18/0.68    inference(unit_resulting_resolution,[],[f1079,f796,f50])).
% 2.18/0.68  fof(f796,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0))) )),
% 2.18/0.68    inference(unit_resulting_resolution,[],[f77,f76])).
% 2.18/0.68  fof(f77,plain,(
% 2.18/0.68    ( ! [X4,X0,X1] : (sP5(X4,X4,X1,X0)) )),
% 2.18/0.68    inference(equality_resolution,[],[f54])).
% 2.18/0.68  fof(f54,plain,(
% 2.18/0.68    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP5(X4,X2,X1,X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f28])).
% 2.18/0.68  fof(f551,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(forward_demodulation,[],[f546,f37])).
% 2.18/0.68  fof(f546,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(backward_demodulation,[],[f80,f539])).
% 2.18/0.68  fof(f539,plain,(
% 2.18/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.18/0.68    inference(forward_demodulation,[],[f513,f36])).
% 2.18/0.68  fof(f36,plain,(
% 2.18/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f1])).
% 2.18/0.68  fof(f1,axiom,(
% 2.18/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.18/0.68  fof(f513,plain,(
% 2.18/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 2.18/0.68    inference(superposition,[],[f45,f34])).
% 2.18/0.68  fof(f34,plain,(
% 2.18/0.68    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.18/0.68    inference(cnf_transformation,[],[f21])).
% 2.18/0.68  fof(f21,plain,(
% 2.18/0.68    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.68    inference(rectify,[],[f3])).
% 2.18/0.68  fof(f3,axiom,(
% 2.18/0.68    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.18/0.68  fof(f45,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f7])).
% 2.18/0.68  fof(f7,axiom,(
% 2.18/0.68    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.18/0.68  fof(f80,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(backward_demodulation,[],[f68,f36])).
% 2.18/0.68  fof(f68,plain,(
% 2.18/0.68    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.18/0.68    inference(definition_unfolding,[],[f29,f65,f39,f65])).
% 2.18/0.68  fof(f39,plain,(
% 2.18/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.68    inference(cnf_transformation,[],[f6])).
% 2.18/0.68  fof(f6,axiom,(
% 2.18/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.18/0.68  fof(f29,plain,(
% 2.18/0.68    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.18/0.68    inference(cnf_transformation,[],[f23])).
% 2.18/0.68  fof(f23,plain,(
% 2.18/0.68    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.18/0.68    inference(ennf_transformation,[],[f20])).
% 2.18/0.68  fof(f20,negated_conjecture,(
% 2.18/0.68    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.18/0.68    inference(negated_conjecture,[],[f19])).
% 2.18/0.68  fof(f19,conjecture,(
% 2.18/0.68    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.18/0.68  fof(f1100,plain,(
% 2.18/0.68    ~r2_hidden(sK0,sK2)),
% 2.18/0.68    inference(duplicate_literal_removal,[],[f1097])).
% 2.18/0.68  fof(f1097,plain,(
% 2.18/0.68    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2)),
% 2.18/0.68    inference(resolution,[],[f1095,f78])).
% 2.18/0.68  fof(f1095,plain,(
% 2.18/0.68    ( ! [X2] : (~sP5(X2,sK1,sK0,sK0) | ~r2_hidden(sK0,sK2) | ~r2_hidden(X2,sK2)) )),
% 2.18/0.68    inference(resolution,[],[f1089,f76])).
% 2.18/0.68  fof(f1089,plain,(
% 2.18/0.68    ( ! [X0] : (~r2_hidden(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(X0,sK2) | ~r2_hidden(sK0,sK2)) )),
% 2.18/0.68    inference(resolution,[],[f1054,f40])).
% 2.18/0.68  fof(f40,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f24])).
% 2.18/0.68  fof(f24,plain,(
% 2.18/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.18/0.68    inference(ennf_transformation,[],[f22])).
% 2.18/0.68  fof(f22,plain,(
% 2.18/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.68    inference(rectify,[],[f5])).
% 2.18/0.68  fof(f5,axiom,(
% 2.18/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.18/0.68  fof(f1054,plain,(
% 2.18/0.68    r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 2.18/0.68    inference(superposition,[],[f594,f550])).
% 2.18/0.68  fof(f550,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 2.18/0.68    inference(forward_demodulation,[],[f545,f37])).
% 2.18/0.68  fof(f545,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK0,sK2)),
% 2.18/0.68    inference(backward_demodulation,[],[f81,f539])).
% 2.18/0.68  fof(f81,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 2.18/0.68    inference(backward_demodulation,[],[f67,f36])).
% 2.18/0.68  fof(f67,plain,(
% 2.18/0.68    ~r2_hidden(sK0,sK2) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.18/0.68    inference(definition_unfolding,[],[f30,f65,f39,f65])).
% 2.18/0.68  fof(f30,plain,(
% 2.18/0.68    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.18/0.68    inference(cnf_transformation,[],[f23])).
% 2.18/0.68  fof(f594,plain,(
% 2.18/0.68    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X2)) )),
% 2.18/0.68    inference(superposition,[],[f543,f37])).
% 2.18/0.68  fof(f543,plain,(
% 2.18/0.68    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),X2)) )),
% 2.18/0.68    inference(backward_demodulation,[],[f92,f539])).
% 2.18/0.68  fof(f92,plain,(
% 2.18/0.68    ( ! [X2,X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)) )),
% 2.18/0.68    inference(superposition,[],[f69,f36])).
% 2.18/0.68  fof(f69,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.18/0.68    inference(definition_unfolding,[],[f35,f39])).
% 2.18/0.68  fof(f35,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f9])).
% 2.18/0.68  fof(f9,axiom,(
% 2.18/0.68    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.18/0.68  fof(f1079,plain,(
% 2.18/0.68    ~r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(duplicate_literal_removal,[],[f1076])).
% 2.18/0.68  fof(f1076,plain,(
% 2.18/0.68    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(resolution,[],[f1052,f77])).
% 2.18/0.68  fof(f1052,plain,(
% 2.18/0.68    ( ! [X2] : (~sP5(X2,sK1,sK0,sK0) | ~r2_hidden(sK1,sK2) | ~r2_hidden(X2,sK2)) )),
% 2.18/0.68    inference(resolution,[],[f1048,f76])).
% 2.18/0.68  fof(f1048,plain,(
% 2.18/0.68    ( ! [X0] : (~r2_hidden(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(X0,sK2) | ~r2_hidden(sK1,sK2)) )),
% 2.18/0.68    inference(resolution,[],[f1026,f40])).
% 2.18/0.68  fof(f1026,plain,(
% 2.18/0.68    r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(superposition,[],[f594,f549])).
% 2.18/0.68  fof(f549,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(forward_demodulation,[],[f544,f37])).
% 2.18/0.68  fof(f544,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(backward_demodulation,[],[f82,f539])).
% 2.18/0.68  fof(f82,plain,(
% 2.18/0.68    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 2.18/0.68    inference(backward_demodulation,[],[f66,f36])).
% 2.18/0.68  fof(f66,plain,(
% 2.18/0.68    ~r2_hidden(sK1,sK2) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.18/0.68    inference(definition_unfolding,[],[f31,f65,f39,f65])).
% 2.18/0.68  fof(f31,plain,(
% 2.18/0.68    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.18/0.68    inference(cnf_transformation,[],[f23])).
% 2.18/0.68  % SZS output end Proof for theBenchmark
% 2.18/0.68  % (27482)------------------------------
% 2.18/0.68  % (27482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.68  % (27482)Termination reason: Refutation
% 2.18/0.68  
% 2.18/0.68  % (27482)Memory used [KB]: 8059
% 2.18/0.68  % (27482)Time elapsed: 0.263 s
% 2.18/0.68  % (27482)------------------------------
% 2.18/0.68  % (27482)------------------------------
% 2.18/0.68  % (27457)Success in time 0.318 s
%------------------------------------------------------------------------------
