%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:16 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 130 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  275 ( 357 expanded)
%              Number of equality atoms :  195 ( 249 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1757,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f52,f51,f1719,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1719,plain,(
    r2_hidden(sK0,k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f94,f1538])).

fof(f1538,plain,(
    k2_tarski(sK2,sK3) = k1_enumset1(sK2,sK3,sK0) ),
    inference(forward_demodulation,[],[f1537,f176])).

fof(f176,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f172,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f172,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f64,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f57,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1537,plain,(
    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k1_enumset1(sK2,sK3,sK0) ),
    inference(forward_demodulation,[],[f1523,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f141,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f141,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f79,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f1523,plain,(
    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK0)) ),
    inference(superposition,[],[f64,f1126])).

fof(f1126,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f1107,f835])).

fof(f835,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f121,f833])).

fof(f833,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f827,f178])).

fof(f178,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f112,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f69,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f827,plain,(
    ! [X2] : k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f66,f286])).

fof(f286,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f282,f176])).

fof(f282,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f122,f112])).

fof(f122,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f65,f62])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f121,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f65,f59])).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1107,plain,(
    k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f65,f348])).

fof(f348,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f268,f69])).

fof(f268,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f237,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f237,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_tarski(sK0,sK1))
      | r1_tarski(X8,k2_tarski(sK2,sK3)) ) ),
    inference(superposition,[],[f119,f114])).

fof(f114,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f69,f50])).

fof(f50,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f119,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k3_xboole_0(X3,X2))
      | r1_tarski(X4,X2) ) ),
    inference(superposition,[],[f71,f62])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f94,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK7(X0,X1,X2,X3) != X2
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X2
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X0
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
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
     => ( ( ( sK7(X0,X1,X2,X3) != X2
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X2
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X0
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

% (15670)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f45,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f51,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (15641)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (15626)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (15633)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (15633)Refutation not found, incomplete strategy% (15633)------------------------------
% 0.21/0.52  % (15633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15633)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15633)Memory used [KB]: 1791
% 0.21/0.52  % (15633)Time elapsed: 0.060 s
% 0.21/0.52  % (15633)------------------------------
% 0.21/0.52  % (15633)------------------------------
% 0.21/0.53  % (15624)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (15629)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (15622)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (15623)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (15642)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (15621)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (15631)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (15619)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.55  % (15645)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (15646)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.55  % (15644)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.55  % (15620)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.42/0.55  % (15648)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (15648)Refutation not found, incomplete strategy% (15648)------------------------------
% 1.42/0.55  % (15648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (15648)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (15648)Memory used [KB]: 1663
% 1.42/0.55  % (15648)Time elapsed: 0.001 s
% 1.42/0.55  % (15648)------------------------------
% 1.42/0.55  % (15648)------------------------------
% 1.42/0.55  % (15620)Refutation not found, incomplete strategy% (15620)------------------------------
% 1.42/0.55  % (15620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (15639)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.55  % (15627)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.55  % (15630)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.55  % (15647)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.55  % (15620)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (15620)Memory used [KB]: 1663
% 1.42/0.55  % (15620)Time elapsed: 0.135 s
% 1.42/0.55  % (15620)------------------------------
% 1.42/0.55  % (15620)------------------------------
% 1.42/0.55  % (15638)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.56  % (15636)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.56  % (15634)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.56  % (15637)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.56  % (15637)Refutation not found, incomplete strategy% (15637)------------------------------
% 1.42/0.56  % (15637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (15635)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.56  % (15628)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (15631)Refutation not found, incomplete strategy% (15631)------------------------------
% 1.42/0.56  % (15631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (15643)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.56  % (15631)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (15631)Memory used [KB]: 10618
% 1.42/0.56  % (15631)Time elapsed: 0.151 s
% 1.42/0.56  % (15631)------------------------------
% 1.42/0.56  % (15631)------------------------------
% 1.42/0.56  % (15637)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (15637)Memory used [KB]: 1791
% 1.42/0.56  % (15637)Time elapsed: 0.137 s
% 1.42/0.56  % (15637)------------------------------
% 1.42/0.56  % (15637)------------------------------
% 1.59/0.57  % (15635)Refutation not found, incomplete strategy% (15635)------------------------------
% 1.59/0.57  % (15635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (15646)Refutation not found, incomplete strategy% (15646)------------------------------
% 1.59/0.57  % (15646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (15646)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (15646)Memory used [KB]: 6268
% 1.59/0.57  % (15646)Time elapsed: 0.139 s
% 1.59/0.57  % (15646)------------------------------
% 1.59/0.57  % (15646)------------------------------
% 1.59/0.57  % (15625)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.57  % (15643)Refutation not found, incomplete strategy% (15643)------------------------------
% 1.59/0.57  % (15643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (15643)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (15643)Memory used [KB]: 10746
% 1.59/0.57  % (15643)Time elapsed: 0.157 s
% 1.59/0.57  % (15643)------------------------------
% 1.59/0.57  % (15643)------------------------------
% 1.59/0.58  % (15632)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.59/0.58  % (15644)Refutation not found, incomplete strategy% (15644)------------------------------
% 1.59/0.58  % (15644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (15644)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (15644)Memory used [KB]: 6396
% 1.59/0.58  % (15644)Time elapsed: 0.142 s
% 1.59/0.58  % (15644)------------------------------
% 1.59/0.58  % (15644)------------------------------
% 1.59/0.58  % (15635)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (15635)Memory used [KB]: 10618
% 1.59/0.58  % (15635)Time elapsed: 0.147 s
% 1.59/0.58  % (15635)------------------------------
% 1.59/0.58  % (15635)------------------------------
% 1.59/0.60  % (15640)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.05/0.65  % (15626)Refutation found. Thanks to Tanya!
% 2.05/0.65  % SZS status Theorem for theBenchmark
% 2.05/0.65  % SZS output start Proof for theBenchmark
% 2.05/0.66  fof(f1757,plain,(
% 2.05/0.66    $false),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f52,f51,f1719,f92])).
% 2.05/0.66  fof(f92,plain,(
% 2.05/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.05/0.66    inference(equality_resolution,[],[f72])).
% 2.05/0.66  fof(f72,plain,(
% 2.05/0.66    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.05/0.66    inference(cnf_transformation,[],[f44])).
% 2.05/0.66  fof(f44,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 2.05/0.66  fof(f43,plain,(
% 2.05/0.66    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f42,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.66    inference(rectify,[],[f41])).
% 2.05/0.66  fof(f41,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.66    inference(flattening,[],[f40])).
% 2.05/0.66  fof(f40,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.66    inference(nnf_transformation,[],[f16])).
% 2.05/0.66  fof(f16,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.05/0.66  fof(f1719,plain,(
% 2.05/0.66    r2_hidden(sK0,k2_tarski(sK2,sK3))),
% 2.05/0.66    inference(superposition,[],[f94,f1538])).
% 2.05/0.66  fof(f1538,plain,(
% 2.05/0.66    k2_tarski(sK2,sK3) = k1_enumset1(sK2,sK3,sK0)),
% 2.05/0.66    inference(forward_demodulation,[],[f1537,f176])).
% 2.05/0.66  fof(f176,plain,(
% 2.05/0.66    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.05/0.66    inference(forward_demodulation,[],[f172,f55])).
% 2.05/0.66  fof(f55,plain,(
% 2.05/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f7])).
% 2.05/0.66  fof(f7,axiom,(
% 2.05/0.66    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.05/0.66  fof(f172,plain,(
% 2.05/0.66    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 2.05/0.66    inference(superposition,[],[f64,f103])).
% 2.05/0.66  fof(f103,plain,(
% 2.05/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.05/0.66    inference(resolution,[],[f57,f60])).
% 2.05/0.66  fof(f60,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f10])).
% 2.05/0.66  fof(f10,axiom,(
% 2.05/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.05/0.66  fof(f57,plain,(
% 2.05/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f28])).
% 2.05/0.66  fof(f28,plain,(
% 2.05/0.66    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.05/0.66    inference(ennf_transformation,[],[f11])).
% 2.05/0.66  fof(f11,axiom,(
% 2.05/0.66    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.05/0.66  fof(f64,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f14])).
% 2.05/0.66  fof(f14,axiom,(
% 2.05/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.05/0.66  fof(f1537,plain,(
% 2.05/0.66    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k1_enumset1(sK2,sK3,sK0)),
% 2.05/0.66    inference(forward_demodulation,[],[f1523,f142])).
% 2.05/0.66  fof(f142,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.05/0.66    inference(forward_demodulation,[],[f141,f70])).
% 2.05/0.66  fof(f70,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f20])).
% 2.05/0.66  fof(f20,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.05/0.66  fof(f141,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.05/0.66    inference(superposition,[],[f79,f63])).
% 2.05/0.66  fof(f63,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f19])).
% 2.05/0.66  fof(f19,axiom,(
% 2.05/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.05/0.66  fof(f79,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f17])).
% 2.05/0.66  fof(f17,axiom,(
% 2.05/0.66    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 2.05/0.66  fof(f1523,plain,(
% 2.05/0.66    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK0))),
% 2.05/0.66    inference(superposition,[],[f64,f1126])).
% 2.05/0.66  fof(f1126,plain,(
% 2.05/0.66    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 2.05/0.66    inference(forward_demodulation,[],[f1107,f835])).
% 2.05/0.66  fof(f835,plain,(
% 2.05/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.05/0.66    inference(backward_demodulation,[],[f121,f833])).
% 2.05/0.66  fof(f833,plain,(
% 2.05/0.66    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 2.05/0.66    inference(forward_demodulation,[],[f827,f178])).
% 2.05/0.66  fof(f178,plain,(
% 2.05/0.66    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 2.05/0.66    inference(superposition,[],[f112,f62])).
% 2.05/0.66  fof(f62,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f1])).
% 2.05/0.66  fof(f1,axiom,(
% 2.05/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.05/0.66  fof(f112,plain,(
% 2.05/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.05/0.66    inference(resolution,[],[f69,f54])).
% 2.05/0.66  fof(f54,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f9])).
% 2.05/0.66  fof(f9,axiom,(
% 2.05/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.05/0.66  fof(f69,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f31])).
% 2.05/0.66  fof(f31,plain,(
% 2.05/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f8])).
% 2.05/0.66  fof(f8,axiom,(
% 2.05/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.05/0.66  fof(f827,plain,(
% 2.05/0.66    ( ! [X2] : (k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2)) )),
% 2.05/0.66    inference(superposition,[],[f66,f286])).
% 2.05/0.66  fof(f286,plain,(
% 2.05/0.66    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) )),
% 2.05/0.66    inference(forward_demodulation,[],[f282,f176])).
% 2.05/0.66  fof(f282,plain,(
% 2.05/0.66    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 2.05/0.66    inference(superposition,[],[f122,f112])).
% 2.05/0.66  fof(f122,plain,(
% 2.05/0.66    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.05/0.66    inference(superposition,[],[f65,f62])).
% 2.05/0.66  fof(f65,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f5])).
% 2.05/0.66  fof(f5,axiom,(
% 2.05/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.05/0.66  fof(f66,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f12])).
% 2.05/0.66  fof(f12,axiom,(
% 2.05/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.05/0.66  fof(f121,plain,(
% 2.05/0.66    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.05/0.66    inference(superposition,[],[f65,f59])).
% 2.05/0.66  fof(f59,plain,(
% 2.05/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f25])).
% 2.05/0.66  fof(f25,plain,(
% 2.05/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.05/0.66    inference(rectify,[],[f2])).
% 2.05/0.66  fof(f2,axiom,(
% 2.05/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.05/0.66  fof(f1107,plain,(
% 2.05/0.66    k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 2.05/0.66    inference(superposition,[],[f65,f348])).
% 2.05/0.66  fof(f348,plain,(
% 2.05/0.66    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 2.05/0.66    inference(resolution,[],[f268,f69])).
% 2.05/0.66  fof(f268,plain,(
% 2.05/0.66    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 2.05/0.66    inference(resolution,[],[f237,f61])).
% 2.05/0.66  fof(f61,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f22])).
% 2.05/0.66  fof(f22,axiom,(
% 2.05/0.66    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 2.05/0.66  fof(f237,plain,(
% 2.05/0.66    ( ! [X8] : (~r1_tarski(X8,k2_tarski(sK0,sK1)) | r1_tarski(X8,k2_tarski(sK2,sK3))) )),
% 2.05/0.66    inference(superposition,[],[f119,f114])).
% 2.05/0.66  fof(f114,plain,(
% 2.05/0.66    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.05/0.66    inference(resolution,[],[f69,f50])).
% 2.05/0.66  fof(f50,plain,(
% 2.05/0.66    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.05/0.66    inference(cnf_transformation,[],[f35])).
% 2.05/0.66  fof(f35,plain,(
% 2.05/0.66    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f34])).
% 2.05/0.66  fof(f34,plain,(
% 2.05/0.66    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f27,plain,(
% 2.05/0.66    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.05/0.66    inference(ennf_transformation,[],[f24])).
% 2.05/0.66  fof(f24,negated_conjecture,(
% 2.05/0.66    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.05/0.66    inference(negated_conjecture,[],[f23])).
% 2.05/0.66  fof(f23,conjecture,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 2.05/0.66  fof(f119,plain,(
% 2.05/0.66    ( ! [X4,X2,X3] : (~r1_tarski(X4,k3_xboole_0(X3,X2)) | r1_tarski(X4,X2)) )),
% 2.05/0.66    inference(superposition,[],[f71,f62])).
% 2.05/0.66  fof(f71,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f32])).
% 2.05/0.66  fof(f32,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.05/0.66    inference(ennf_transformation,[],[f6])).
% 2.05/0.66  fof(f6,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.05/0.66  fof(f94,plain,(
% 2.05/0.66    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 2.05/0.66    inference(equality_resolution,[],[f93])).
% 2.05/0.66  fof(f93,plain,(
% 2.05/0.66    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 2.05/0.66    inference(equality_resolution,[],[f83])).
% 2.05/0.66  fof(f83,plain,(
% 2.05/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.05/0.66    inference(cnf_transformation,[],[f49])).
% 2.05/0.66  fof(f49,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK7(X0,X1,X2,X3) != X2 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X2 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X0 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 2.05/0.66  fof(f48,plain,(
% 2.05/0.66    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X2 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X2 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X0 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f47,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.05/0.66    inference(rectify,[],[f46])).
% 2.05/0.66  fof(f46,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.05/0.66    inference(flattening,[],[f45])).
% 2.05/0.66  % (15670)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.05/0.66  fof(f45,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.05/0.66    inference(nnf_transformation,[],[f33])).
% 2.05/0.66  fof(f33,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.05/0.66    inference(ennf_transformation,[],[f15])).
% 2.05/0.66  fof(f15,axiom,(
% 2.05/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.05/0.66  fof(f51,plain,(
% 2.05/0.66    sK0 != sK2),
% 2.05/0.66    inference(cnf_transformation,[],[f35])).
% 2.05/0.66  fof(f52,plain,(
% 2.05/0.66    sK0 != sK3),
% 2.05/0.66    inference(cnf_transformation,[],[f35])).
% 2.05/0.66  % SZS output end Proof for theBenchmark
% 2.05/0.66  % (15626)------------------------------
% 2.05/0.66  % (15626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.66  % (15626)Termination reason: Refutation
% 2.05/0.66  
% 2.05/0.66  % (15626)Memory used [KB]: 2686
% 2.05/0.66  % (15626)Time elapsed: 0.184 s
% 2.05/0.66  % (15626)------------------------------
% 2.05/0.66  % (15626)------------------------------
% 2.05/0.66  % (15618)Success in time 0.293 s
%------------------------------------------------------------------------------
