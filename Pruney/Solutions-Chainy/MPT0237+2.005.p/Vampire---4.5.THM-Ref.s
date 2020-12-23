%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:29 EST 2020

% Result     : Theorem 21.23s
% Output     : Refutation 21.23s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 596 expanded)
%              Number of leaves         :   21 ( 196 expanded)
%              Depth                    :   20
%              Number of atoms          :  205 ( 910 expanded)
%              Number of equality atoms :  170 ( 819 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7110,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7041,f1459])).

fof(f1459,plain,(
    ! [X14,X15,X16] : k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16) = k3_tarski(k6_enumset1(k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16))) ),
    inference(forward_demodulation,[],[f1445,f251])).

fof(f251,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f110,f101])).

fof(f101,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f88,f84])).

fof(f84,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f44,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f110,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f101,f37])).

fof(f1445,plain,(
    ! [X14,X15,X16] : k3_tarski(k6_enumset1(k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16))) = k5_xboole_0(k5_xboole_0(k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16)),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16)) ),
    inference(superposition,[],[f66,f213])).

fof(f213,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f78,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(definition_unfolding,[],[f42,f64,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f78,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f7041,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f65,f7040])).

fof(f7040,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f7039,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f41,f62,f64,f64])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f7039,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f7038,f215])).

fof(f215,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f82,f68])).

fof(f82,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7038,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f6368,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6368,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))
    | sK0 = sK1 ),
    inference(superposition,[],[f1466,f232])).

fof(f232,plain,(
    ! [X4,X3] :
      ( k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
      | X3 = X4 ) ),
    inference(superposition,[],[f67,f37])).

fof(f1466,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f1465,f37])).

fof(f1465,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f1460,f36])).

fof(f1460,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f498,f1446])).

fof(f1446,plain,(
    ! [X19,X17,X20,X18] : k3_xboole_0(k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),X20),k6_enumset1(X17,X17,X17,X17,X17,X17,X18,X19)) = k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k3_xboole_0(X20,k6_enumset1(X17,X17,X17,X17,X17,X17,X18,X19))) ),
    inference(superposition,[],[f124,f213])).

fof(f124,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f45,f36])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f498,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f188,f44])).

fof(f188,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f65,f66])).

fof(f65,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f32,f62,f62,f64,f64])).

fof(f32,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (31281)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.47  % (31297)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.47  % (31297)Refutation not found, incomplete strategy% (31297)------------------------------
% 0.19/0.47  % (31297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (31297)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (31297)Memory used [KB]: 1663
% 0.19/0.47  % (31297)Time elapsed: 0.074 s
% 0.19/0.47  % (31297)------------------------------
% 0.19/0.47  % (31297)------------------------------
% 0.19/0.50  % (31278)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (31275)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (31296)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (31274)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (31274)Refutation not found, incomplete strategy% (31274)------------------------------
% 0.19/0.52  % (31274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (31274)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (31274)Memory used [KB]: 1663
% 0.19/0.52  % (31274)Time elapsed: 0.115 s
% 0.19/0.52  % (31274)------------------------------
% 0.19/0.52  % (31274)------------------------------
% 0.19/0.52  % (31288)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (31279)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (31276)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (31276)Refutation not found, incomplete strategy% (31276)------------------------------
% 0.19/0.53  % (31276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (31276)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (31276)Memory used [KB]: 10746
% 0.19/0.53  % (31276)Time elapsed: 0.125 s
% 0.19/0.53  % (31276)------------------------------
% 0.19/0.53  % (31276)------------------------------
% 0.19/0.53  % (31286)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (31277)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (31300)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (31289)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.53  % (31303)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (31289)Refutation not found, incomplete strategy% (31289)------------------------------
% 0.19/0.53  % (31289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (31289)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (31289)Memory used [KB]: 6140
% 0.19/0.53  % (31289)Time elapsed: 0.118 s
% 0.19/0.53  % (31289)------------------------------
% 0.19/0.53  % (31289)------------------------------
% 0.19/0.53  % (31292)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (31302)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (31295)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.54  % (31301)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.54  % (31295)Refutation not found, incomplete strategy% (31295)------------------------------
% 0.19/0.54  % (31295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31295)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (31295)Memory used [KB]: 1791
% 0.19/0.54  % (31295)Time elapsed: 0.140 s
% 0.19/0.54  % (31295)------------------------------
% 0.19/0.54  % (31295)------------------------------
% 0.19/0.54  % (31282)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (31291)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.54  % (31291)Refutation not found, incomplete strategy% (31291)------------------------------
% 0.19/0.54  % (31291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31282)Refutation not found, incomplete strategy% (31282)------------------------------
% 0.19/0.54  % (31282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31282)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (31282)Memory used [KB]: 10746
% 0.19/0.54  % (31282)Time elapsed: 0.135 s
% 0.19/0.54  % (31282)------------------------------
% 0.19/0.54  % (31282)------------------------------
% 0.19/0.54  % (31283)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.54  % (31294)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.54  % (31284)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (31293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (31294)Refutation not found, incomplete strategy% (31294)------------------------------
% 0.19/0.54  % (31294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31284)Refutation not found, incomplete strategy% (31284)------------------------------
% 0.19/0.54  % (31284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31285)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (31291)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (31291)Memory used [KB]: 10618
% 0.19/0.54  % (31291)Time elapsed: 0.141 s
% 0.19/0.54  % (31291)------------------------------
% 0.19/0.54  % (31291)------------------------------
% 0.19/0.55  % (31280)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.55  % (31299)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.55  % (31287)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.55  % (31294)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (31294)Memory used [KB]: 10746
% 0.19/0.55  % (31294)Time elapsed: 0.152 s
% 0.19/0.55  % (31294)------------------------------
% 0.19/0.55  % (31294)------------------------------
% 0.19/0.55  % (31284)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (31284)Memory used [KB]: 10618
% 0.19/0.55  % (31284)Time elapsed: 0.150 s
% 0.19/0.55  % (31284)------------------------------
% 0.19/0.55  % (31284)------------------------------
% 0.19/0.55  % (31290)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.55  % (31285)Refutation not found, incomplete strategy% (31285)------------------------------
% 0.19/0.55  % (31285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (31285)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (31285)Memory used [KB]: 10618
% 0.19/0.55  % (31285)Time elapsed: 0.160 s
% 0.19/0.55  % (31285)------------------------------
% 0.19/0.55  % (31285)------------------------------
% 0.19/0.55  % (31298)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.60  % (31304)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.91/0.61  % (31304)Refutation not found, incomplete strategy% (31304)------------------------------
% 1.91/0.61  % (31304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (31304)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.61  
% 1.91/0.61  % (31304)Memory used [KB]: 6140
% 1.91/0.61  % (31304)Time elapsed: 0.064 s
% 1.91/0.61  % (31304)------------------------------
% 1.91/0.61  % (31304)------------------------------
% 2.11/0.65  % (31305)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.66  % (31306)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.11/0.67  % (31307)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.67  % (31308)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.11/0.68  % (31312)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.11/0.68  % (31310)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.11/0.69  % (31311)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.11/0.69  % (31313)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.71/0.71  % (31309)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.71/0.75  % (31315)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 3.27/0.82  % (31279)Time limit reached!
% 3.27/0.82  % (31279)------------------------------
% 3.27/0.82  % (31279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.82  % (31279)Termination reason: Time limit
% 3.27/0.82  % (31279)Termination phase: Saturation
% 3.27/0.82  
% 3.27/0.82  % (31279)Memory used [KB]: 9083
% 3.27/0.82  % (31279)Time elapsed: 0.400 s
% 3.27/0.82  % (31279)------------------------------
% 3.27/0.82  % (31279)------------------------------
% 4.09/0.90  % (31286)Time limit reached!
% 4.09/0.90  % (31286)------------------------------
% 4.09/0.90  % (31286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.90  % (31286)Termination reason: Time limit
% 4.09/0.90  % (31286)Termination phase: Saturation
% 4.09/0.90  
% 4.09/0.90  % (31286)Memory used [KB]: 10746
% 4.09/0.90  % (31286)Time elapsed: 0.513 s
% 4.09/0.90  % (31286)------------------------------
% 4.09/0.90  % (31286)------------------------------
% 4.39/0.95  % (31316)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.39/0.96  % (31308)Time limit reached!
% 4.39/0.96  % (31308)------------------------------
% 4.39/0.96  % (31308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.96  % (31308)Termination reason: Time limit
% 4.39/0.96  
% 4.39/0.96  % (31308)Memory used [KB]: 13560
% 4.39/0.96  % (31308)Time elapsed: 0.402 s
% 4.39/0.96  % (31308)------------------------------
% 4.39/0.96  % (31308)------------------------------
% 4.39/0.98  % (31307)Time limit reached!
% 4.39/0.98  % (31307)------------------------------
% 4.39/0.98  % (31307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.98  % (31307)Termination reason: Time limit
% 4.39/0.98  
% 4.39/0.98  % (31307)Memory used [KB]: 8443
% 4.39/0.98  % (31307)Time elapsed: 0.419 s
% 4.39/0.98  % (31307)------------------------------
% 4.39/0.98  % (31307)------------------------------
% 4.39/0.98  % (31275)Time limit reached!
% 4.39/0.98  % (31275)------------------------------
% 4.39/0.98  % (31275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.98  % (31275)Termination reason: Time limit
% 4.39/0.98  
% 4.39/0.98  % (31275)Memory used [KB]: 10362
% 4.39/0.98  % (31275)Time elapsed: 0.575 s
% 4.39/0.98  % (31275)------------------------------
% 4.39/0.98  % (31275)------------------------------
% 4.39/0.99  % (31290)Time limit reached!
% 4.39/0.99  % (31290)------------------------------
% 4.39/0.99  % (31290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.99  % (31290)Termination reason: Time limit
% 4.39/0.99  % (31290)Termination phase: Saturation
% 4.39/0.99  
% 4.39/0.99  % (31290)Memory used [KB]: 15991
% 4.39/0.99  % (31290)Time elapsed: 0.600 s
% 4.39/0.99  % (31290)------------------------------
% 4.39/0.99  % (31290)------------------------------
% 5.01/1.02  % (31302)Time limit reached!
% 5.01/1.02  % (31302)------------------------------
% 5.01/1.02  % (31302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.02  % (31302)Termination reason: Time limit
% 5.01/1.02  
% 5.01/1.02  % (31302)Memory used [KB]: 11001
% 5.01/1.02  % (31302)Time elapsed: 0.621 s
% 5.01/1.02  % (31302)------------------------------
% 5.01/1.02  % (31302)------------------------------
% 5.01/1.02  % (31281)Time limit reached!
% 5.01/1.02  % (31281)------------------------------
% 5.01/1.02  % (31281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.02  % (31281)Termination reason: Time limit
% 5.01/1.02  % (31281)Termination phase: Saturation
% 5.01/1.02  
% 5.01/1.02  % (31281)Memory used [KB]: 12920
% 5.01/1.02  % (31281)Time elapsed: 0.600 s
% 5.01/1.02  % (31281)------------------------------
% 5.01/1.02  % (31281)------------------------------
% 5.01/1.03  % (31317)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.43/1.13  % (31318)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.43/1.13  % (31318)Refutation not found, incomplete strategy% (31318)------------------------------
% 5.43/1.13  % (31318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.43/1.13  % (31318)Termination reason: Refutation not found, incomplete strategy
% 5.43/1.13  
% 5.43/1.13  % (31318)Memory used [KB]: 1663
% 5.43/1.13  % (31318)Time elapsed: 0.120 s
% 5.43/1.13  % (31318)------------------------------
% 5.43/1.13  % (31318)------------------------------
% 5.43/1.14  % (31321)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 5.43/1.14  % (31320)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.43/1.14  % (31319)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.43/1.14  % (31323)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 5.43/1.15  % (31322)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.85/1.27  % (31324)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 8.19/1.42  % (31321)Time limit reached!
% 8.19/1.42  % (31321)------------------------------
% 8.19/1.42  % (31321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.19/1.42  % (31321)Termination reason: Time limit
% 8.19/1.42  % (31321)Termination phase: Saturation
% 8.19/1.42  
% 8.19/1.42  % (31321)Memory used [KB]: 4221
% 8.19/1.42  % (31321)Time elapsed: 0.400 s
% 8.19/1.42  % (31321)------------------------------
% 8.19/1.42  % (31321)------------------------------
% 8.19/1.45  % (31317)Time limit reached!
% 8.19/1.45  % (31317)------------------------------
% 8.19/1.45  % (31317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.19/1.45  % (31317)Termination reason: Time limit
% 8.19/1.45  
% 8.19/1.45  % (31317)Memory used [KB]: 4221
% 8.19/1.45  % (31317)Time elapsed: 0.524 s
% 8.19/1.45  % (31317)------------------------------
% 8.19/1.45  % (31317)------------------------------
% 8.75/1.55  % (31325)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 9.49/1.59  % (31324)Time limit reached!
% 9.49/1.59  % (31324)------------------------------
% 9.49/1.59  % (31324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.49/1.59  % (31324)Termination reason: Time limit
% 9.49/1.59  
% 9.49/1.59  % (31324)Memory used [KB]: 5500
% 9.49/1.59  % (31324)Time elapsed: 0.416 s
% 9.49/1.59  % (31324)------------------------------
% 9.49/1.59  % (31324)------------------------------
% 9.49/1.59  % (31326)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 9.74/1.62  % (31296)Time limit reached!
% 9.74/1.62  % (31296)------------------------------
% 9.74/1.62  % (31296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.74/1.62  % (31296)Termination reason: Time limit
% 9.74/1.62  
% 9.74/1.62  % (31296)Memory used [KB]: 15351
% 9.74/1.62  % (31296)Time elapsed: 1.201 s
% 9.74/1.62  % (31296)------------------------------
% 9.74/1.62  % (31296)------------------------------
% 9.96/1.63  % (31300)Time limit reached!
% 9.96/1.63  % (31300)------------------------------
% 9.96/1.63  % (31300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.96/1.63  % (31300)Termination reason: Time limit
% 9.96/1.63  
% 9.96/1.63  % (31300)Memory used [KB]: 16119
% 9.96/1.63  % (31300)Time elapsed: 1.230 s
% 9.96/1.63  % (31300)------------------------------
% 9.96/1.63  % (31300)------------------------------
% 9.96/1.71  % (31327)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.96/1.72  % (31298)Time limit reached!
% 9.96/1.72  % (31298)------------------------------
% 9.96/1.72  % (31298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.96/1.72  % (31298)Termination reason: Time limit
% 9.96/1.72  % (31298)Termination phase: Saturation
% 9.96/1.72  
% 9.96/1.72  % (31298)Memory used [KB]: 22899
% 9.96/1.72  % (31298)Time elapsed: 1.300 s
% 9.96/1.72  % (31298)------------------------------
% 9.96/1.72  % (31298)------------------------------
% 10.67/1.75  % (31328)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.67/1.76  % (31329)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.67/1.79  % (31310)Time limit reached!
% 10.67/1.79  % (31310)------------------------------
% 10.67/1.79  % (31310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.67/1.79  % (31310)Termination reason: Time limit
% 10.67/1.79  % (31310)Termination phase: Saturation
% 10.67/1.79  
% 10.67/1.79  % (31310)Memory used [KB]: 15223
% 10.67/1.79  % (31310)Time elapsed: 1.200 s
% 10.67/1.79  % (31310)------------------------------
% 10.67/1.79  % (31310)------------------------------
% 11.14/1.86  % (31330)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.14/1.86  % (31330)Refutation not found, incomplete strategy% (31330)------------------------------
% 11.14/1.86  % (31330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.14/1.86  % (31330)Termination reason: Refutation not found, incomplete strategy
% 11.14/1.86  
% 11.14/1.86  % (31330)Memory used [KB]: 6140
% 11.14/1.86  % (31330)Time elapsed: 0.102 s
% 11.14/1.86  % (31330)------------------------------
% 11.14/1.86  % (31330)------------------------------
% 12.04/1.90  % (31328)Refutation not found, incomplete strategy% (31328)------------------------------
% 12.04/1.90  % (31328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.04/1.92  % (31328)Termination reason: Refutation not found, incomplete strategy
% 12.04/1.92  
% 12.04/1.92  % (31328)Memory used [KB]: 6140
% 12.04/1.92  % (31328)Time elapsed: 0.220 s
% 12.04/1.92  % (31328)------------------------------
% 12.04/1.92  % (31328)------------------------------
% 12.04/1.93  % (31331)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.04/1.96  % (31301)Time limit reached!
% 12.04/1.96  % (31301)------------------------------
% 12.04/1.96  % (31301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.04/1.96  % (31301)Termination reason: Time limit
% 12.04/1.96  
% 12.04/1.96  % (31301)Memory used [KB]: 23922
% 12.04/1.96  % (31301)Time elapsed: 1.556 s
% 12.04/1.96  % (31301)------------------------------
% 12.04/1.96  % (31301)------------------------------
% 13.26/2.04  % (31332)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 13.26/2.04  % (31332)Refutation not found, incomplete strategy% (31332)------------------------------
% 13.26/2.04  % (31332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.26/2.04  % (31332)Termination reason: Refutation not found, incomplete strategy
% 13.26/2.04  
% 13.26/2.04  % (31332)Memory used [KB]: 10746
% 13.26/2.04  % (31332)Time elapsed: 0.122 s
% 13.26/2.04  % (31332)------------------------------
% 13.26/2.04  % (31332)------------------------------
% 13.26/2.06  % (31278)Time limit reached!
% 13.26/2.06  % (31278)------------------------------
% 13.26/2.06  % (31278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.26/2.06  % (31278)Termination reason: Time limit
% 13.26/2.06  
% 13.26/2.06  % (31278)Memory used [KB]: 16247
% 13.26/2.06  % (31278)Time elapsed: 1.659 s
% 13.26/2.06  % (31278)------------------------------
% 13.26/2.06  % (31278)------------------------------
% 13.26/2.07  % (31329)Time limit reached!
% 13.26/2.07  % (31329)------------------------------
% 13.26/2.07  % (31329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.26/2.07  % (31329)Termination reason: Time limit
% 13.26/2.07  
% 13.26/2.07  % (31329)Memory used [KB]: 10490
% 13.26/2.07  % (31329)Time elapsed: 0.412 s
% 13.26/2.07  % (31329)------------------------------
% 13.26/2.07  % (31329)------------------------------
% 14.53/2.23  % (31320)Time limit reached!
% 14.53/2.23  % (31320)------------------------------
% 14.53/2.23  % (31320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.53/2.23  % (31320)Termination reason: Time limit
% 14.53/2.23  
% 14.53/2.23  % (31320)Memory used [KB]: 12025
% 14.53/2.23  % (31320)Time elapsed: 1.218 s
% 14.53/2.23  % (31320)------------------------------
% 14.53/2.23  % (31320)------------------------------
% 14.53/2.25  % (31331)Time limit reached!
% 14.53/2.25  % (31331)------------------------------
% 14.53/2.25  % (31331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.53/2.25  % (31331)Termination reason: Time limit
% 14.53/2.25  
% 14.53/2.25  % (31331)Memory used [KB]: 9083
% 14.53/2.25  % (31331)Time elapsed: 0.422 s
% 14.53/2.25  % (31331)------------------------------
% 14.53/2.25  % (31331)------------------------------
% 15.22/2.27  % (31306)Time limit reached!
% 15.22/2.27  % (31306)------------------------------
% 15.22/2.27  % (31306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.22/2.27  % (31306)Termination reason: Time limit
% 15.22/2.27  
% 15.22/2.27  % (31306)Memory used [KB]: 25330
% 15.22/2.27  % (31306)Time elapsed: 1.724 s
% 15.22/2.27  % (31306)------------------------------
% 15.22/2.27  % (31306)------------------------------
% 15.26/2.29  % (31288)Time limit reached!
% 15.26/2.29  % (31288)------------------------------
% 15.26/2.29  % (31288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.26/2.29  % (31288)Termination reason: Time limit
% 15.26/2.29  
% 15.26/2.29  % (31288)Memory used [KB]: 21236
% 15.26/2.29  % (31288)Time elapsed: 1.845 s
% 15.26/2.29  % (31288)------------------------------
% 15.26/2.29  % (31288)------------------------------
% 15.55/2.32  % (31312)Time limit reached!
% 15.55/2.32  % (31312)------------------------------
% 15.55/2.32  % (31312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.55/2.32  % (31312)Termination reason: Time limit
% 15.55/2.32  
% 15.55/2.32  % (31312)Memory used [KB]: 14711
% 15.55/2.32  % (31312)Time elapsed: 1.736 s
% 15.55/2.32  % (31312)------------------------------
% 15.55/2.32  % (31312)------------------------------
% 16.42/2.44  % (31292)Time limit reached!
% 16.42/2.44  % (31292)------------------------------
% 16.42/2.44  % (31292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.42/2.44  % (31292)Termination reason: Time limit
% 16.42/2.44  
% 16.42/2.44  % (31292)Memory used [KB]: 17270
% 16.42/2.44  % (31292)Time elapsed: 2.035 s
% 16.42/2.44  % (31292)------------------------------
% 16.42/2.44  % (31292)------------------------------
% 16.42/2.46  % (31323)Time limit reached!
% 16.42/2.46  % (31323)------------------------------
% 16.42/2.46  % (31323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.42/2.46  % (31323)Termination reason: Time limit
% 16.42/2.46  % (31323)Termination phase: Saturation
% 16.42/2.46  
% 16.42/2.46  % (31323)Memory used [KB]: 23539
% 16.42/2.46  % (31323)Time elapsed: 1.300 s
% 16.42/2.46  % (31323)------------------------------
% 16.42/2.46  % (31323)------------------------------
% 16.42/2.47  % (31280)Time limit reached!
% 16.42/2.47  % (31280)------------------------------
% 16.42/2.47  % (31280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.42/2.47  % (31280)Termination reason: Time limit
% 16.42/2.47  % (31280)Termination phase: Saturation
% 16.42/2.47  
% 16.42/2.47  % (31280)Memory used [KB]: 36459
% 16.42/2.47  % (31280)Time elapsed: 2.0000 s
% 16.42/2.47  % (31280)------------------------------
% 16.42/2.47  % (31280)------------------------------
% 20.44/3.00  % (31293)Time limit reached!
% 20.44/3.00  % (31293)------------------------------
% 20.44/3.00  % (31293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.23/3.02  % (31293)Termination reason: Time limit
% 21.23/3.02  % (31293)Termination phase: Saturation
% 21.23/3.02  
% 21.23/3.02  % (31293)Memory used [KB]: 49764
% 21.23/3.02  % (31293)Time elapsed: 2.600 s
% 21.23/3.02  % (31293)------------------------------
% 21.23/3.02  % (31293)------------------------------
% 21.23/3.05  % (31326)Refutation found. Thanks to Tanya!
% 21.23/3.05  % SZS status Theorem for theBenchmark
% 21.23/3.05  % SZS output start Proof for theBenchmark
% 21.23/3.05  fof(f7110,plain,(
% 21.23/3.05    $false),
% 21.23/3.05    inference(subsumption_resolution,[],[f7041,f1459])).
% 21.23/3.05  fof(f1459,plain,(
% 21.23/3.05    ( ! [X14,X15,X16] : (k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16) = k3_tarski(k6_enumset1(k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16)))) )),
% 21.23/3.05    inference(forward_demodulation,[],[f1445,f251])).
% 21.23/3.05  fof(f251,plain,(
% 21.23/3.05    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 21.23/3.05    inference(superposition,[],[f110,f101])).
% 21.23/3.05  fof(f101,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 21.23/3.05    inference(forward_demodulation,[],[f88,f84])).
% 21.23/3.05  fof(f84,plain,(
% 21.23/3.05    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 21.23/3.05    inference(superposition,[],[f37,f34])).
% 21.23/3.05  fof(f34,plain,(
% 21.23/3.05    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.23/3.05    inference(cnf_transformation,[],[f4])).
% 21.23/3.05  fof(f4,axiom,(
% 21.23/3.05    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 21.23/3.05  fof(f37,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f2])).
% 21.23/3.05  fof(f2,axiom,(
% 21.23/3.05    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 21.23/3.05  fof(f88,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 21.23/3.05    inference(superposition,[],[f44,f33])).
% 21.23/3.05  fof(f33,plain,(
% 21.23/3.05    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f6])).
% 21.23/3.05  fof(f6,axiom,(
% 21.23/3.05    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 21.23/3.05  fof(f44,plain,(
% 21.23/3.05    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 21.23/3.05    inference(cnf_transformation,[],[f5])).
% 21.23/3.05  fof(f5,axiom,(
% 21.23/3.05    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 21.23/3.05  fof(f110,plain,(
% 21.23/3.05    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 21.23/3.05    inference(superposition,[],[f101,f37])).
% 21.23/3.05  fof(f1445,plain,(
% 21.23/3.05    ( ! [X14,X15,X16] : (k3_tarski(k6_enumset1(k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16))) = k5_xboole_0(k5_xboole_0(k6_enumset1(X14,X14,X14,X14,X14,X14,X15,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16)),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16))) )),
% 21.23/3.05    inference(superposition,[],[f66,f213])).
% 21.23/3.05  fof(f213,plain,(
% 21.23/3.05    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 21.23/3.05    inference(unit_resulting_resolution,[],[f78,f68])).
% 21.23/3.05  fof(f68,plain,(
% 21.23/3.05    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 21.23/3.05    inference(definition_unfolding,[],[f42,f64,f64])).
% 21.23/3.05  fof(f64,plain,(
% 21.23/3.05    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 21.23/3.05    inference(definition_unfolding,[],[f35,f62])).
% 21.23/3.05  fof(f62,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 21.23/3.05    inference(definition_unfolding,[],[f39,f61])).
% 21.23/3.05  fof(f61,plain,(
% 21.23/3.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 21.23/3.05    inference(definition_unfolding,[],[f43,f60])).
% 21.23/3.05  fof(f60,plain,(
% 21.23/3.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 21.23/3.05    inference(definition_unfolding,[],[f46,f59])).
% 21.23/3.05  fof(f59,plain,(
% 21.23/3.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 21.23/3.05    inference(definition_unfolding,[],[f55,f58])).
% 21.23/3.05  fof(f58,plain,(
% 21.23/3.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 21.23/3.05    inference(definition_unfolding,[],[f56,f57])).
% 21.23/3.05  fof(f57,plain,(
% 21.23/3.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f15])).
% 21.23/3.05  fof(f15,axiom,(
% 21.23/3.05    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 21.23/3.05  fof(f56,plain,(
% 21.23/3.05    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f14])).
% 21.23/3.05  fof(f14,axiom,(
% 21.23/3.05    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 21.23/3.05  fof(f55,plain,(
% 21.23/3.05    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f13])).
% 21.23/3.05  fof(f13,axiom,(
% 21.23/3.05    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 21.23/3.05  fof(f46,plain,(
% 21.23/3.05    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f12])).
% 21.23/3.05  fof(f12,axiom,(
% 21.23/3.05    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 21.23/3.05  fof(f43,plain,(
% 21.23/3.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f11])).
% 21.23/3.05  fof(f11,axiom,(
% 21.23/3.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 21.23/3.05  fof(f39,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f10])).
% 21.23/3.05  fof(f10,axiom,(
% 21.23/3.05    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 21.23/3.05  fof(f35,plain,(
% 21.23/3.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f9])).
% 21.23/3.05  fof(f9,axiom,(
% 21.23/3.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 21.23/3.05  fof(f42,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 21.23/3.05    inference(cnf_transformation,[],[f23])).
% 21.23/3.05  fof(f23,plain,(
% 21.23/3.05    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 21.23/3.05    inference(ennf_transformation,[],[f16])).
% 21.23/3.05  fof(f16,axiom,(
% 21.23/3.05    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 21.23/3.05  fof(f78,plain,(
% 21.23/3.05    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 21.23/3.05    inference(equality_resolution,[],[f77])).
% 21.23/3.05  fof(f77,plain,(
% 21.23/3.05    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 21.23/3.05    inference(equality_resolution,[],[f73])).
% 21.23/3.05  fof(f73,plain,(
% 21.23/3.05    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 21.23/3.05    inference(definition_unfolding,[],[f50,f61])).
% 21.23/3.05  fof(f50,plain,(
% 21.23/3.05    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 21.23/3.05    inference(cnf_transformation,[],[f31])).
% 21.23/3.05  fof(f31,plain,(
% 21.23/3.05    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.23/3.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 21.23/3.05  fof(f30,plain,(
% 21.23/3.05    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 21.23/3.05    introduced(choice_axiom,[])).
% 21.23/3.05  fof(f29,plain,(
% 21.23/3.05    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.23/3.05    inference(rectify,[],[f28])).
% 21.23/3.05  fof(f28,plain,(
% 21.23/3.05    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.23/3.05    inference(flattening,[],[f27])).
% 21.23/3.05  fof(f27,plain,(
% 21.23/3.05    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.23/3.05    inference(nnf_transformation,[],[f24])).
% 21.23/3.05  fof(f24,plain,(
% 21.23/3.05    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 21.23/3.05    inference(ennf_transformation,[],[f8])).
% 21.23/3.05  fof(f8,axiom,(
% 21.23/3.05    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 21.23/3.05  fof(f66,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 21.23/3.05    inference(definition_unfolding,[],[f40,f63])).
% 21.23/3.05  fof(f63,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 21.23/3.05    inference(definition_unfolding,[],[f38,f62])).
% 21.23/3.05  fof(f38,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 21.23/3.05    inference(cnf_transformation,[],[f17])).
% 21.23/3.05  fof(f17,axiom,(
% 21.23/3.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 21.23/3.05  fof(f40,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 21.23/3.05    inference(cnf_transformation,[],[f7])).
% 21.23/3.05  fof(f7,axiom,(
% 21.23/3.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.23/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 21.23/3.05  fof(f7041,plain,(
% 21.23/3.05    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 21.23/3.05    inference(backward_demodulation,[],[f65,f7040])).
% 21.23/3.05  fof(f7040,plain,(
% 21.23/3.05    sK0 = sK1),
% 21.23/3.05    inference(subsumption_resolution,[],[f7039,f67])).
% 21.23/3.05  fof(f67,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 21.23/3.05    inference(definition_unfolding,[],[f41,f62,f64,f64])).
% 21.23/3.05  fof(f41,plain,(
% 21.23/3.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 21.23/3.05    inference(cnf_transformation,[],[f22])).
% 21.23/3.07  fof(f22,plain,(
% 21.23/3.07    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 21.23/3.07    inference(ennf_transformation,[],[f18])).
% 21.23/3.07  fof(f18,axiom,(
% 21.23/3.07    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 21.23/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 21.23/3.07  fof(f7039,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 21.23/3.07    inference(forward_demodulation,[],[f7038,f215])).
% 21.23/3.07  fof(f215,plain,(
% 21.23/3.07    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 21.23/3.07    inference(unit_resulting_resolution,[],[f82,f68])).
% 21.23/3.07  fof(f82,plain,(
% 21.23/3.07    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 21.23/3.07    inference(equality_resolution,[],[f81])).
% 21.23/3.07  fof(f81,plain,(
% 21.23/3.07    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 21.23/3.07    inference(equality_resolution,[],[f75])).
% 21.23/3.07  fof(f75,plain,(
% 21.23/3.07    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 21.23/3.07    inference(definition_unfolding,[],[f48,f61])).
% 21.23/3.07  fof(f48,plain,(
% 21.23/3.07    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 21.23/3.07    inference(cnf_transformation,[],[f31])).
% 21.23/3.07  fof(f7038,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | sK0 = sK1),
% 21.23/3.07    inference(forward_demodulation,[],[f6368,f36])).
% 21.23/3.07  fof(f36,plain,(
% 21.23/3.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 21.23/3.07    inference(cnf_transformation,[],[f1])).
% 21.23/3.07  fof(f1,axiom,(
% 21.23/3.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 21.23/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 21.23/3.07  fof(f6368,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))) | sK0 = sK1),
% 21.23/3.07    inference(superposition,[],[f1466,f232])).
% 21.23/3.07  fof(f232,plain,(
% 21.23/3.07    ( ! [X4,X3] : (k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) | X3 = X4) )),
% 21.23/3.07    inference(superposition,[],[f67,f37])).
% 21.23/3.07  fof(f1466,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 21.23/3.07    inference(forward_demodulation,[],[f1465,f37])).
% 21.23/3.07  fof(f1465,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 21.23/3.07    inference(forward_demodulation,[],[f1460,f36])).
% 21.23/3.07  fof(f1460,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 21.23/3.07    inference(backward_demodulation,[],[f498,f1446])).
% 21.23/3.07  fof(f1446,plain,(
% 21.23/3.07    ( ! [X19,X17,X20,X18] : (k3_xboole_0(k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),X20),k6_enumset1(X17,X17,X17,X17,X17,X17,X18,X19)) = k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k3_xboole_0(X20,k6_enumset1(X17,X17,X17,X17,X17,X17,X18,X19)))) )),
% 21.23/3.07    inference(superposition,[],[f124,f213])).
% 21.23/3.07  fof(f124,plain,(
% 21.23/3.07    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X1))) )),
% 21.23/3.07    inference(superposition,[],[f45,f36])).
% 21.23/3.07  fof(f45,plain,(
% 21.23/3.07    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 21.23/3.07    inference(cnf_transformation,[],[f3])).
% 21.23/3.07  fof(f3,axiom,(
% 21.23/3.07    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 21.23/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 21.23/3.07  fof(f498,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 21.23/3.07    inference(superposition,[],[f188,f44])).
% 21.23/3.07  fof(f188,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 21.23/3.07    inference(superposition,[],[f65,f66])).
% 21.23/3.07  fof(f65,plain,(
% 21.23/3.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 21.23/3.07    inference(definition_unfolding,[],[f32,f62,f62,f64,f64])).
% 21.23/3.07  fof(f32,plain,(
% 21.23/3.07    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 21.23/3.07    inference(cnf_transformation,[],[f26])).
% 21.23/3.07  fof(f26,plain,(
% 21.23/3.07    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 21.23/3.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).
% 21.23/3.07  fof(f25,plain,(
% 21.23/3.07    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 21.23/3.07    introduced(choice_axiom,[])).
% 21.23/3.07  fof(f21,plain,(
% 21.23/3.07    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 21.23/3.07    inference(ennf_transformation,[],[f20])).
% 21.23/3.07  fof(f20,negated_conjecture,(
% 21.23/3.07    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 21.23/3.07    inference(negated_conjecture,[],[f19])).
% 21.23/3.07  fof(f19,conjecture,(
% 21.23/3.07    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 21.23/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 21.23/3.07  % SZS output end Proof for theBenchmark
% 21.23/3.07  % (31326)------------------------------
% 21.23/3.07  % (31326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.23/3.07  % (31326)Termination reason: Refutation
% 21.23/3.07  
% 21.23/3.07  % (31326)Memory used [KB]: 26737
% 21.23/3.07  % (31326)Time elapsed: 1.502 s
% 21.23/3.07  % (31326)------------------------------
% 21.23/3.07  % (31326)------------------------------
% 21.23/3.07  % (31273)Success in time 2.723 s
%------------------------------------------------------------------------------
