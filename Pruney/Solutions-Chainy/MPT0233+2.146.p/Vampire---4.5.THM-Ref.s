%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:23 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  101 (1506 expanded)
%              Number of leaves         :   14 ( 455 expanded)
%              Depth                    :   24
%              Number of atoms          :  294 (3617 expanded)
%              Number of equality atoms :  197 (2720 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(subsumption_resolution,[],[f448,f32])).

fof(f32,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f448,plain,(
    sK0 = sK3 ),
    inference(subsumption_resolution,[],[f447,f389])).

fof(f389,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f31,f326])).

fof(f326,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f325,f182])).

fof(f182,plain,
    ( sK0 != sK1
    | sK1 = sK2 ),
    inference(superposition,[],[f32,f181])).

fof(f181,plain,
    ( sK1 = sK3
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f169,f126])).

fof(f126,plain,(
    ! [X2] : k1_xboole_0 != k4_enumset1(X2,X2,X2,X2,X2,X2) ),
    inference(subsumption_resolution,[],[f123,f80])).

fof(f80,plain,(
    ! [X4,X1] : r2_hidden(X4,k4_enumset1(X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k4_enumset1(X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f123,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_enumset1(X2,X2,X2,X2,X2,X2)
      | ~ r2_hidden(X2,k4_enumset1(X2,X2,X2,X2,X2,X3)) ) ),
    inference(superposition,[],[f76,f97])).

fof(f97,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f82,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f82,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X1,X1,X1,X1,X1,X2) != X0 ) ),
    inference(definition_unfolding,[],[f50,f59,f59])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f51,f60,f59])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f59])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f169,plain,
    ( k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 = sK2
    | sK1 = sK3 ),
    inference(superposition,[],[f104,f162])).

fof(f162,plain,(
    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f152,f37])).

fof(f152,plain,(
    r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f151,f61])).

fof(f61,plain,(
    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f30,f59,f59])).

fof(f30,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1),X3)
      | r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X3) ) ),
    inference(superposition,[],[f39,f100])).

fof(f100,plain,(
    ! [X2,X3] : k4_enumset1(X3,X3,X3,X3,X3,X2) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X2)) ),
    inference(resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f83,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f49,f59,f60])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(resolution,[],[f86,f81])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f54,f60,f59])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f325,plain,
    ( sK0 = sK1
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f324,f31])).

fof(f324,plain,
    ( sK0 = sK2
    | sK0 = sK1
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f269,f126])).

fof(f269,plain,
    ( k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK2
    | sK0 = sK1
    | sK1 = sK2 ),
    inference(superposition,[],[f225,f184])).

fof(f184,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK1))
    | sK1 = sK2 ),
    inference(superposition,[],[f89,f181])).

fof(f89,plain,(
    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f61,f37])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X1))
      | X0 = X2
      | X0 = X1 ) ),
    inference(resolution,[],[f115,f78])).

fof(f78,plain,(
    ! [X4,X0] : r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X3,X3,X3,X3,X3,X3) = k4_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X0),k4_enumset1(X1,X1,X1,X1,X1,X2))
      | X1 = X3
      | X2 = X3 ) ),
    inference(resolution,[],[f74,f81])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f60,f59])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f31,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f447,plain,
    ( sK0 = sK1
    | sK0 = sK3 ),
    inference(subsumption_resolution,[],[f441,f126])).

fof(f441,plain,
    ( k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1
    | sK0 = sK3 ),
    inference(superposition,[],[f406,f104])).

fof(f406,plain,(
    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK3)) ),
    inference(resolution,[],[f255,f327])).

fof(f327,plain,(
    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK3)) ),
    inference(backward_demodulation,[],[f61,f326])).

fof(f255,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k4_enumset1(X14,X14,X14,X14,X14,X15),X16)
      | k1_xboole_0 = k4_xboole_0(k4_enumset1(X14,X14,X14,X14,X14,X14),X16) ) ),
    inference(resolution,[],[f156,f37])).

fof(f156,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),X4)
      | ~ r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3),X4) ) ),
    inference(superposition,[],[f39,f102])).

fof(f102,plain,(
    ! [X2,X3] : k4_enumset1(X2,X2,X2,X2,X2,X3) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X2,X2,X2,X2,X2,X3)) ),
    inference(resolution,[],[f84,f35])).

fof(f84,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f48,f59,f60])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (28671)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (28663)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (28679)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.56  % (28680)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.56  % (28672)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.57  % (28664)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.71/0.59  % (28661)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.71/0.59  % (28660)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.71/0.60  % (28670)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.71/0.61  % (28659)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.71/0.61  % (28658)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.71/0.61  % (28658)Refutation not found, incomplete strategy% (28658)------------------------------
% 1.71/0.61  % (28658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.61  % (28658)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.61  
% 1.71/0.61  % (28658)Memory used [KB]: 1663
% 1.71/0.61  % (28658)Time elapsed: 0.185 s
% 1.71/0.61  % (28658)------------------------------
% 1.71/0.61  % (28658)------------------------------
% 1.71/0.62  % (28682)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.71/0.62  % (28657)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.71/0.62  % (28662)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.71/0.62  % (28683)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.71/0.62  % (28674)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.71/0.62  % (28685)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.71/0.63  % (28684)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.71/0.63  % (28675)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.71/0.63  % (28679)Refutation found. Thanks to Tanya!
% 1.71/0.63  % SZS status Theorem for theBenchmark
% 1.71/0.63  % SZS output start Proof for theBenchmark
% 1.71/0.63  fof(f449,plain,(
% 1.71/0.63    $false),
% 1.71/0.63    inference(subsumption_resolution,[],[f448,f32])).
% 1.71/0.63  fof(f32,plain,(
% 1.71/0.63    sK0 != sK3),
% 1.71/0.63    inference(cnf_transformation,[],[f19])).
% 1.71/0.63  fof(f19,plain,(
% 1.71/0.63    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.71/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).
% 1.71/0.63  fof(f18,plain,(
% 1.71/0.63    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.71/0.63    introduced(choice_axiom,[])).
% 1.71/0.63  fof(f14,plain,(
% 1.71/0.63    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.71/0.63    inference(ennf_transformation,[],[f13])).
% 1.71/0.63  fof(f13,negated_conjecture,(
% 1.71/0.63    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.71/0.63    inference(negated_conjecture,[],[f12])).
% 1.71/0.63  fof(f12,conjecture,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.71/0.63  fof(f448,plain,(
% 1.71/0.63    sK0 = sK3),
% 1.71/0.63    inference(subsumption_resolution,[],[f447,f389])).
% 1.71/0.63  fof(f389,plain,(
% 1.71/0.63    sK0 != sK1),
% 1.71/0.63    inference(superposition,[],[f31,f326])).
% 1.71/0.63  fof(f326,plain,(
% 1.71/0.63    sK1 = sK2),
% 1.71/0.63    inference(subsumption_resolution,[],[f325,f182])).
% 1.71/0.63  fof(f182,plain,(
% 1.71/0.63    sK0 != sK1 | sK1 = sK2),
% 1.71/0.63    inference(superposition,[],[f32,f181])).
% 1.71/0.63  fof(f181,plain,(
% 1.71/0.63    sK1 = sK3 | sK1 = sK2),
% 1.71/0.63    inference(subsumption_resolution,[],[f169,f126])).
% 1.71/0.63  fof(f126,plain,(
% 1.71/0.63    ( ! [X2] : (k1_xboole_0 != k4_enumset1(X2,X2,X2,X2,X2,X2)) )),
% 1.71/0.63    inference(subsumption_resolution,[],[f123,f80])).
% 1.71/0.63  fof(f80,plain,(
% 1.71/0.63    ( ! [X4,X1] : (r2_hidden(X4,k4_enumset1(X4,X4,X4,X4,X4,X1))) )),
% 1.71/0.63    inference(equality_resolution,[],[f79])).
% 1.71/0.63  fof(f79,plain,(
% 1.71/0.63    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k4_enumset1(X4,X4,X4,X4,X4,X1) != X2) )),
% 1.71/0.63    inference(equality_resolution,[],[f66])).
% 1.71/0.63  fof(f66,plain,(
% 1.71/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 1.71/0.63    inference(definition_unfolding,[],[f41,f59])).
% 1.71/0.63  fof(f59,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.71/0.63    inference(definition_unfolding,[],[f34,f58])).
% 1.71/0.63  fof(f58,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.71/0.63    inference(definition_unfolding,[],[f38,f57])).
% 1.71/0.63  fof(f57,plain,(
% 1.71/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.71/0.63    inference(definition_unfolding,[],[f55,f56])).
% 1.71/0.63  fof(f56,plain,(
% 1.71/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f9])).
% 1.71/0.63  fof(f9,axiom,(
% 1.71/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.71/0.63  fof(f55,plain,(
% 1.71/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f8])).
% 1.71/0.63  fof(f8,axiom,(
% 1.71/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.71/0.63  fof(f38,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f7])).
% 1.71/0.63  fof(f7,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.71/0.63  fof(f34,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f6])).
% 1.71/0.63  fof(f6,axiom,(
% 1.71/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.71/0.63  fof(f41,plain,(
% 1.71/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.71/0.63    inference(cnf_transformation,[],[f25])).
% 1.71/0.63  fof(f25,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.71/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 1.71/0.63  fof(f24,plain,(
% 1.71/0.63    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.71/0.63    introduced(choice_axiom,[])).
% 1.71/0.63  fof(f23,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.71/0.63    inference(rectify,[],[f22])).
% 1.71/0.63  fof(f22,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.71/0.63    inference(flattening,[],[f21])).
% 1.71/0.63  fof(f21,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.71/0.63    inference(nnf_transformation,[],[f4])).
% 1.71/0.63  fof(f4,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.71/0.63  fof(f123,plain,(
% 1.71/0.63    ( ! [X2,X3] : (k1_xboole_0 != k4_enumset1(X2,X2,X2,X2,X2,X2) | ~r2_hidden(X2,k4_enumset1(X2,X2,X2,X2,X2,X3))) )),
% 1.71/0.63    inference(superposition,[],[f76,f97])).
% 1.71/0.63  fof(f97,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.71/0.63    inference(resolution,[],[f82,f37])).
% 1.71/0.63  fof(f37,plain,(
% 1.71/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.71/0.63    inference(cnf_transformation,[],[f20])).
% 1.71/0.63  fof(f20,plain,(
% 1.71/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.71/0.63    inference(nnf_transformation,[],[f1])).
% 1.71/0.63  fof(f1,axiom,(
% 1.71/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.71/0.63  fof(f82,plain,(
% 1.71/0.63    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 1.71/0.63    inference(equality_resolution,[],[f68])).
% 1.71/0.63  fof(f68,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X1,X1,X1,X1,X1,X2) != X0) )),
% 1.71/0.63    inference(definition_unfolding,[],[f50,f59,f59])).
% 1.71/0.63  fof(f50,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 1.71/0.63    inference(cnf_transformation,[],[f27])).
% 1.71/0.63  fof(f27,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.71/0.63    inference(flattening,[],[f26])).
% 1.71/0.63  fof(f26,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.71/0.63    inference(nnf_transformation,[],[f17])).
% 1.71/0.63  fof(f17,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.71/0.63    inference(ennf_transformation,[],[f11])).
% 1.71/0.63  fof(f11,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.71/0.63  fof(f76,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.71/0.63    inference(definition_unfolding,[],[f51,f60,f59])).
% 1.71/0.63  fof(f60,plain,(
% 1.71/0.63    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.71/0.63    inference(definition_unfolding,[],[f33,f59])).
% 1.71/0.63  fof(f33,plain,(
% 1.71/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f5])).
% 1.71/0.63  fof(f5,axiom,(
% 1.71/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.71/0.63  fof(f51,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f29])).
% 1.71/0.63  fof(f29,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.71/0.63    inference(flattening,[],[f28])).
% 1.71/0.63  fof(f28,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.71/0.63    inference(nnf_transformation,[],[f10])).
% 1.71/0.63  fof(f10,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.71/0.63  fof(f169,plain,(
% 1.71/0.63    k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | sK1 = sK2 | sK1 = sK3),
% 1.71/0.63    inference(superposition,[],[f104,f162])).
% 1.71/0.63  fof(f162,plain,(
% 1.71/0.63    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.71/0.63    inference(resolution,[],[f152,f37])).
% 1.71/0.63  fof(f152,plain,(
% 1.71/0.63    r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.71/0.63    inference(resolution,[],[f151,f61])).
% 1.71/0.63  fof(f61,plain,(
% 1.71/0.63    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.71/0.63    inference(definition_unfolding,[],[f30,f59,f59])).
% 1.71/0.63  fof(f30,plain,(
% 1.71/0.63    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.71/0.63    inference(cnf_transformation,[],[f19])).
% 1.71/0.63  fof(f151,plain,(
% 1.71/0.63    ( ! [X2,X3,X1] : (~r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1),X3) | r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X3)) )),
% 1.71/0.63    inference(superposition,[],[f39,f100])).
% 1.71/0.63  fof(f100,plain,(
% 1.71/0.63    ( ! [X2,X3] : (k4_enumset1(X3,X3,X3,X3,X3,X2) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X2))) )),
% 1.71/0.63    inference(resolution,[],[f83,f35])).
% 1.71/0.63  fof(f35,plain,(
% 1.71/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.71/0.63    inference(cnf_transformation,[],[f15])).
% 1.71/0.63  fof(f15,plain,(
% 1.71/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.71/0.63    inference(ennf_transformation,[],[f3])).
% 1.71/0.63  fof(f3,axiom,(
% 1.71/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.71/0.63  fof(f83,plain,(
% 1.71/0.63    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 1.71/0.63    inference(equality_resolution,[],[f69])).
% 1.71/0.63  fof(f69,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0) )),
% 1.71/0.63    inference(definition_unfolding,[],[f49,f59,f60])).
% 1.71/0.63  fof(f49,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.71/0.63    inference(cnf_transformation,[],[f27])).
% 1.71/0.63  fof(f39,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f16])).
% 1.71/0.63  fof(f16,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.71/0.63    inference(ennf_transformation,[],[f2])).
% 1.71/0.63  fof(f2,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.71/0.63  fof(f104,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2) )),
% 1.71/0.63    inference(resolution,[],[f86,f81])).
% 1.71/0.63  fof(f81,plain,(
% 1.71/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.71/0.63    inference(equality_resolution,[],[f67])).
% 1.71/0.63  fof(f67,plain,(
% 1.71/0.63    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 1.71/0.63    inference(definition_unfolding,[],[f40,f59])).
% 1.71/0.63  fof(f40,plain,(
% 1.71/0.63    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.71/0.63    inference(cnf_transformation,[],[f25])).
% 1.71/0.63  fof(f86,plain,(
% 1.71/0.63    ( ! [X2,X1] : (r2_hidden(X1,X2) | k4_enumset1(X1,X1,X1,X1,X1,X1) = k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)) )),
% 1.71/0.63    inference(equality_resolution,[],[f73])).
% 1.71/0.63  fof(f73,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 1.71/0.63    inference(definition_unfolding,[],[f54,f60,f59])).
% 1.71/0.63  fof(f54,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f29])).
% 1.71/0.63  fof(f325,plain,(
% 1.71/0.63    sK0 = sK1 | sK1 = sK2),
% 1.71/0.63    inference(subsumption_resolution,[],[f324,f31])).
% 1.71/0.63  fof(f324,plain,(
% 1.71/0.63    sK0 = sK2 | sK0 = sK1 | sK1 = sK2),
% 1.71/0.63    inference(subsumption_resolution,[],[f269,f126])).
% 1.71/0.63  fof(f269,plain,(
% 1.71/0.63    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) | sK0 = sK2 | sK0 = sK1 | sK1 = sK2),
% 1.71/0.63    inference(superposition,[],[f225,f184])).
% 1.71/0.63  fof(f184,plain,(
% 1.71/0.63    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK1)) | sK1 = sK2),
% 1.71/0.63    inference(superposition,[],[f89,f181])).
% 1.71/0.63  fof(f89,plain,(
% 1.71/0.63    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.71/0.63    inference(resolution,[],[f61,f37])).
% 1.71/0.63  fof(f225,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X1)) | X0 = X2 | X0 = X1) )),
% 1.71/0.63    inference(resolution,[],[f115,f78])).
% 1.71/0.63  fof(f78,plain,(
% 1.71/0.63    ( ! [X4,X0] : (r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X4))) )),
% 1.71/0.63    inference(equality_resolution,[],[f77])).
% 1.71/0.63  fof(f77,plain,(
% 1.71/0.63    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k4_enumset1(X0,X0,X0,X0,X0,X4) != X2) )),
% 1.71/0.63    inference(equality_resolution,[],[f65])).
% 1.71/0.63  fof(f65,plain,(
% 1.71/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 1.71/0.63    inference(definition_unfolding,[],[f42,f59])).
% 1.71/0.63  fof(f42,plain,(
% 1.71/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.71/0.63    inference(cnf_transformation,[],[f25])).
% 1.71/0.63  fof(f115,plain,(
% 1.71/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X3,X3,X3,X3,X3,X3) = k4_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X0),k4_enumset1(X1,X1,X1,X1,X1,X2)) | X1 = X3 | X2 = X3) )),
% 1.71/0.63    inference(resolution,[],[f74,f81])).
% 1.71/0.63  fof(f74,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | k4_enumset1(X0,X0,X0,X0,X0,X0) = k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 1.71/0.63    inference(definition_unfolding,[],[f53,f60,f59])).
% 1.71/0.63  fof(f53,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f29])).
% 1.71/0.63  fof(f31,plain,(
% 1.71/0.63    sK0 != sK2),
% 1.71/0.63    inference(cnf_transformation,[],[f19])).
% 1.71/0.63  fof(f447,plain,(
% 1.71/0.63    sK0 = sK1 | sK0 = sK3),
% 1.71/0.63    inference(subsumption_resolution,[],[f441,f126])).
% 1.71/0.63  fof(f441,plain,(
% 1.71/0.63    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) | sK0 = sK1 | sK0 = sK3),
% 1.71/0.63    inference(superposition,[],[f406,f104])).
% 1.71/0.63  fof(f406,plain,(
% 1.71/0.63    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK3))),
% 1.71/0.63    inference(resolution,[],[f255,f327])).
% 1.71/0.63  fof(f327,plain,(
% 1.71/0.63    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK3))),
% 1.71/0.63    inference(backward_demodulation,[],[f61,f326])).
% 1.71/0.63  fof(f255,plain,(
% 1.71/0.63    ( ! [X14,X15,X16] : (~r1_tarski(k4_enumset1(X14,X14,X14,X14,X14,X15),X16) | k1_xboole_0 = k4_xboole_0(k4_enumset1(X14,X14,X14,X14,X14,X14),X16)) )),
% 1.71/0.63    inference(resolution,[],[f156,f37])).
% 1.71/0.63  fof(f156,plain,(
% 1.71/0.63    ( ! [X4,X2,X3] : (r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),X4) | ~r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3),X4)) )),
% 1.71/0.63    inference(superposition,[],[f39,f102])).
% 1.71/0.63  fof(f102,plain,(
% 1.71/0.63    ( ! [X2,X3] : (k4_enumset1(X2,X2,X2,X2,X2,X3) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X2,X2,X2,X2,X2,X3))) )),
% 1.71/0.63    inference(resolution,[],[f84,f35])).
% 1.71/0.63  fof(f84,plain,(
% 1.71/0.63    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 1.71/0.63    inference(equality_resolution,[],[f70])).
% 1.71/0.63  fof(f70,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X1,X1,X1,X1,X1,X1) != X0) )),
% 1.71/0.63    inference(definition_unfolding,[],[f48,f59,f60])).
% 1.71/0.63  fof(f48,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 1.71/0.63    inference(cnf_transformation,[],[f27])).
% 1.71/0.63  % SZS output end Proof for theBenchmark
% 1.71/0.63  % (28679)------------------------------
% 1.71/0.63  % (28679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.63  % (28679)Termination reason: Refutation
% 1.71/0.63  
% 1.71/0.63  % (28679)Memory used [KB]: 6652
% 1.71/0.63  % (28679)Time elapsed: 0.218 s
% 1.71/0.63  % (28679)------------------------------
% 1.71/0.63  % (28679)------------------------------
% 1.71/0.63  % (28686)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.71/0.63  % (28677)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.71/0.63  % (28686)Refutation not found, incomplete strategy% (28686)------------------------------
% 1.71/0.63  % (28686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.63  % (28686)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.63  
% 1.71/0.63  % (28686)Memory used [KB]: 1663
% 1.71/0.63  % (28686)Time elapsed: 0.001 s
% 1.71/0.63  % (28686)------------------------------
% 1.71/0.63  % (28686)------------------------------
% 1.71/0.63  % (28656)Success in time 0.272 s
%------------------------------------------------------------------------------
