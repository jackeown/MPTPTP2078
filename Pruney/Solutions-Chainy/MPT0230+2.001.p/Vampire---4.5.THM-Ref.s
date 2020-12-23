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
% DateTime   : Thu Dec  3 12:36:34 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 183 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  220 ( 453 expanded)
%              Number of equality atoms :  163 ( 346 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f32,f31,f81,f231])).

fof(f231,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2))
      | sK1 = X0
      | sK2 = X0 ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2))
      | sK1 = X0
      | sK1 = X0
      | sK2 = X0 ) ),
    inference(superposition,[],[f82,f213])).

fof(f213,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f212,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f47,f58,f57,f60,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f212,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f211,f87])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f83,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f63,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f211,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f208,f110])).

fof(f110,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f109,f86])).

fof(f86,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f42,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5)) ),
    inference(forward_demodulation,[],[f105,f87])).

fof(f105,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X5,k1_xboole_0))) ),
    inference(superposition,[],[f61,f88])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f85,f37])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f40,f40])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f208,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f64,f98])).

fof(f98,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f30,f60,f59])).

fof(f30,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != sK2
    & sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK0 != sK2
      & sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f57,f57])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f82,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f81,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f31,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.22/0.52  % (31113)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.52  % (31126)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.52  % (31122)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.52  % (31117)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.52  % (31127)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.22/0.53  % (31121)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.53  % (31120)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.22/0.53  % (31134)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.53  % (31112)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.53  % (31123)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.53  % (31111)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.53  % (31112)Refutation not found, incomplete strategy% (31112)------------------------------
% 1.22/0.53  % (31112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (31112)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (31112)Memory used [KB]: 1663
% 1.22/0.53  % (31112)Time elapsed: 0.112 s
% 1.22/0.53  % (31112)------------------------------
% 1.22/0.53  % (31112)------------------------------
% 1.22/0.53  % (31123)Refutation not found, incomplete strategy% (31123)------------------------------
% 1.22/0.53  % (31123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (31123)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (31123)Memory used [KB]: 10618
% 1.22/0.53  % (31123)Time elapsed: 0.117 s
% 1.22/0.53  % (31123)------------------------------
% 1.22/0.53  % (31123)------------------------------
% 1.33/0.54  % (31128)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.54  % (31118)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.54  % (31119)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.54  % (31114)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (31116)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  % (31140)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (31140)Refutation not found, incomplete strategy% (31140)------------------------------
% 1.33/0.54  % (31140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (31140)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (31140)Memory used [KB]: 1663
% 1.33/0.54  % (31140)Time elapsed: 0.140 s
% 1.33/0.54  % (31140)------------------------------
% 1.33/0.54  % (31140)------------------------------
% 1.33/0.55  % (31136)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.55  % (31127)Refutation not found, incomplete strategy% (31127)------------------------------
% 1.33/0.55  % (31127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (31127)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (31127)Memory used [KB]: 10618
% 1.33/0.55  % (31127)Time elapsed: 0.134 s
% 1.33/0.55  % (31127)------------------------------
% 1.33/0.55  % (31127)------------------------------
% 1.33/0.55  % (31132)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  % (31129)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.55  % (31124)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.55  % (31121)Refutation not found, incomplete strategy% (31121)------------------------------
% 1.33/0.55  % (31121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (31121)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (31121)Memory used [KB]: 10746
% 1.33/0.55  % (31121)Time elapsed: 0.140 s
% 1.33/0.55  % (31121)------------------------------
% 1.33/0.55  % (31121)------------------------------
% 1.33/0.55  % (31129)Refutation not found, incomplete strategy% (31129)------------------------------
% 1.33/0.55  % (31129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (31129)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (31129)Memory used [KB]: 1663
% 1.33/0.55  % (31129)Time elapsed: 0.136 s
% 1.33/0.55  % (31129)------------------------------
% 1.33/0.55  % (31129)------------------------------
% 1.33/0.55  % (31137)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.55  % (31130)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.55  % (31133)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.33/0.55  % (31139)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.55  % (31137)Refutation not found, incomplete strategy% (31137)------------------------------
% 1.33/0.55  % (31137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (31138)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (31115)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.56  % (31133)Refutation found. Thanks to Tanya!
% 1.33/0.56  % SZS status Theorem for theBenchmark
% 1.33/0.56  % SZS output start Proof for theBenchmark
% 1.33/0.56  fof(f232,plain,(
% 1.33/0.56    $false),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f32,f31,f81,f231])).
% 1.33/0.56  fof(f231,plain,(
% 1.33/0.56    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2)) | sK1 = X0 | sK2 = X0) )),
% 1.33/0.56    inference(duplicate_literal_removal,[],[f227])).
% 1.33/0.56  fof(f227,plain,(
% 1.33/0.56    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2)) | sK1 = X0 | sK1 = X0 | sK2 = X0) )),
% 1.33/0.56    inference(superposition,[],[f82,f213])).
% 1.33/0.56  fof(f213,plain,(
% 1.33/0.56    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 1.33/0.56    inference(forward_demodulation,[],[f212,f65])).
% 1.33/0.56  fof(f65,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 1.33/0.56    inference(definition_unfolding,[],[f47,f58,f57,f60,f59])).
% 1.33/0.56  fof(f59,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.33/0.56    inference(definition_unfolding,[],[f38,f58])).
% 1.33/0.56  fof(f38,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f13])).
% 1.33/0.56  fof(f13,axiom,(
% 1.33/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.33/0.56  fof(f60,plain,(
% 1.33/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.33/0.56    inference(definition_unfolding,[],[f35,f59])).
% 1.33/0.56  fof(f35,plain,(
% 1.33/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f12])).
% 1.33/0.56  fof(f12,axiom,(
% 1.33/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.33/0.56  fof(f57,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.33/0.56    inference(definition_unfolding,[],[f39,f40])).
% 1.33/0.56  fof(f40,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f4])).
% 1.33/0.56  fof(f4,axiom,(
% 1.33/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.33/0.56  fof(f39,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f9])).
% 1.33/0.56  fof(f9,axiom,(
% 1.33/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.33/0.56  fof(f58,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.33/0.56    inference(definition_unfolding,[],[f46,f48])).
% 1.33/0.56  fof(f48,plain,(
% 1.33/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  fof(f15,axiom,(
% 1.33/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.33/0.56  fof(f46,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f14])).
% 1.33/0.56  fof(f14,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.33/0.56  fof(f47,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f11])).
% 1.33/0.56  fof(f11,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 1.33/0.56  fof(f212,plain,(
% 1.33/0.56    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.33/0.56    inference(forward_demodulation,[],[f211,f87])).
% 1.33/0.56  fof(f87,plain,(
% 1.33/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.33/0.56    inference(backward_demodulation,[],[f83,f85])).
% 1.33/0.56  fof(f85,plain,(
% 1.33/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.33/0.56    inference(resolution,[],[f42,f33])).
% 1.33/0.56  fof(f33,plain,(
% 1.33/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f6])).
% 1.33/0.56  fof(f6,axiom,(
% 1.33/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.33/0.56  fof(f42,plain,(
% 1.33/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.33/0.56    inference(cnf_transformation,[],[f19])).
% 1.33/0.56  fof(f19,plain,(
% 1.33/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.33/0.56    inference(ennf_transformation,[],[f5])).
% 1.33/0.56  fof(f5,axiom,(
% 1.33/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.33/0.56  fof(f83,plain,(
% 1.33/0.56    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.33/0.56    inference(superposition,[],[f63,f37])).
% 1.33/0.56  fof(f37,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f2])).
% 1.33/0.56  fof(f2,axiom,(
% 1.33/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.33/0.56  fof(f63,plain,(
% 1.33/0.56    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.33/0.56    inference(definition_unfolding,[],[f34,f40])).
% 1.33/0.56  fof(f34,plain,(
% 1.33/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.33/0.56    inference(cnf_transformation,[],[f7])).
% 1.33/0.56  fof(f7,axiom,(
% 1.33/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.33/0.56  fof(f211,plain,(
% 1.33/0.56    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k1_xboole_0)),
% 1.33/0.56    inference(forward_demodulation,[],[f208,f110])).
% 1.33/0.56  fof(f110,plain,(
% 1.33/0.56    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 1.33/0.56    inference(forward_demodulation,[],[f109,f86])).
% 1.33/0.56  fof(f86,plain,(
% 1.33/0.56    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.33/0.56    inference(resolution,[],[f42,f74])).
% 1.33/0.56  fof(f74,plain,(
% 1.33/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.56    inference(equality_resolution,[],[f44])).
% 1.33/0.56  fof(f44,plain,(
% 1.33/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.56    inference(cnf_transformation,[],[f24])).
% 1.33/0.56  fof(f24,plain,(
% 1.33/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.56    inference(flattening,[],[f23])).
% 1.33/0.56  fof(f23,plain,(
% 1.33/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.56    inference(nnf_transformation,[],[f3])).
% 1.33/0.56  fof(f3,axiom,(
% 1.33/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.56  fof(f109,plain,(
% 1.33/0.56    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5))) )),
% 1.33/0.56    inference(forward_demodulation,[],[f105,f87])).
% 1.33/0.56  fof(f105,plain,(
% 1.33/0.56    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X5,k1_xboole_0)))) )),
% 1.33/0.56    inference(superposition,[],[f61,f88])).
% 1.33/0.56  fof(f88,plain,(
% 1.33/0.56    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.33/0.56    inference(superposition,[],[f85,f37])).
% 1.33/0.56  fof(f61,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.33/0.56    inference(definition_unfolding,[],[f41,f40,f40])).
% 1.33/0.56  fof(f41,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f8])).
% 1.33/0.56  fof(f8,axiom,(
% 1.33/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.33/0.56  fof(f208,plain,(
% 1.33/0.56    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.33/0.56    inference(superposition,[],[f64,f98])).
% 1.33/0.56  fof(f98,plain,(
% 1.33/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.33/0.56    inference(resolution,[],[f62,f42])).
% 1.33/0.56  fof(f62,plain,(
% 1.33/0.56    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.33/0.56    inference(definition_unfolding,[],[f30,f60,f59])).
% 1.33/0.56  fof(f30,plain,(
% 1.33/0.56    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.33/0.56    inference(cnf_transformation,[],[f22])).
% 1.33/0.56  fof(f22,plain,(
% 1.33/0.56    sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.33/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 1.33/0.56  fof(f21,plain,(
% 1.33/0.56    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f18,plain,(
% 1.33/0.56    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.33/0.56    inference(ennf_transformation,[],[f17])).
% 1.33/0.56  fof(f17,negated_conjecture,(
% 1.33/0.56    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.33/0.56    inference(negated_conjecture,[],[f16])).
% 1.33/0.56  fof(f16,conjecture,(
% 1.33/0.56    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.33/0.56  fof(f64,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.33/0.56    inference(definition_unfolding,[],[f36,f57,f57])).
% 1.33/0.56  fof(f36,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f1])).
% 1.33/0.56  fof(f1,axiom,(
% 1.33/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.33/0.56  fof(f82,plain,(
% 1.33/0.56    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.33/0.56    inference(equality_resolution,[],[f73])).
% 1.33/0.56  fof(f73,plain,(
% 1.33/0.56    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.33/0.56    inference(definition_unfolding,[],[f49,f58])).
% 1.33/0.56  fof(f49,plain,(
% 1.33/0.56    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.33/0.56    inference(cnf_transformation,[],[f29])).
% 1.33/0.56  fof(f29,plain,(
% 1.33/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.33/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.33/0.56  fof(f28,plain,(
% 1.33/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f27,plain,(
% 1.33/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.33/0.56    inference(rectify,[],[f26])).
% 1.33/0.56  fof(f26,plain,(
% 1.33/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.33/0.56    inference(flattening,[],[f25])).
% 1.33/0.56  fof(f25,plain,(
% 1.33/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.33/0.56    inference(nnf_transformation,[],[f20])).
% 1.33/0.56  fof(f20,plain,(
% 1.33/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.33/0.56    inference(ennf_transformation,[],[f10])).
% 1.33/0.56  fof(f10,axiom,(
% 1.33/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.33/0.56  fof(f81,plain,(
% 1.33/0.56    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 1.33/0.56    inference(equality_resolution,[],[f80])).
% 1.33/0.56  fof(f80,plain,(
% 1.33/0.56    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 1.33/0.56    inference(equality_resolution,[],[f72])).
% 1.33/0.56  fof(f72,plain,(
% 1.33/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.33/0.56    inference(definition_unfolding,[],[f50,f58])).
% 1.33/0.56  fof(f50,plain,(
% 1.33/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.33/0.56    inference(cnf_transformation,[],[f29])).
% 1.33/0.56  fof(f31,plain,(
% 1.33/0.56    sK0 != sK1),
% 1.33/0.56    inference(cnf_transformation,[],[f22])).
% 1.33/0.56  fof(f32,plain,(
% 1.33/0.56    sK0 != sK2),
% 1.33/0.56    inference(cnf_transformation,[],[f22])).
% 1.33/0.56  % SZS output end Proof for theBenchmark
% 1.33/0.56  % (31133)------------------------------
% 1.33/0.56  % (31133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (31133)Termination reason: Refutation
% 1.33/0.56  
% 1.33/0.56  % (31133)Memory used [KB]: 6268
% 1.33/0.56  % (31133)Time elapsed: 0.142 s
% 1.33/0.56  % (31133)------------------------------
% 1.33/0.56  % (31133)------------------------------
% 1.33/0.56  % (31110)Success in time 0.189 s
%------------------------------------------------------------------------------
