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
% DateTime   : Thu Dec  3 12:35:52 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  162 (330227 expanded)
%              Number of leaves         :   19 (113184 expanded)
%              Depth                    :   37
%              Number of atoms          :  280 (352997 expanded)
%              Number of equality atoms :  248 (352943 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1940,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1938,f34])).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f1938,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f1926,f85])).

fof(f85,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1926,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f1920])).

fof(f1920,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | sK1 = X0
      | sK1 = X0
      | sK1 = X0 ) ),
    inference(superposition,[],[f88,f1685])).

fof(f1685,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f1677,f562])).

fof(f562,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f327,f552])).

fof(f552,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f314,f551])).

fof(f551,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f407,f546])).

fof(f546,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(superposition,[],[f325,f39])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f325,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))) ),
    inference(superposition,[],[f47,f323])).

fof(f323,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f320,f314])).

fof(f320,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f71,f312])).

fof(f312,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f303,f173])).

fof(f173,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f89,f172])).

fof(f172,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f134,f167])).

fof(f167,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f98,f39])).

fof(f98,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f47,f96])).

fof(f96,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f93,f89])).

fof(f93,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f71,f68])).

fof(f68,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f33,f66,f66,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f134,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f133,f109])).

fof(f109,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f104,f97])).

fof(f97,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f94,f89])).

fof(f94,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f72,f68])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f104,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f71,f89])).

fof(f133,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f132,f98])).

fof(f132,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f131,f121])).

fof(f121,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f120,f110])).

fof(f110,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f105,f97])).

fof(f105,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f70,f89])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f43,f43])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f120,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f115,f109])).

fof(f115,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(superposition,[],[f72,f95])).

fof(f95,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f92,f89])).

fof(f92,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f67,f68])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f131,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f119,f98])).

fof(f119,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(superposition,[],[f67,f95])).

fof(f89,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f73,f68])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ),
    inference(definition_unfolding,[],[f49,f63,f43,f64,f66])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f303,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f91,f180])).

fof(f180,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f153,f172])).

fof(f153,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f90,f39])).

fof(f90,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f47,f68])).

fof(f91,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f47,f68])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f407,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f406,f382])).

fof(f382,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f377,f324])).

fof(f324,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f321,f314])).

fof(f321,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f72,f312])).

fof(f377,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(superposition,[],[f71,f314])).

fof(f406,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f405,f325])).

fof(f405,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))) ),
    inference(forward_demodulation,[],[f404,f394])).

fof(f394,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f393,f383])).

fof(f383,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f378,f324])).

fof(f378,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f70,f314])).

fof(f393,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f388,f382])).

fof(f388,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(superposition,[],[f72,f322])).

fof(f322,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f319,f314])).

fof(f319,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f67,f312])).

fof(f404,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))) ),
    inference(forward_demodulation,[],[f392,f325])).

fof(f392,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(superposition,[],[f67,f322])).

fof(f314,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f73,f312])).

fof(f327,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f67,f323])).

fof(f1677,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f1110,f1670])).

fof(f1670,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f555,f1669])).

fof(f1669,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1658,f551])).

fof(f1658,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f1004,f39])).

fof(f1004,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k3_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f47,f974])).

fof(f974,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f973,f312])).

fof(f973,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f972,f177])).

fof(f177,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(backward_demodulation,[],[f121,f172])).

fof(f972,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f971,f172])).

fof(f971,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f953,f47])).

fof(f953,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f809,f39])).

fof(f809,plain,(
    ! [X1] : k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f161,f795])).

fof(f795,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(k5_xboole_0(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f165,f790])).

fof(f790,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f740,f789])).

fof(f789,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f511,f743])).

fof(f743,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(superposition,[],[f71,f155])).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(superposition,[],[f72,f90])).

fof(f511,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) ),
    inference(superposition,[],[f72,f157])).

fof(f157,plain,(
    ! [X4] : k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(superposition,[],[f67,f90])).

fof(f740,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f155,f70])).

fof(f165,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(k5_xboole_0(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f162,f90])).

fof(f162,plain,(
    ! [X2] : k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f70,f91])).

fof(f161,plain,(
    ! [X1] : k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f71,f91])).

fof(f555,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f385,f551])).

fof(f385,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f380,f324])).

fof(f380,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(superposition,[],[f67,f314])).

fof(f1110,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f1012,f1107])).

fof(f1107,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f1106,f1016])).

fof(f1016,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f1015,f1011])).

fof(f1011,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f1006,f73])).

fof(f1006,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f70,f974])).

fof(f1015,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f1009,f484])).

fof(f484,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f318,f39])).

fof(f318,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f47,f312])).

fof(f1009,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f72,f974])).

fof(f1106,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1097,f484])).

fof(f1097,plain,(
    k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f67,f1011])).

fof(f1012,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f1005,f1011])).

fof(f1005,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f67,f974])).

fof(f88,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:20:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (6096)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (6102)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (6099)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (6101)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (6112)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (6119)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (6100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (6111)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (6096)Refutation not found, incomplete strategy% (6096)------------------------------
% 0.21/0.52  % (6096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6096)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6096)Memory used [KB]: 1663
% 0.21/0.52  % (6096)Time elapsed: 0.106 s
% 0.21/0.52  % (6096)------------------------------
% 0.21/0.52  % (6096)------------------------------
% 0.21/0.52  % (6120)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (6118)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (6121)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (6104)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (6110)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (6111)Refutation not found, incomplete strategy% (6111)------------------------------
% 0.21/0.53  % (6111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6111)Memory used [KB]: 6140
% 0.21/0.53  % (6111)Time elapsed: 0.081 s
% 0.21/0.53  % (6111)------------------------------
% 0.21/0.53  % (6111)------------------------------
% 0.21/0.53  % (6109)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (6103)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (6097)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6098)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (6124)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (6125)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.55  % (6122)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.55  % (6117)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.55  % (6115)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (6116)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.55  % (6114)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.55  % (6107)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.55  % (6107)Refutation not found, incomplete strategy% (6107)------------------------------
% 1.34/0.55  % (6107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (6107)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (6107)Memory used [KB]: 10618
% 1.34/0.55  % (6107)Time elapsed: 0.141 s
% 1.34/0.55  % (6107)------------------------------
% 1.34/0.55  % (6107)------------------------------
% 1.34/0.56  % (6113)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.56  % (6108)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.56  % (6113)Refutation not found, incomplete strategy% (6113)------------------------------
% 1.34/0.56  % (6113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (6106)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.56  % (6106)Refutation not found, incomplete strategy% (6106)------------------------------
% 1.34/0.56  % (6106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (6106)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (6106)Memory used [KB]: 10618
% 1.34/0.56  % (6106)Time elapsed: 0.149 s
% 1.34/0.56  % (6106)------------------------------
% 1.34/0.56  % (6106)------------------------------
% 1.55/0.57  % (6113)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (6113)Memory used [KB]: 10618
% 1.55/0.57  % (6113)Time elapsed: 0.137 s
% 1.55/0.57  % (6113)------------------------------
% 1.55/0.57  % (6113)------------------------------
% 1.55/0.57  % (6105)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.55/0.57  % (6105)Refutation not found, incomplete strategy% (6105)------------------------------
% 1.55/0.57  % (6105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (6105)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (6105)Memory used [KB]: 10618
% 1.55/0.57  % (6105)Time elapsed: 0.145 s
% 1.55/0.57  % (6105)------------------------------
% 1.55/0.57  % (6105)------------------------------
% 1.97/0.66  % (6132)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.22/0.67  % (6131)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.22/0.69  % (6142)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.22/0.70  % (6140)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.22/0.71  % (6138)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.22/0.71  % (6141)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.22/0.71  % (6104)Refutation found. Thanks to Tanya!
% 2.22/0.71  % SZS status Theorem for theBenchmark
% 2.22/0.72  % SZS output start Proof for theBenchmark
% 2.22/0.72  fof(f1940,plain,(
% 2.22/0.72    $false),
% 2.22/0.72    inference(subsumption_resolution,[],[f1938,f34])).
% 2.22/0.72  fof(f34,plain,(
% 2.22/0.72    sK0 != sK1),
% 2.22/0.72    inference(cnf_transformation,[],[f27])).
% 2.22/0.72  fof(f27,plain,(
% 2.22/0.72    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.22/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).
% 2.22/0.72  fof(f26,plain,(
% 2.22/0.72    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.22/0.72    introduced(choice_axiom,[])).
% 2.22/0.72  fof(f24,plain,(
% 2.22/0.72    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.22/0.72    inference(ennf_transformation,[],[f21])).
% 2.22/0.72  fof(f21,negated_conjecture,(
% 2.22/0.72    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.22/0.72    inference(negated_conjecture,[],[f20])).
% 2.22/0.72  fof(f20,conjecture,(
% 2.22/0.72    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 2.22/0.72  fof(f1938,plain,(
% 2.22/0.72    sK0 = sK1),
% 2.22/0.72    inference(resolution,[],[f1926,f85])).
% 2.22/0.72  fof(f85,plain,(
% 2.22/0.72    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 2.22/0.72    inference(equality_resolution,[],[f84])).
% 2.22/0.72  fof(f84,plain,(
% 2.22/0.72    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 2.22/0.72    inference(equality_resolution,[],[f79])).
% 2.22/0.72  fof(f79,plain,(
% 2.22/0.72    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.22/0.72    inference(definition_unfolding,[],[f52,f64])).
% 2.22/0.72  fof(f64,plain,(
% 2.22/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.22/0.72    inference(definition_unfolding,[],[f46,f63])).
% 2.22/0.72  fof(f63,plain,(
% 2.22/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.22/0.72    inference(definition_unfolding,[],[f48,f62])).
% 2.22/0.72  fof(f62,plain,(
% 2.22/0.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.22/0.72    inference(definition_unfolding,[],[f58,f61])).
% 2.22/0.72  fof(f61,plain,(
% 2.22/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.22/0.72    inference(definition_unfolding,[],[f59,f60])).
% 2.22/0.72  fof(f60,plain,(
% 2.22/0.72    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f19])).
% 2.22/0.72  fof(f19,axiom,(
% 2.22/0.72    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.22/0.72  fof(f59,plain,(
% 2.22/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f18])).
% 2.22/0.72  fof(f18,axiom,(
% 2.22/0.72    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.22/0.72  fof(f58,plain,(
% 2.22/0.72    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f17])).
% 2.22/0.72  fof(f17,axiom,(
% 2.22/0.72    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.22/0.72  fof(f48,plain,(
% 2.22/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f16])).
% 2.22/0.72  fof(f16,axiom,(
% 2.22/0.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.22/0.72  fof(f46,plain,(
% 2.22/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f15])).
% 2.22/0.72  fof(f15,axiom,(
% 2.22/0.72    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.22/0.72  fof(f52,plain,(
% 2.22/0.72    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.22/0.72    inference(cnf_transformation,[],[f32])).
% 2.22/0.72  fof(f32,plain,(
% 2.22/0.72    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.22/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 2.22/0.72  fof(f31,plain,(
% 2.22/0.72    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 2.22/0.72    introduced(choice_axiom,[])).
% 2.22/0.72  fof(f30,plain,(
% 2.22/0.72    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.22/0.72    inference(rectify,[],[f29])).
% 2.22/0.72  fof(f29,plain,(
% 2.22/0.72    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.22/0.72    inference(flattening,[],[f28])).
% 2.22/0.72  fof(f28,plain,(
% 2.22/0.72    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.22/0.72    inference(nnf_transformation,[],[f25])).
% 2.22/0.72  fof(f25,plain,(
% 2.22/0.72    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.22/0.72    inference(ennf_transformation,[],[f11])).
% 2.22/0.72  fof(f11,axiom,(
% 2.22/0.72    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.22/0.72  fof(f1926,plain,(
% 2.22/0.72    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X0) )),
% 2.22/0.72    inference(duplicate_literal_removal,[],[f1920])).
% 2.22/0.72  fof(f1920,plain,(
% 2.22/0.72    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X0 | sK1 = X0 | sK1 = X0) )),
% 2.22/0.72    inference(superposition,[],[f88,f1685])).
% 2.22/0.72  fof(f1685,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 2.22/0.72    inference(forward_demodulation,[],[f1677,f562])).
% 2.22/0.72  fof(f562,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f327,f552])).
% 2.22/0.72  fof(f552,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f314,f551])).
% 2.22/0.72  fof(f551,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f407,f546])).
% 2.22/0.72  fof(f546,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(superposition,[],[f325,f39])).
% 2.22/0.72  fof(f39,plain,(
% 2.22/0.72    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.22/0.72    inference(cnf_transformation,[],[f23])).
% 2.22/0.72  fof(f23,plain,(
% 2.22/0.72    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.22/0.72    inference(rectify,[],[f3])).
% 2.22/0.72  fof(f3,axiom,(
% 2.22/0.72    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.22/0.72  fof(f325,plain,(
% 2.22/0.72    ( ! [X0] : (k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) )),
% 2.22/0.72    inference(superposition,[],[f47,f323])).
% 2.22/0.72  fof(f323,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f320,f314])).
% 2.22/0.72  fof(f320,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(superposition,[],[f71,f312])).
% 2.22/0.72  fof(f312,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f303,f173])).
% 2.22/0.72  fof(f173,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.22/0.72    inference(backward_demodulation,[],[f89,f172])).
% 2.22/0.72  fof(f172,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f134,f167])).
% 2.22/0.72  fof(f167,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(superposition,[],[f98,f39])).
% 2.22/0.72  fof(f98,plain,(
% 2.22/0.72    ( ! [X0] : (k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) )),
% 2.22/0.72    inference(superposition,[],[f47,f96])).
% 2.22/0.72  fof(f96,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f93,f89])).
% 2.22/0.72  fof(f93,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.22/0.72    inference(superposition,[],[f71,f68])).
% 2.22/0.72  fof(f68,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(definition_unfolding,[],[f33,f66,f66,f66])).
% 2.22/0.72  fof(f66,plain,(
% 2.22/0.72    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.22/0.72    inference(definition_unfolding,[],[f37,f65])).
% 2.22/0.72  fof(f65,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.22/0.72    inference(definition_unfolding,[],[f42,f64])).
% 2.22/0.72  fof(f42,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f14])).
% 2.22/0.72  fof(f14,axiom,(
% 2.22/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.22/0.72  fof(f37,plain,(
% 2.22/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f13])).
% 2.22/0.72  fof(f13,axiom,(
% 2.22/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.22/0.72  fof(f33,plain,(
% 2.22/0.72    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.22/0.72    inference(cnf_transformation,[],[f27])).
% 2.22/0.72  fof(f134,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f133,f109])).
% 2.22/0.72  fof(f109,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f104,f97])).
% 2.22/0.72  fof(f97,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.22/0.72    inference(forward_demodulation,[],[f94,f89])).
% 2.22/0.72  fof(f94,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.22/0.72    inference(superposition,[],[f72,f68])).
% 2.22/0.72  fof(f72,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 2.22/0.72    inference(definition_unfolding,[],[f44,f43,f43])).
% 2.22/0.72  fof(f43,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.22/0.72    inference(cnf_transformation,[],[f9])).
% 2.22/0.72  fof(f9,axiom,(
% 2.22/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.22/0.72  fof(f44,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.22/0.72    inference(cnf_transformation,[],[f8])).
% 2.22/0.72  fof(f8,axiom,(
% 2.22/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.22/0.72  fof(f104,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.22/0.72    inference(superposition,[],[f71,f89])).
% 2.22/0.72  fof(f133,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f132,f98])).
% 2.22/0.72  fof(f132,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f131,f121])).
% 2.22/0.72  fof(f121,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f120,f110])).
% 2.22/0.72  fof(f110,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.22/0.72    inference(forward_demodulation,[],[f105,f97])).
% 2.22/0.72  fof(f105,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.22/0.72    inference(superposition,[],[f70,f89])).
% 2.22/0.72  fof(f70,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X1,X0))) )),
% 2.22/0.72    inference(definition_unfolding,[],[f40,f43,f43])).
% 2.22/0.72  fof(f40,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f1])).
% 2.22/0.72  fof(f1,axiom,(
% 2.22/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.22/0.72  fof(f120,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.22/0.72    inference(forward_demodulation,[],[f115,f109])).
% 2.22/0.72  fof(f115,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.22/0.72    inference(superposition,[],[f72,f95])).
% 2.22/0.72  fof(f95,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f92,f89])).
% 2.22/0.72  fof(f92,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.22/0.72    inference(superposition,[],[f67,f68])).
% 2.22/0.72  fof(f67,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 2.22/0.72    inference(definition_unfolding,[],[f45,f43])).
% 2.22/0.72  fof(f45,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.22/0.72    inference(cnf_transformation,[],[f10])).
% 2.22/0.72  fof(f10,axiom,(
% 2.22/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.22/0.72  fof(f131,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f119,f98])).
% 2.22/0.72  fof(f119,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.22/0.72    inference(superposition,[],[f67,f95])).
% 2.22/0.72  fof(f89,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.22/0.72    inference(superposition,[],[f73,f68])).
% 2.22/0.72  fof(f73,plain,(
% 2.22/0.72    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))) )),
% 2.22/0.72    inference(definition_unfolding,[],[f49,f63,f43,f64,f66])).
% 2.22/0.72  fof(f49,plain,(
% 2.22/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.22/0.72    inference(cnf_transformation,[],[f12])).
% 2.22/0.72  fof(f12,axiom,(
% 2.22/0.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 2.22/0.72  fof(f303,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(superposition,[],[f91,f180])).
% 2.22/0.72  fof(f180,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f153,f172])).
% 2.22/0.72  fof(f153,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(superposition,[],[f90,f39])).
% 2.22/0.72  fof(f90,plain,(
% 2.22/0.72    ( ! [X0] : (k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) )),
% 2.22/0.72    inference(superposition,[],[f47,f68])).
% 2.22/0.72  fof(f91,plain,(
% 2.22/0.72    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )),
% 2.22/0.72    inference(superposition,[],[f47,f68])).
% 2.22/0.72  fof(f71,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0) )),
% 2.22/0.72    inference(definition_unfolding,[],[f41,f43])).
% 2.22/0.72  fof(f41,plain,(
% 2.22/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.22/0.72    inference(cnf_transformation,[],[f5])).
% 2.22/0.72  fof(f5,axiom,(
% 2.22/0.72    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.22/0.72  fof(f47,plain,(
% 2.22/0.72    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.22/0.72    inference(cnf_transformation,[],[f4])).
% 2.22/0.72  fof(f4,axiom,(
% 2.22/0.72    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.22/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.22/0.72  fof(f407,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f406,f382])).
% 2.22/0.72  fof(f382,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f377,f324])).
% 2.22/0.72  fof(f324,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f321,f314])).
% 2.22/0.72  fof(f321,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(superposition,[],[f72,f312])).
% 2.22/0.72  fof(f377,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.22/0.72    inference(superposition,[],[f71,f314])).
% 2.22/0.72  fof(f406,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f405,f325])).
% 2.22/0.72  fof(f405,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f404,f394])).
% 2.22/0.72  fof(f394,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f393,f383])).
% 2.22/0.72  fof(f383,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.22/0.72    inference(forward_demodulation,[],[f378,f324])).
% 2.22/0.72  fof(f378,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(superposition,[],[f70,f314])).
% 2.22/0.72  fof(f393,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.22/0.72    inference(forward_demodulation,[],[f388,f382])).
% 2.22/0.72  fof(f388,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.22/0.72    inference(superposition,[],[f72,f322])).
% 2.22/0.72  fof(f322,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f319,f314])).
% 2.22/0.72  fof(f319,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(superposition,[],[f67,f312])).
% 2.22/0.72  fof(f404,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f392,f325])).
% 2.22/0.72  fof(f392,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.22/0.72    inference(superposition,[],[f67,f322])).
% 2.22/0.72  fof(f314,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(superposition,[],[f73,f312])).
% 2.22/0.72  fof(f327,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(superposition,[],[f67,f323])).
% 2.22/0.72  fof(f1677,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f1110,f1670])).
% 2.22/0.72  fof(f1670,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f555,f1669])).
% 2.22/0.72  fof(f1669,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f1658,f551])).
% 2.22/0.72  fof(f1658,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(superposition,[],[f1004,f39])).
% 2.22/0.72  fof(f1004,plain,(
% 2.22/0.72    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k3_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 2.22/0.72    inference(superposition,[],[f47,f974])).
% 2.22/0.72  fof(f974,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f973,f312])).
% 2.22/0.72  fof(f973,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f972,f177])).
% 2.22/0.72  fof(f177,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(backward_demodulation,[],[f121,f172])).
% 2.22/0.72  fof(f972,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f971,f172])).
% 2.22/0.72  fof(f971,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f953,f47])).
% 2.22/0.72  fof(f953,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.22/0.72    inference(superposition,[],[f809,f39])).
% 2.22/0.72  fof(f809,plain,(
% 2.22/0.72    ( ! [X1] : (k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) )),
% 2.22/0.72    inference(backward_demodulation,[],[f161,f795])).
% 2.22/0.72  fof(f795,plain,(
% 2.22/0.72    ( ! [X2] : (k5_xboole_0(k3_xboole_0(k5_xboole_0(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) )),
% 2.22/0.72    inference(backward_demodulation,[],[f165,f790])).
% 2.22/0.72  fof(f790,plain,(
% 2.22/0.72    ( ! [X1] : (k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) )),
% 2.22/0.72    inference(backward_demodulation,[],[f740,f789])).
% 2.22/0.72  fof(f789,plain,(
% 2.22/0.72    ( ! [X0] : (k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) )),
% 2.22/0.72    inference(backward_demodulation,[],[f511,f743])).
% 2.22/0.72  fof(f743,plain,(
% 2.22/0.72    ( ! [X1] : (k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) )),
% 2.22/0.72    inference(superposition,[],[f71,f155])).
% 2.22/0.72  fof(f155,plain,(
% 2.22/0.72    ( ! [X0] : (k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) )),
% 2.22/0.72    inference(superposition,[],[f72,f90])).
% 2.22/0.72  fof(f511,plain,(
% 2.22/0.72    ( ! [X0] : (k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))))) )),
% 2.22/0.72    inference(superposition,[],[f72,f157])).
% 2.22/0.72  fof(f157,plain,(
% 2.22/0.72    ( ! [X4] : (k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) )),
% 2.22/0.72    inference(superposition,[],[f67,f90])).
% 2.22/0.72  fof(f740,plain,(
% 2.22/0.72    ( ! [X1] : (k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) )),
% 2.22/0.72    inference(superposition,[],[f155,f70])).
% 2.22/0.72  fof(f165,plain,(
% 2.22/0.72    ( ! [X2] : (k5_xboole_0(k3_xboole_0(k5_xboole_0(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) )),
% 2.22/0.72    inference(forward_demodulation,[],[f162,f90])).
% 2.22/0.72  fof(f162,plain,(
% 2.22/0.72    ( ! [X2] : (k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) )),
% 2.22/0.72    inference(superposition,[],[f70,f91])).
% 2.22/0.72  fof(f161,plain,(
% 2.22/0.72    ( ! [X1] : (k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) )),
% 2.22/0.72    inference(superposition,[],[f71,f91])).
% 2.22/0.72  fof(f555,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f385,f551])).
% 2.22/0.72  fof(f385,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f380,f324])).
% 2.22/0.72  fof(f380,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.22/0.72    inference(superposition,[],[f67,f314])).
% 2.22/0.72  fof(f1110,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f1012,f1107])).
% 2.22/0.72  fof(f1107,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f1106,f1016])).
% 2.22/0.72  fof(f1016,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f1015,f1011])).
% 2.22/0.72  fof(f1011,plain,(
% 2.22/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(forward_demodulation,[],[f1006,f73])).
% 2.22/0.72  fof(f1006,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(superposition,[],[f70,f974])).
% 2.22/0.72  fof(f1015,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.22/0.72    inference(forward_demodulation,[],[f1009,f484])).
% 2.22/0.72  fof(f484,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.22/0.72    inference(superposition,[],[f318,f39])).
% 2.22/0.72  fof(f318,plain,(
% 2.22/0.72    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k3_xboole_0(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) )),
% 2.22/0.72    inference(superposition,[],[f47,f312])).
% 2.22/0.72  fof(f1009,plain,(
% 2.22/0.72    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.72    inference(superposition,[],[f72,f974])).
% 2.22/0.72  fof(f1106,plain,(
% 2.22/0.72    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.22/0.72    inference(forward_demodulation,[],[f1097,f484])).
% 2.22/0.72  fof(f1097,plain,(
% 2.22/0.72    k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.22/0.72    inference(superposition,[],[f67,f1011])).
% 2.22/0.72  fof(f1012,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.22/0.72    inference(backward_demodulation,[],[f1005,f1011])).
% 2.22/0.72  fof(f1005,plain,(
% 2.22/0.72    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.72    inference(superposition,[],[f67,f974])).
% 2.22/0.72  fof(f88,plain,(
% 2.22/0.72    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.22/0.72    inference(equality_resolution,[],[f81])).
% 2.22/0.72  fof(f81,plain,(
% 2.22/0.72    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.22/0.72    inference(definition_unfolding,[],[f50,f64])).
% 2.22/0.72  fof(f50,plain,(
% 2.22/0.72    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.22/0.72    inference(cnf_transformation,[],[f32])).
% 2.22/0.72  % SZS output end Proof for theBenchmark
% 2.22/0.72  % (6104)------------------------------
% 2.22/0.72  % (6104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.72  % (6104)Termination reason: Refutation
% 2.22/0.72  
% 2.22/0.72  % (6104)Memory used [KB]: 13048
% 2.22/0.72  % (6104)Time elapsed: 0.301 s
% 2.22/0.72  % (6104)------------------------------
% 2.22/0.72  % (6104)------------------------------
% 2.22/0.73  % (6095)Success in time 0.359 s
%------------------------------------------------------------------------------
