%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:21 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 149 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   18
%              Number of atoms          :  291 ( 893 expanded)
%              Number of equality atoms :  155 ( 491 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(subsumption_resolution,[],[f401,f109])).

fof(f109,plain,(
    r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f101,plain,(
    r2_hidden(sK3,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,(
    k3_xboole_0(sK1,sK2) = k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f32,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f401,plain,(
    ~ r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f400,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK3,k3_xboole_0(sK0,X0))
      | ~ r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f33,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f400,plain,(
    ~ r2_hidden(sK3,k3_xboole_0(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f386])).

fof(f386,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(sK0,sK2))
    | sK3 != sK3
    | k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f88,f357])).

fof(f357,plain,(
    sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f356])).

fof(f356,plain,
    ( sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2))
    | k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,
    ( sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2))
    | sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2))
    | k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f312,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,sK3,sK3,X0),X0)
      | sK3 = sK4(sK3,sK3,sK3,X0)
      | k3_xboole_0(sK0,sK2) != X0 ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK2) != X0
      | sK3 = sK4(sK3,sK3,sK3,X0)
      | sK3 = sK4(sK3,sK3,sK3,X0)
      | sK3 = sK4(sK3,sK3,sK3,X0)
      | r2_hidden(sK4(sK3,sK3,sK3,X0),X0) ) ),
    inference(superposition,[],[f54,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK4(X0,X1,X2,X3) = X2
      | sK4(X0,X1,X2,X3) = X1
      | sK4(X0,X1,X2,X3) = X0
      | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    k3_xboole_0(sK0,sK2) != k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f34,f53])).

fof(f34,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f312,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,k3_xboole_0(sK0,sK2))
      | sK3 = X14 ) ),
    inference(superposition,[],[f147,f75])).

fof(f75,plain,(
    ! [X3] : k3_xboole_0(sK0,k3_xboole_0(sK1,X3)) = k3_xboole_0(sK0,X3) ),
    inference(superposition,[],[f50,f66])).

fof(f66,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f31,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f147,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,k3_xboole_0(sK1,sK2)))
      | sK3 = X3 ) ),
    inference(resolution,[],[f105,f64])).

fof(f105,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k3_xboole_0(sK1,sK2))
      | sK3 = X4 ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k3_xboole_0(sK1,sK2))
      | sK3 = X4
      | sK3 = X4
      | sK3 = X4 ) ),
    inference(superposition,[],[f62,f55])).

fof(f62,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK3,sK3,sK3,X1),X1)
      | sK3 != sK4(sK3,sK3,sK3,X1)
      | k3_xboole_0(sK0,sK2) != X1 ) ),
    inference(superposition,[],[f54,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK4(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (7682)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (7676)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (7687)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (7668)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (7669)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (7674)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (7673)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (7679)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (7681)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (7696)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.53  % (7694)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.53  % (7671)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (7693)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.54  % (7699)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  % (7685)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.54  % (7687)Refutation not found, incomplete strategy% (7687)------------------------------
% 1.33/0.54  % (7687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (7687)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (7687)Memory used [KB]: 10746
% 1.33/0.54  % (7687)Time elapsed: 0.132 s
% 1.33/0.54  % (7687)------------------------------
% 1.33/0.54  % (7687)------------------------------
% 1.33/0.54  % (7684)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.54  % (7670)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (7692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.54  % (7695)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.55  % (7697)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.55  % (7677)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.55  % (7700)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (7688)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (7686)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (7691)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.55  % (7690)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (7678)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.56  % (7680)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.56  % (7689)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.56  % (7683)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.56  % (7668)Refutation found. Thanks to Tanya!
% 1.40/0.56  % SZS status Theorem for theBenchmark
% 1.40/0.56  % SZS output start Proof for theBenchmark
% 1.40/0.56  fof(f410,plain,(
% 1.40/0.56    $false),
% 1.40/0.56    inference(subsumption_resolution,[],[f401,f109])).
% 1.40/0.56  fof(f109,plain,(
% 1.40/0.56    r2_hidden(sK3,sK2)),
% 1.40/0.56    inference(resolution,[],[f101,f64])).
% 1.40/0.56  fof(f64,plain,(
% 1.40/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.40/0.56    inference(equality_resolution,[],[f44])).
% 1.40/0.56  fof(f44,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.40/0.56    inference(cnf_transformation,[],[f30])).
% 1.40/0.56  fof(f30,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 1.40/0.56  fof(f29,plain,(
% 1.40/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(rectify,[],[f27])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(flattening,[],[f26])).
% 1.40/0.56  fof(f26,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(nnf_transformation,[],[f1])).
% 1.40/0.56  fof(f1,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.40/0.56  fof(f101,plain,(
% 1.40/0.56    r2_hidden(sK3,k3_xboole_0(sK1,sK2))),
% 1.40/0.56    inference(superposition,[],[f57,f55])).
% 1.40/0.56  fof(f55,plain,(
% 1.40/0.56    k3_xboole_0(sK1,sK2) = k1_enumset1(sK3,sK3,sK3)),
% 1.40/0.56    inference(definition_unfolding,[],[f32,f53])).
% 1.40/0.56  fof(f53,plain,(
% 1.40/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.40/0.56    inference(definition_unfolding,[],[f49,f52])).
% 1.40/0.56  fof(f52,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f7])).
% 1.40/0.56  fof(f7,axiom,(
% 1.40/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.56  fof(f49,plain,(
% 1.40/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f6])).
% 1.40/0.56  fof(f6,axiom,(
% 1.40/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.56  fof(f32,plain,(
% 1.40/0.56    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.40/0.56    inference(cnf_transformation,[],[f20])).
% 1.40/0.56  fof(f20,plain,(
% 1.40/0.56    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f19])).
% 1.40/0.56  fof(f19,plain,(
% 1.40/0.56    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f16,plain,(
% 1.40/0.56    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.40/0.56    inference(flattening,[],[f15])).
% 1.40/0.56  fof(f15,plain,(
% 1.40/0.56    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.40/0.56    inference(ennf_transformation,[],[f14])).
% 1.40/0.56  fof(f14,negated_conjecture,(
% 1.40/0.56    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.40/0.56    inference(negated_conjecture,[],[f13])).
% 1.40/0.56  fof(f13,conjecture,(
% 1.40/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.40/0.56  fof(f57,plain,(
% 1.40/0.56    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.40/0.56    inference(equality_resolution,[],[f56])).
% 1.40/0.56  fof(f56,plain,(
% 1.40/0.56    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.40/0.56    inference(equality_resolution,[],[f38])).
% 1.40/0.56  fof(f38,plain,(
% 1.40/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.40/0.56    inference(cnf_transformation,[],[f25])).
% 1.40/0.56  fof(f25,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 1.40/0.56  fof(f24,plain,(
% 1.40/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f23,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.40/0.56    inference(rectify,[],[f22])).
% 1.40/0.56  fof(f22,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.40/0.56    inference(flattening,[],[f21])).
% 1.40/0.56  fof(f21,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.40/0.56    inference(nnf_transformation,[],[f17])).
% 1.40/0.56  fof(f17,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.40/0.56    inference(ennf_transformation,[],[f5])).
% 1.40/0.56  fof(f5,axiom,(
% 1.40/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.40/0.56  fof(f401,plain,(
% 1.40/0.56    ~r2_hidden(sK3,sK2)),
% 1.40/0.56    inference(resolution,[],[f400,f67])).
% 1.40/0.56  fof(f67,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(sK3,k3_xboole_0(sK0,X0)) | ~r2_hidden(sK3,X0)) )),
% 1.40/0.56    inference(resolution,[],[f33,f63])).
% 1.40/0.56  fof(f63,plain,(
% 1.40/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.40/0.56    inference(equality_resolution,[],[f45])).
% 1.40/0.56  fof(f45,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.40/0.56    inference(cnf_transformation,[],[f30])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    r2_hidden(sK3,sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f20])).
% 1.40/0.56  fof(f400,plain,(
% 1.40/0.56    ~r2_hidden(sK3,k3_xboole_0(sK0,sK2))),
% 1.40/0.56    inference(trivial_inequality_removal,[],[f386])).
% 1.40/0.56  fof(f386,plain,(
% 1.40/0.56    ~r2_hidden(sK3,k3_xboole_0(sK0,sK2)) | sK3 != sK3 | k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)),
% 1.40/0.56    inference(superposition,[],[f88,f357])).
% 1.40/0.56  fof(f357,plain,(
% 1.40/0.56    sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2))),
% 1.40/0.56    inference(trivial_inequality_removal,[],[f356])).
% 1.40/0.56  fof(f356,plain,(
% 1.40/0.56    sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2)) | k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f347])).
% 1.40/0.56  fof(f347,plain,(
% 1.40/0.56    sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2)) | sK3 = sK4(sK3,sK3,sK3,k3_xboole_0(sK0,sK2)) | k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)),
% 1.40/0.56    inference(resolution,[],[f312,f91])).
% 1.40/0.56  fof(f91,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(sK4(sK3,sK3,sK3,X0),X0) | sK3 = sK4(sK3,sK3,sK3,X0) | k3_xboole_0(sK0,sK2) != X0) )),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f87])).
% 1.40/0.56  fof(f87,plain,(
% 1.40/0.56    ( ! [X0] : (k3_xboole_0(sK0,sK2) != X0 | sK3 = sK4(sK3,sK3,sK3,X0) | sK3 = sK4(sK3,sK3,sK3,X0) | sK3 = sK4(sK3,sK3,sK3,X0) | r2_hidden(sK4(sK3,sK3,sK3,X0),X0)) )),
% 1.40/0.56    inference(superposition,[],[f54,f39])).
% 1.40/0.56  fof(f39,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f25])).
% 1.40/0.56  fof(f54,plain,(
% 1.40/0.56    k3_xboole_0(sK0,sK2) != k1_enumset1(sK3,sK3,sK3)),
% 1.40/0.56    inference(definition_unfolding,[],[f34,f53])).
% 1.40/0.56  fof(f34,plain,(
% 1.40/0.56    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.40/0.56    inference(cnf_transformation,[],[f20])).
% 1.40/0.56  fof(f312,plain,(
% 1.40/0.56    ( ! [X14] : (~r2_hidden(X14,k3_xboole_0(sK0,sK2)) | sK3 = X14) )),
% 1.40/0.56    inference(superposition,[],[f147,f75])).
% 1.40/0.56  fof(f75,plain,(
% 1.40/0.56    ( ! [X3] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X3)) = k3_xboole_0(sK0,X3)) )),
% 1.40/0.56    inference(superposition,[],[f50,f66])).
% 1.40/0.56  fof(f66,plain,(
% 1.40/0.56    sK0 = k3_xboole_0(sK0,sK1)),
% 1.40/0.56    inference(resolution,[],[f31,f51])).
% 1.40/0.56  fof(f51,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f18])).
% 1.40/0.56  fof(f18,plain,(
% 1.40/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.40/0.56    inference(ennf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.40/0.56  fof(f31,plain,(
% 1.40/0.56    r1_tarski(sK0,sK1)),
% 1.40/0.56    inference(cnf_transformation,[],[f20])).
% 1.40/0.56  fof(f50,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f2])).
% 1.40/0.56  fof(f2,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.40/0.56  fof(f147,plain,(
% 1.40/0.56    ( ! [X4,X3] : (~r2_hidden(X3,k3_xboole_0(X4,k3_xboole_0(sK1,sK2))) | sK3 = X3) )),
% 1.40/0.56    inference(resolution,[],[f105,f64])).
% 1.40/0.56  fof(f105,plain,(
% 1.40/0.56    ( ! [X4] : (~r2_hidden(X4,k3_xboole_0(sK1,sK2)) | sK3 = X4) )),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f104])).
% 1.40/0.56  fof(f104,plain,(
% 1.40/0.56    ( ! [X4] : (~r2_hidden(X4,k3_xboole_0(sK1,sK2)) | sK3 = X4 | sK3 = X4 | sK3 = X4) )),
% 1.40/0.56    inference(superposition,[],[f62,f55])).
% 1.40/0.56  fof(f62,plain,(
% 1.40/0.56    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 1.40/0.56    inference(equality_resolution,[],[f35])).
% 1.40/0.56  fof(f35,plain,(
% 1.40/0.56    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.40/0.56    inference(cnf_transformation,[],[f25])).
% 1.40/0.56  fof(f88,plain,(
% 1.40/0.56    ( ! [X1] : (~r2_hidden(sK4(sK3,sK3,sK3,X1),X1) | sK3 != sK4(sK3,sK3,sK3,X1) | k3_xboole_0(sK0,sK2) != X1) )),
% 1.40/0.56    inference(superposition,[],[f54,f40])).
% 1.40/0.56  fof(f40,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK4(X0,X1,X2,X3) != X0 | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f25])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (7668)------------------------------
% 1.40/0.56  % (7668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (7668)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (7668)Memory used [KB]: 1918
% 1.40/0.56  % (7668)Time elapsed: 0.154 s
% 1.40/0.56  % (7668)------------------------------
% 1.40/0.56  % (7668)------------------------------
% 1.40/0.56  % (7665)Success in time 0.196 s
%------------------------------------------------------------------------------
